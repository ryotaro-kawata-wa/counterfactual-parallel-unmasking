"""Passive forest KL with exact small factors and explicit Monte Carlo error.

Please leave the generation oracle exact. Conditioning on the existing history
leaves a forest. Marginalizing each connected unselected component produces a
factor on its selected boundary. These factors form an acyclic hypergraph with
singleton separators, so KL(product marginals || batch marginal) is the sum of
the corresponding boundary-factor reverse KLs. Degree-two paths are integrated
exactly before evaluating each factor.

Factors with at most four boundary variables are enumerated; larger factors use
independent draws from their product marginals. The integrand expm1(log(p/q)) -
log(p/q) is nonnegative and has expectation KL(q||p). Measurement standard errors
are conditional on the saved generation histories, separately from seed spread.
"""
import ctypes
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import numpy as np

from minimal_oracle import ChainEvaluator, MinimalRecorder

_BACKEND = None
STAT_NAMES = ('exact_factors', 'mc_factors', 'max_boundary', 'mc_draws',
              'hidden_components', 'max_compressed_nodes')


def load_backend():
    global _BACKEND
    if _BACKEND is None:
        source = Path(__file__).with_name('forest_batch_kl.c')
        key = hashlib.sha256(source.read_bytes()+sys.platform.encode()).hexdigest()[:20]
        directory = Path(tempfile.gettempdir())/'forest-toy-general-kl'
        directory.mkdir(exist_ok=True)
        binary = directory/(key+('.dylib' if sys.platform == 'darwin' else '.so'))
        if not binary.exists():
            temporary = binary.with_name(binary.name+f'.{os.getpid()}.tmp')
            subprocess.run(['cc', '-O3', '-std=c99', '-dynamiclib' if sys.platform == 'darwin' else '-shared',
                            '-fPIC', str(source), '-o', str(temporary), '-lm'], check=True, capture_output=True)
            os.replace(temporary, binary)
        library = ctypes.CDLL(str(binary))
        real = np.ctypeslib.ndpointer(dtype=np.float64, flags='C_CONTIGUOUS')
        integer = np.ctypeslib.ndpointer(dtype=np.int64, flags='C_CONTIGUOUS')
        library.forest_batch_kl.argtypes = [ctypes.c_int64, real, real, integer, integer,
            integer, integer, integer, integer, ctypes.c_int64, ctypes.c_int64,
            ctypes.c_uint64, real, real, real, real, integer]
        library.forest_batch_kl.restype = ctypes.c_int
        _BACKEND = library
    return _BACKEND


class ForestEvaluator:
    """Please keep this evaluator and its RNG entirely outside the controller."""
    def __init__(self, oracle, *, seed=0, samples=128, exact_arity=4):
        if samples < 2 or not 2 <= exact_arity <= 10:
            raise ValueError('Please use at least two MC draws and exact arity between 2 and 10.')
        self.oracle, self.n = oracle, oracle.n
        self.seed, self.samples, self.exact_arity = int(seed), int(samples), int(exact_arity)
        self.rng = np.random.default_rng(seed)
        self.events = []

    def evaluate(self, history, batch):
        history = np.ascontiguousarray(history, dtype=np.int64)
        batch = np.asarray(batch, dtype=np.int64)
        if (history.shape != (self.n,) or np.any(history < -1) or np.any(history >= self.oracle.vocab)
                or batch.ndim != 1 or np.any(batch < 0) or np.any(batch >= self.n)
                or len(np.unique(batch)) != len(batch) or np.any(history[batch] >= 0)):
            raise ValueError('Please evaluate distinct uncommitted positions in a valid history.')
        selected = np.zeros(self.n, dtype=np.int64)
        selected[batch] = 1
        rows, pairs = np.empty((self.n, 3)), np.zeros(self.n)
        total, variance, stats = np.zeros(1), np.zeros(1), np.zeros(6, dtype=np.int64)
        oracle = self.oracle
        random_seed = int(self.rng.integers(0, np.iinfo(np.uint64).max, dtype=np.uint64))
        code = load_backend().forest_batch_kl(self.n, oracle.prior, oracle.parent_strength,
            oracle.parent, oracle.order, oracle.offsets, oracle.neighbors, history, selected,
            self.exact_arity, self.samples, random_seed, rows, pairs, total, variance, stats)
        if code or not np.isfinite(rows).all():
            raise ArithmeticError(f'Forest KL evaluation failed with code {code}.')
        self.events.append({'kl': float(total[0]), 'variance': float(variance[0]),
                            **dict(zip(STAT_NAMES, map(int, stats)))})
        return float(total[0]), rows, pairs


def initial_edges(oracle):
    """All-selected forests have only pair factors, so this profile is exact."""
    if oracle.max_degree <= 2:
        from profile_minimal import initial_edges as chain_initial_edges
        return chain_initial_edges(oracle)
    evaluator = ForestEvaluator(oracle)
    total, rows, pairs = evaluator.evaluate(np.full(oracle.n, -1), np.arange(oracle.n))
    children = np.asarray([v if oracle.parent[v] == u else u for u, v in oracle.edges])
    assert evaluator.events[0]['mc_factors'] == 0
    weights = pairs[children]
    np.testing.assert_allclose(weights.sum(), total, atol=1e-12, rtol=1e-12)
    return rows, weights, total


class ForestRecorder(MinimalRecorder):
    def __init__(self, n, *, seed=0, samples=128, exact_arity=4):
        super().__init__(n)
        self.evaluation_seed, self.samples, self.exact_arity = int(seed), int(samples), int(exact_arity)

    def finish(self, oracle, snapshot=None):
        if oracle.max_degree <= 2:
            result = super().finish(oracle, snapshot)
            return {**result, 'kl_evaluation': 'exact_chain', 'kl_evaluation_exact': True,
                    'kl_mc_se_per_token': 0., 'kl_mc_variance': 0.,
                    'kl_mc_factors': 0, 'kl_mc_draws': 0, 'kl_max_boundary': 2,
                    'evaluation_seed': self.evaluation_seed}
        evaluator = ForestEvaluator(oracle, seed=self.evaluation_seed,
                                    samples=self.samples, exact_arity=self.exact_arity)
        result = super().finish(oracle, snapshot, evaluator=evaluator)
        events = iter(evaluator.events)
        batch_variance, batch_mc_factors = [], []
        for batch in self.batches:
            event = next(events) if len(batch) > 1 else {'variance': 0., 'mc_factors': 0}
            batch_variance.append(event['variance'])
            batch_mc_factors.append(event['mc_factors'])
        variance = float(sum(batch_variance))
        count = sum(batch_mc_factors)
        if snapshot is not None:
            with np.load(snapshot) as saved:
                arrays = {k: saved[k] for k in saved.files}
            arrays.update(batch_mc_variance=np.asarray(batch_variance),
                          batch_mc_factors=np.asarray(batch_mc_factors, dtype=np.int64))
            np.savez_compressed(snapshot, **arrays)
        return {**result, 'kl_evaluation': 'exact_forest' if count == 0 else 'forest_exact_plus_mc',
                'kl_evaluation_exact': count == 0, 'kl_mc_se_per_token': np.sqrt(variance)/oracle.n,
                'kl_mc_variance': variance, 'kl_mc_factors': count,
                'kl_mc_draws': sum(e['mc_draws'] for e in evaluator.events),
                'kl_max_boundary': max((e['max_boundary'] for e in evaluator.events), default=0),
                'evaluation_seed': self.evaluation_seed, 'evaluation_samples_per_factor': self.samples,
                'evaluation_exact_arity': self.exact_arity}
