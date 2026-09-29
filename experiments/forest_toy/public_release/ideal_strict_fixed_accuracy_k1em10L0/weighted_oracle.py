"""Separate exact weighted-forest oracle; the legacy sources remain unchanged."""

import ctypes
import hashlib
from math import expm1, fsum
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import numpy as np

from confidence import confidence_scores, top_confidence
from robustness_study import build_target, seeds_for
from toy import feature
from tradeoff_core import DensityRecorder, balanced_batches
from tree_oracle import TreeOracle, tree_schedule_audit

LAWS = ('original_uniform', 'loguniform10', 'mean_uniform')
_BACKEND = None


def load_weighted_backend():
    global _BACKEND
    if _BACKEND is None:
        source = Path(__file__).with_name('weighted_tree_bp.c')
        key = hashlib.sha256(source.read_bytes()+sys.platform.encode()).hexdigest()[:20]
        directory = Path(tempfile.gettempdir())/'forest-toy-weighted-bp'
        directory.mkdir(exist_ok=True)
        binary = directory/(key+('.dylib' if sys.platform == 'darwin' else '.so'))
        if not binary.exists():
            temporary = binary.with_name(binary.name+f'.{os.getpid()}.tmp')
            subprocess.run(['cc', '-O3', '-std=c99',
                            '-dynamiclib' if sys.platform == 'darwin' else '-shared',
                            '-fPIC', str(source), '-o', str(temporary)],
                           check=True, capture_output=True, text=True)
            os.replace(temporary, binary)
        function = ctypes.CDLL(str(binary)).weighted_forest_rows
        integer = np.ctypeslib.ndpointer(dtype=np.int64, flags='C_CONTIGUOUS')
        real = np.ctypeslib.ndpointer(dtype=np.float64, flags='C_CONTIGUOUS')
        function.argtypes = [ctypes.c_int64, ctypes.c_int64, real, integer, integer,
                             integer, integer, integer, ctypes.c_int64, integer, real]
        function.restype = ctypes.c_int
        _BACKEND = function
    return _BACKEND


class WeightedTreeOracle(TreeOracle):
    """Keep theta as the public reference calibration, separately from true weights."""

    def __init__(self, n, edges, strengths, theta_reference, vocab=2048):
        super().__init__(n, edges, theta_reference, vocab=vocab)
        strengths = np.ascontiguousarray(strengths, dtype=np.float64)
        if (strengths.shape != (len(self.edges),) or not np.all(np.isfinite(strengths))
                or np.any(strengths <= 0) or np.any(strengths > theta_reference)):
            raise ValueError('Please use one positive strength per edge, below the reference cap.')
        self.edge_strengths = strengths.copy()
        self.edge_strengths.flags.writeable = False
        self.parent_strength = np.zeros(n, dtype=np.float64)
        incident = np.zeros(n, dtype=np.float64)
        for (u, v), strength in zip(self.edges, self.edge_strengths):
            child = v if self.parent[v] == u else u
            self.parent_strength[child] = strength
            incident[u] += strength
            incident[v] += strength
        self.max_incident_strength = float(incident.max())
        if self.max_incident_strength > .5+1e-12:
            raise ValueError('Please retain the incident-strength sufficient bound of one half.')

    def rows_many(self, states, readouts):
        states = np.ascontiguousarray(states, dtype=np.int64)
        readouts = np.ascontiguousarray(readouts, dtype=np.int64)
        if (states.ndim != 2 or states.shape[1] != self.n or readouts.ndim != 1
                or np.any(states < -1) or np.any(states >= self.vocab)
                or np.any(readouts < 0) or np.any(readouts >= self.n)):
            raise ValueError('Please submit valid states and readout indices.')
        if np.any(states[:, readouts] != -1):
            raise ValueError('Please mask every requested readout in every state.')
        result = np.empty((len(states), len(readouts), 3), dtype=np.float64)
        status = load_weighted_backend()(self.n, len(states), self.parent_strength,
                                         self.parent, self.order, self.offsets, self.neighbors,
                                         states, len(readouts), readouts, result)
        if status or not np.all(np.isfinite(result)):
            raise ArithmeticError('Weighted forest conditional evaluation failed.')
        return result


def weight_seed(target, n, repeat):
    payload = f'weighted-forest-v1|{target}|{n}|{repeat}'.encode()
    return int.from_bytes(hashlib.sha256(payload).digest()[:8], 'little')


def make_weighted_target(target, n, repeat, law, kind='proposal', budget=0):
    if law not in LAWS:
        raise ValueError('Please choose one of the three frozen target laws.')
    seeds = seeds_for(target, n, repeat, kind, budget)
    base = build_target(target, n, seeds[0])
    if hasattr(base, 'edges'):
        edges = base.edges
    else:
        leaf = np.flatnonzero(base.leaf)
        edges = np.column_stack((leaf, base.root_of[leaf]))
    # Please associate random weights with canonical public edge identities.
    edges = np.asarray(sorted(tuple(sorted(map(int, edge))) for edge in edges), dtype=np.int64)
    rng = np.random.default_rng(weight_seed(target, n, repeat))
    heterogeneous = base.theta*np.exp(rng.uniform(np.log(.1), 0, len(edges)))
    strengths = (heterogeneous if law == 'loguniform10' else
                 np.full(len(edges), heterogeneous.mean() if law == 'mean_uniform' else base.theta))
    oracle = WeightedTreeOracle(n, edges, strengths, base.theta, base.vocab)
    oracle.target_law = law
    oracle.weight_seed = weight_seed(target, n, repeat)
    return oracle, seeds


def weight_metadata(oracle):
    weights = oracle.edge_strengths
    return {'weight_seed': oracle.weight_seed, 'max_degree': oracle.max_degree,
            'edge_count': len(weights), 'component_count': int((oracle.parent < 0).sum()),
            'edges_sha256': hashlib.sha256(oracle.edges.astype('<i8').tobytes()).hexdigest(),
            'weights_sha256': hashlib.sha256(weights.astype('<f8').tobytes()).hexdigest(),
            'weight_min': float(weights.min()), 'weight_max': float(weights.max()),
            'weight_mean': float(weights.mean()), 'weight_rms': float(np.sqrt(np.mean(weights**2))),
            'max_incident_strength': oracle.max_incident_strength,
            'true_signal_lower_bound': float(weights.min()/10),
            'true_response_upper_bound': float(10*weights.max())}


class WeightedDensityRecorder(DensityRecorder):
    def finish(self, oracle, values):
        if not np.all(self._seen):
            raise ValueError('Please complete every token before computing its joint density.')
        phi = feature(np.asarray(values))
        terms = np.log1p(oracle.edge_strengths*phi[oracle.edges[:, 0]]*phi[oracle.edges[:, 1]])
        log_p, log_q = fsum(map(float, terms)), fsum(self._terms)
        ratio = log_q-log_p
        score = -expm1(-ratio) if ratio > 0 else 0.0
        return {'log_q_over_product': log_q, 'log_p_over_product': log_p,
                'log_q_over_p': ratio, 'tv_score': score,
                'tv_score_above_numerical_floor': score > 1e-10}


def weighted_baseline_sample(oracle, count, order_seed, commit_seed, policy, observer=None):
    """Reuse the established position policy; only the oracle and density are weighted."""
    if not 1 <= count <= oracle.n or policy not in ('random', 'confidence'):
        raise ValueError('Please use random/confidence and a batch count between one and N.')
    history = np.full(oracle.n, -1, dtype=np.int64)
    recorder, rng = WeightedDensityRecorder(oracle.n), np.random.default_rng(commit_seed)
    if policy == 'random':
        scheduled = balanced_batches(oracle.n, count, np.random.default_rng(order_seed))
    else:
        order = np.random.default_rng(order_seed).permutation(oracle.n)
        ranks = np.empty(oracle.n, dtype=np.int64)
        ranks[order] = np.arange(oracle.n)
    small, extra = divmod(oracle.n, count)
    batches = []
    for step in range(count):
        if policy == 'random':
            batch = scheduled[step]
            readouts = batch
            rows = used = oracle.submit(history, batch, 'commit')
        else:
            readouts = np.flatnonzero(history < 0)
            rows = oracle.submit(history, readouts, 'commit')
            selected = top_confidence(confidence_scores(rows, oracle.vocab), ranks[readouts],
                                      small+(step < extra))
            selected = selected[np.argsort(readouts[selected])]
            batch, used = readouts[selected], rows[selected]
        values = (rng.random(len(batch))[:, None] > used[:, :2].cumsum(axis=-1)).sum(axis=-1)
        tail = values == 2
        values[tail] = rng.integers(2, oracle.vocab, size=int(tail.sum()))
        if observer is not None:
            observer(history, readouts, rows, batch, values)
        history[batch] = values
        recorder(batch, used, values)
        batches.append(batch.tolist())
    return {'sample': history, 'batches': batches, **recorder.finish(oracle, history),
            **tree_schedule_audit(oracle, batches)}
