"""Exact forest targets with asymmetric unaries and a mean-matched weak tail.

Please keep this experiment separate from the previous weighted study. No noise,
hidden-edge score, or true topology is exposed to the sampling controller.
"""
import ctypes
import hashlib
from math import expm1, fsum
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from time import perf_counter

import numpy as np

from confidence import confidence_scores, top_confidence
from toy import feature
from tradeoff_core import balanced_batches
from tree_oracle import TreeOracle, tree_schedule_audit
from weighted_oracle import make_weighted_target, weight_metadata

_BACKEND = None


def load_backend():
    global _BACKEND
    if _BACKEND is None:
        source = Path(__file__).with_name('minimal_tree_bp.c')
        key = hashlib.sha256(source.read_bytes()+sys.platform.encode()).hexdigest()[:20]
        directory = Path(tempfile.gettempdir())/'forest-toy-minimal-bp'
        directory.mkdir(exist_ok=True)
        binary = directory/(key+('.dylib' if sys.platform == 'darwin' else '.so'))
        if not binary.exists():
            temporary = binary.with_name(binary.name+f'.{os.getpid()}.tmp')
            subprocess.run(['cc', '-O3', '-std=c99',
                            '-dynamiclib' if sys.platform == 'darwin' else '-shared',
                            '-fPIC', str(source), '-o', str(temporary), '-lm'],
                           check=True, capture_output=True, text=True)
            os.replace(temporary, binary)
        library = ctypes.CDLL(str(binary))
        integer = np.ctypeslib.ndpointer(dtype=np.int64, flags='C_CONTIGUOUS')
        real = np.ctypeslib.ndpointer(dtype=np.float64, flags='C_CONTIGUOUS')
        library.field_forest_rows.argtypes = [
            ctypes.c_int64, ctypes.c_int64, real, real, integer, integer, integer,
            integer, integer, ctypes.c_int64, integer, real, ctypes.c_int,
            ctypes.c_int64, real]
        library.field_forest_rows.restype = ctypes.c_int
        library.field_chain_kl.argtypes = [ctypes.c_int64, real, real, integer,
                                           integer, real, real, real]
        library.field_chain_kl.restype = ctypes.c_int
        _BACKEND = library
    return _BACKEND


def field_priors(fields):
    fields = np.asarray(fields, dtype=np.float64)
    logits = np.log([.4, .4, .2])[None, :] + fields[:, None]*np.array([1., -1., 0.])
    logits -= logits.max(axis=1, keepdims=True)
    probabilities = np.exp(logits)
    return np.ascontiguousarray(probabilities/probabilities.sum(axis=1, keepdims=True))


class MinimalOracle(TreeOracle):
    """Positive edge factors with normalized position-dependent unary priors."""

    def __init__(self, n, edges, strengths, theta_reference, fields, vocab=2048):
        super().__init__(n, edges, theta_reference, vocab=vocab)
        self.fields = np.ascontiguousarray(fields, dtype=np.float64)
        self.edge_strengths = np.ascontiguousarray(strengths, dtype=np.float64)
        if (self.fields.shape != (n,) or not np.isfinite(self.fields).all()
                or self.edge_strengths.shape != (len(self.edges),)
                or not np.isfinite(self.edge_strengths).all()
                or np.any(self.edge_strengths < 0)
                or np.any(self.edge_strengths > theta_reference)):
            raise ValueError('Please supply finite fields and one bounded nonnegative edge strength.')
        self.prior = field_priors(self.fields)
        self.parent_strength = np.zeros(n, dtype=np.float64)
        incident = np.zeros(n)
        for (u, v), weight in zip(self.edges, self.edge_strengths):
            child = v if self.parent[v] == u else u
            self.parent_strength[child] = weight
            incident[u] += weight
            incident[v] += weight
        self.max_incident_strength = float(incident.max())
        for array in (self.fields, self.edge_strengths, self.prior, self.parent_strength):
            array.flags.writeable = False
        _, z = self._evaluate(np.full((1, n), -1, dtype=np.int64),
                              np.arange(n, dtype=np.int64), compute_z=True)
        self.log_z = float(z[0])

    def _evaluate(self, states, readouts, compute_z=False):
        states = np.ascontiguousarray(states, dtype=np.int64)
        readouts = np.ascontiguousarray(readouts, dtype=np.int64)
        if (states.ndim != 2 or states.shape[1] != self.n or readouts.ndim != 1
                or np.any(states < -1) or np.any(states >= self.vocab)
                or np.any(readouts < 0) or np.any(readouts >= self.n)
                or np.any(states[:, readouts] != -1)):
            raise ValueError('Please submit valid states and mask every requested readout.')
        out = np.empty((len(states), len(readouts), 3), dtype=np.float64)
        log_z = np.zeros(len(states), dtype=np.float64)
        status = load_backend().field_forest_rows(
            self.n, len(states), self.parent_strength, self.prior, self.parent,
            self.order, self.offsets, self.neighbors, states, len(readouts),
            readouts, out, int(compute_z), self.vocab, log_z)
        if status or not np.isfinite(out).all() or not np.isfinite(log_z).all():
            raise ArithmeticError('Exact field-forest inference failed.')
        return out, log_z

    def rows_many(self, states, readouts):
        return self._evaluate(states, readouts)[0]

    def log_probability(self, values):
        values = np.asarray(values, dtype=np.int64)
        if values.shape != (self.n,) or np.any(values < 0) or np.any(values >= self.vocab):
            raise ValueError('Please evaluate a complete assignment.')
        groups = np.minimum(values, 2)
        unary = np.log(self.prior[np.arange(self.n), groups])
        unary[groups == 2] -= np.log(self.vocab-2)
        phi = feature(values)
        edge = np.log1p(self.edge_strengths*phi[self.edges[:, 0]]*phi[self.edges[:, 1]])
        return fsum(map(float, unary))+fsum(map(float, edge))-self.log_z


def field_seed(target, n, repeat):
    key = f'minimal-fields-v1|{target}|{n}|{repeat}'.encode()
    return int.from_bytes(hashlib.sha256(key).digest()[:8], 'little')


def tail_weights(old, theta):
    """Keep support in [0, theta] and match this graph's realized mean exactly.

    Please transform the same uniform quantiles, so edge-strength ranks stay
    paired. F(x)=1-(1-x)^b has finite density at zero and a continuous weak tail.
    The fitted single exponent depends only on target draws, never sampler scores.
    """
    u = np.clip((np.log(old/theta)-np.log(.1))/np.log(10.), 0., 1.)
    target = float(np.mean(old/theta))
    left, right = .01, 10.
    for _ in range(80):
        exponent = (left+right)/2
        candidate = -np.expm1(exponent*np.log1p(-u))
        if candidate.mean() < target:
            left = exponent
        else:
            right = exponent
    exponent = (left+right)/2
    result = theta*(-np.expm1(exponent*np.log1p(-u)))
    if not np.isclose(result.mean(), old.mean(), rtol=0, atol=1e-14):
        raise AssertionError('The paired target means must agree before sampling.')
    return result, 1/exponent


def make_target(target, n, repeat, biased, weak_tail, sigma, kind='proposal', budget=0):
    base, seeds = make_weighted_target(target, n, repeat, 'loguniform10', kind, budget)
    strengths, shape = tail_weights(base.edge_strengths, base.theta) if weak_tail else (base.edge_strengths, None)
    normal = np.random.default_rng(field_seed(target, n, repeat)).normal(size=n)
    oracle = MinimalOracle(n, base.edges, strengths, base.theta,
                           normal*(sigma if biased else 0), base.vocab)
    oracle.weight_seed = base.weight_seed
    oracle.field_seed = field_seed(target, n, repeat)
    oracle.tail_shape = shape
    return oracle, seeds


class ChainEvaluator:
    """Passive exact KL of a selected batch on a hidden collection of paths."""

    def __init__(self, oracle):
        if oracle.max_degree > 2:
            raise ValueError('This exact marginal-KL evaluator is limited to paths and matchings.')
        order, seen, links = [], set(), []
        weights = {tuple(sorted(map(int, e))): float(w)
                   for e, w in zip(oracle.edges, oracle.edge_strengths)}
        for root in range(oracle.n):
            if root in seen or len(oracle.adjacency[root]) > 1:
                continue
            previous, current = -1, root
            while True:
                order.append(current)
                seen.add(current)
                following = [v for v in oracle.adjacency[current] if v != previous]
                if not following:
                    links.append(0.)
                    break
                nxt = following[0]
                links.append(weights[tuple(sorted((current, nxt)))])
                previous, current = current, nxt
        if len(order) != oracle.n:
            raise AssertionError('The evaluator did not reconstruct every hidden path.')
        self.n = oracle.n
        self.order = np.array(order, dtype=np.int64)
        self.inverse = np.argsort(self.order)
        self.prior = np.ascontiguousarray(oracle.prior[self.order])
        self.strengths = np.ascontiguousarray(links, dtype=np.float64)

    def evaluate(self, history, batch):
        history = np.asarray(history, dtype=np.int64)
        batch = np.asarray(batch, dtype=np.int64)
        if len(np.unique(batch)) != len(batch) or np.any(history[batch] >= 0):
            raise ValueError('Please evaluate distinct uncommitted batch positions.')
        selected = np.zeros(self.n, dtype=np.int64)
        selected[self.inverse[batch]] = 1
        ordered_history = np.ascontiguousarray(history[self.order])
        rows = np.empty((self.n, 3), dtype=np.float64)
        pairs, total = np.zeros(self.n), np.zeros(1)
        status = load_backend().field_chain_kl(self.n, self.prior, self.strengths,
                                               ordered_history, selected, rows, pairs, total)
        if status or not np.isfinite(total[0]) or total[0] < 0:
            raise ArithmeticError('Exact batch KL evaluation failed.')
        return float(total[0]), rows[self.inverse], pairs[self.inverse]


class MinimalRecorder:
    """Record commits, then audit KL and density after all decisions have finished."""

    def __init__(self, n):
        self.history = np.full(n, -1, dtype=np.int64)
        self.commit_step = np.full(n, -1, dtype=np.int64)
        self.selected_probability = np.zeros(n)
        self.batches = []

    def __call__(self, batch, rows, values):
        batch, values = np.asarray(batch, dtype=np.int64), np.asarray(values, dtype=np.int64)
        if np.any(self.history[batch] >= 0):
            raise AssertionError('Please never remask or duplicate a committed token.')
        self.commit_step[batch] = len(self.batches)
        self.selected_probability[batch] = rows[np.arange(len(batch)), np.minimum(values, 2)]
        self.history[batch] = values
        self.batches.append(batch.tolist())

    def finish(self, oracle, snapshot=None, *, evaluator=None):
        if np.any(self.history < 0):
            raise ValueError('A censored trajectory has no completed distribution score.')
        started = perf_counter()
        evaluator = ChainEvaluator(oracle) if evaluator is None else evaluator
        history = np.full(oracle.n, -1, dtype=np.int64)
        costs = []
        for batch in self.batches:
            cost = 0.
            if len(batch) > 1:
                cost, rows, _ = evaluator.evaluate(history, batch)
                expected = rows[batch, np.minimum(self.history[batch], 2)]
                if not np.allclose(expected, self.selected_probability[batch], atol=1e-11, rtol=1e-10):
                    raise AssertionError('Passive chain inference disagrees with the actual commit rows.')
            costs.append(cost)
            history[batch] = self.history[batch]
        groups = np.minimum(history, 2)
        log_q = fsum(map(float, np.log(self.selected_probability)-
                        np.log(oracle.prior[np.arange(oracle.n), groups])))
        phi = feature(history)
        log_p = fsum(map(float, np.log1p(oracle.edge_strengths*
                     phi[oracle.edges[:, 0]]*phi[oracle.edges[:, 1]])))-oracle.log_z
        ratio = log_q-log_p
        total = fsum(costs)
        if snapshot is not None:
            snapshot = Path(snapshot)
            snapshot.parent.mkdir(parents=True, exist_ok=True)
            np.savez_compressed(snapshot, values=history, commit_step=self.commit_step,
                                selected_probability=self.selected_probability,
                                batch_kl=np.asarray(costs))
        return {'kl_nats': total, 'kl_per_token': total/oracle.n,
                'positive_kl_batches': sum(c > 1e-20 for c in costs),
                'maximum_batch_kl': max(costs, default=0.),
                'log_q_over_product_prior': log_q, 'log_p_over_product_prior': log_p,
                'log_q_over_p': ratio,
                'tv_score': -expm1(-ratio) if ratio > 0 else 0.,
                'evaluation_seconds': perf_counter()-started,
                **tree_schedule_audit(oracle, self.batches)}


def baseline_sample(oracle, count, order_seed, commit_seed, policy, recorder):
    """Current-history confidence, balanced batches, stochastic values, no remasking."""
    if not 1 <= count <= oracle.n or policy not in ('random', 'confidence'):
        raise ValueError('Please specify random/confidence and a valid batch count.')
    history = np.full(oracle.n, -1, dtype=np.int64)
    rng = np.random.default_rng(commit_seed)
    if policy == 'random':
        schedule = balanced_batches(oracle.n, count, np.random.default_rng(order_seed))
    else:
        order = np.random.default_rng(order_seed).permutation(oracle.n)
        ranks = np.empty(oracle.n, dtype=np.int64)
        ranks[order] = np.arange(oracle.n)
    small, extra = divmod(oracle.n, count)
    for step in range(count):
        if policy == 'random':
            batch = schedule[step]
            rows = oracle.submit(history, batch, 'commit')
        else:
            readouts = np.flatnonzero(history < 0)
            replies = oracle.submit(history, readouts, 'commit')
            selected = top_confidence(confidence_scores(replies, oracle.vocab),
                                      ranks[readouts], small+(step < extra))
            selected = selected[np.argsort(readouts[selected])]
            batch, rows = readouts[selected], replies[selected]
        values = (rng.random(len(batch))[:, None] > rows[:, :2].cumsum(axis=-1)).sum(axis=-1)
        tail = values == 2
        values[tail] = rng.integers(2, oracle.vocab, size=int(tail.sum()))
        recorder(batch, rows, values)
        history[batch] = values
    return history
