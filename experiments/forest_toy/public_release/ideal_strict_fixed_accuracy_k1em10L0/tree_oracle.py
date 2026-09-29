"""An exact general-forest oracle; the existing sampler is used unchanged."""

import ctypes
import hashlib
import heapq
from math import expm1, fsum
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import numpy as np

from toy import Resources, feature, public_state_codes
from tradeoff_core import DensityRecorder, balanced_batches


_BACKEND = None


def load_backend():
    """Compile the local arithmetic helper in temporary storage when necessary."""
    global _BACKEND
    if _BACKEND is None:
        source = Path(__file__).with_name("tree_bp.c")
        key = hashlib.sha256(source.read_bytes() + sys.platform.encode()).hexdigest()[:20]
        directory = Path(tempfile.gettempdir()) / "forest-toy-bp"
        directory.mkdir(exist_ok=True)
        binary = directory / (key + (".dylib" if sys.platform == "darwin" else ".so"))
        if not binary.exists():
            temporary = binary.with_name(binary.name + f".{os.getpid()}.tmp")
            subprocess.run(["cc", "-O3", "-std=c99", "-dynamiclib" if sys.platform == "darwin" else "-shared",
                            "-fPIC", str(source), "-o", str(temporary)], check=True, capture_output=True, text=True)
            os.replace(temporary, binary)
        library = ctypes.CDLL(str(binary))
        integer_array = np.ctypeslib.ndpointer(dtype=np.int64, flags="C_CONTIGUOUS")
        real_array = np.ctypeslib.ndpointer(dtype=np.float64, flags="C_CONTIGUOUS")
        function = library.forest_rows
        function.argtypes = [ctypes.c_int64, ctypes.c_int64, ctypes.c_double,
                             integer_array, integer_array, integer_array, integer_array,
                             integer_array, ctypes.c_int64, integer_array, real_array]
        function.restype = ctypes.c_int
        _BACKEND = function
    return _BACKEND


class TreeOracle:
    """Exact grouped conditionals of prod(mu) prod_edges(1+theta*phi_u*phi_v)."""

    def __init__(self, n, edges, theta, vocab=2048, reuse_queries=True):
        if not isinstance(n, int) or n < 1 or vocab < 3:
            raise ValueError("Please use a positive node count and vocabulary of at least three tokens.")
        self.n, self.theta, self.vocab = n, theta, vocab
        self.edges = np.asarray(edges, dtype=np.int64).reshape(-1, 2)
        if np.any(self.edges < 0) or np.any(self.edges >= n):
            raise ValueError("Every edge endpoint must be a valid vertex.")
        self.adjacency = [[] for _ in range(n)]
        seen_edges = set()
        for u, v in self.edges.tolist():
            edge = tuple(sorted((u, v)))
            if u == v or edge in seen_edges:
                raise ValueError("Please supply distinct, non-loop edges.")
            seen_edges.add(edge)
            self.adjacency[u].append(v)
            self.adjacency[v].append(u)
        self.max_degree = max(map(len, self.adjacency))
        if not 0 < theta <= .5 or theta*self.max_degree > .5 + 1e-12:
            raise ValueError("The finite signal certificate requires theta*maximum_degree <= 1/2.")
        self.parent = np.full(n, -2, dtype=np.int64)
        order = []
        for root in range(n):
            if self.parent[root] != -2:
                continue
            self.parent[root] = -1
            stack = [root]
            while stack:
                u = stack.pop()
                order.append(u)
                for v in sorted(self.adjacency[u]):
                    if v == self.parent[u]:
                        continue
                    if self.parent[v] != -2:
                        raise ValueError("The supplied graph contains a cycle.")
                    self.parent[v] = u
                    stack.append(v)
        self.order = np.asarray(order, dtype=np.int64)
        self.offsets = np.asarray([0, *np.cumsum(list(map(len, self.adjacency)))], dtype=np.int64)
        self.neighbors = np.asarray([v for group in self.adjacency for v in group], dtype=np.int64)
        self.reuse_queries, self.cost = reuse_queries, Resources()

    def rows_many(self, states, readouts):
        states = np.ascontiguousarray(states, dtype=np.int64)
        readouts = np.ascontiguousarray(readouts, dtype=np.int64)
        if (states.ndim != 2 or states.shape[1] != self.n or readouts.ndim != 1
                or np.any(states < -1) or np.any(states >= self.vocab)
                or np.any(readouts < 0) or np.any(readouts >= self.n)):
            raise ValueError("Please submit valid N-token states and readout indices.")
        if np.any(states[:, readouts] != -1):
            raise ValueError("Readouts must be masked in every submitted state.")
        result = np.empty((len(states), len(readouts), 3), dtype=np.float64)
        status = load_backend()(self.n, len(states), self.theta, self.parent, self.order,
                                self.offsets, self.neighbors, states, len(readouts), readouts, result)
        if status or not np.all(np.isfinite(result)):
            raise ArithmeticError("Exact tree conditional evaluation failed.")
        return result

    def rows(self, state, readouts):
        return self.rows_many(np.asarray(state)[None, :], readouts)[0]

    def submit(self, state, readouts, kind):
        rows = self.rows(state, readouts)
        if kind == "preprocessing":
            self.cost.preprocessing += 1
        elif kind == "commit":
            self.cost.rounds += 1
        else:
            raise ValueError("Unknown submission kind.")
        self.cost.returned_rows += len(readouts)
        self.cost.nominal_returned_rows += len(readouts)
        return rows

    def prepare_screen_coloring(self, history, draft, colors, columns, palette):
        codes = public_state_codes(history, draft, colors, columns, palette) if self.reuse_queries else None
        return history, draft, colors, columns, codes

    def submit_chunk_family(self, prepared, chunk, sources):
        history, draft, colors, columns, codes = prepared
        chunk, sources = np.asarray(chunk, dtype=np.int64), np.asarray(sources, dtype=np.int64)
        if np.any(history[chunk] >= 0) or np.any(np.isin(colors[chunk], sources)):
            raise ValueError("Please separate source and readout colors and preserve the commit history.")
        nominal = len(columns)*len(sources)
        if codes is None:
            representatives = inverse = np.arange(nominal)
        else:
            _, representatives, inverse = np.unique(codes[:, sources].ravel(), return_index=True, return_inverse=True)
        states = np.tile(np.where(history >= 0, history, draft), (len(representatives), 1))
        for i, representative in enumerate(representatives):
            column, source = int(representative)//len(sources), sources[int(representative) % len(sources)]
            changed = (history < 0) & (colors == source)
            states[i, changed] = columns[column, changed]
        states[:, chunk] = -1
        replies = self.rows_many(states, chunk)
        self.cost.counterfactual += len(representatives)
        self.cost.nominal_counterfactual += nominal
        self.cost.returned_rows += len(representatives)*len(chunk)
        self.cost.nominal_returned_rows += nominal*len(chunk)
        self.cost.max_screen_width = max(self.cost.max_screen_width, len(chunk))
        return replies[inverse].reshape(len(columns), len(sources), len(chunk), 3).transpose(0, 2, 1, 3)


def make_tree(n, family, seed, coupling=.5):
    """Generate standard shapes, then hide their labels with a random permutation."""
    rng = np.random.default_rng(seed)
    if family == "path":
        edges = [(i-1, i) for i in range(1, n)]
    elif family == "binary":
        edges = [((i-1)//2, i) for i in range(1, n)]
    elif family == "prufer":
        code = rng.integers(n, size=max(0, n-2))
        degrees = np.ones(n, dtype=np.int64) + np.bincount(code, minlength=n)
        leaves = np.flatnonzero(degrees == 1).tolist()
        heapq.heapify(leaves)
        edges = []
        for v in code.tolist():
            u = heapq.heappop(leaves)
            edges.append((u, v))
            degrees[u] -= 1
            degrees[v] -= 1
            if degrees[v] == 1:
                heapq.heappush(leaves, v)
        if len(leaves) == 2:
            edges.append(tuple(leaves))
    else:
        raise ValueError("Unknown standard tree family.")
    permutation = rng.permutation(n)
    edges = permutation[np.asarray(edges, dtype=np.int64).reshape(-1, 2)]
    maximum = int(np.bincount(edges.ravel(), minlength=n).max())
    return TreeOracle(n, edges, coupling/max(1, maximum))


class TreeDensityRecorder(DensityRecorder):
    def finish(self, oracle, values):
        if not np.all(self._seen):
            raise ValueError("Please finish every token before evaluating its joint density.")
        phi = feature(np.asarray(values))
        terms = np.log1p(oracle.theta*phi[oracle.edges[:, 0]]*phi[oracle.edges[:, 1]])
        log_p, log_q = fsum(map(float, terms)), fsum(self._terms)
        ratio = log_q-log_p
        score = -expm1(-ratio) if ratio > 0 else 0.0
        return {"log_q_over_product": log_q, "log_p_over_product": log_p, "log_q_over_p": ratio,
                "tv_score": score, "tv_score_above_numerical_floor": score > 1e-10}


def tree_schedule_audit(oracle, batches):
    """Reconstruct residual components in reverse order, only after sampling."""
    parent = list(range(oracle.n))
    size = [1]*oracle.n
    active = [False]*oracle.n

    def root(u):
        while parent[u] != u:
            parent[u] = parent[parent[u]]
            u = parent[u]
        return u

    unsafe = 0
    for batch in reversed(batches):
        for u in batch:
            if active[u]:
                raise ValueError("A saved schedule commits a vertex more than once.")
            active[u] = True
        for u in batch:
            for v in oracle.adjacency[u]:
                if active[v]:
                    a, b = root(u), root(v)
                    if a != b:
                        if size[a] < size[b]:
                            a, b = b, a
                        parent[b] = a
                        size[a] += size[b]
        unsafe += len({root(u) for u in batch}) != len(batch)
    return {"unsafe_batches": int(unsafe), "all_tokens_committed": all(active)}


def tree_random_batch_sample(oracle, count, order_seed, commit_seed):
    batches = balanced_batches(oracle.n, count, np.random.default_rng(order_seed))
    history = np.full(oracle.n, -1, dtype=np.int64)
    recorder, rng = TreeDensityRecorder(oracle.n), np.random.default_rng(commit_seed)
    for batch in batches:
        rows = oracle.submit(history, batch, "commit")
        values = (rng.random(len(batch))[:, None] > rows[:, :2].cumsum(axis=-1)).sum(axis=-1)
        tail = values == 2
        values[tail] = rng.integers(2, oracle.vocab, size=int(tail.sum()))
        history[batch] = values
        recorder(batch, rows, values)
    saved_batches = [batch.tolist() for batch in batches]
    return {"sample": history, "batches": saved_batches, **recorder.finish(oracle, history),
            **tree_schedule_audit(oracle, saved_batches)}
