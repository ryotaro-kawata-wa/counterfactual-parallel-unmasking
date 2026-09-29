"""Executable finite packed-screen sampler with an exact star-forest oracle.

Please keep target structure inside the oracle and the post-run auditor.
The controller uses only public parameters, returned rows, and its history.
Rows are represented by their two head masses and aggregate uniform-tail mass;
this is a lossless representation for this particular toy family.
"""

from dataclasses import dataclass
from math import ceil, log, log2

import numpy as np


MU = np.array([0.4, 0.4, 0.2])
PHI = np.array([1.0, -1.0, 0.0])


def feature(values):
    return np.where(values == 0, 1.0, np.where(values == 1, -1.0, 0.0))


@dataclass
class Resources:
    preprocessing: int = 0
    counterfactual: int = 0
    nominal_counterfactual: int = 0
    rounds: int = 0
    returned_rows: int = 0
    nominal_returned_rows: int = 0
    max_screen_width: int = 0

    @property
    def total(self):
        return self.preprocessing + self.counterfactual + self.rounds


@dataclass(frozen=True)
class Parameters:
    n: int
    theta: float
    vocab: int = 2048
    d: int = 9
    chunks: int = 1
    beta: float = 1e-6
    failure: float = 0.01
    palette_override: int = None
    coloring_coefficient: float = None

    def __post_init__(self):
        if not (self.n >= 10 and 9 <= self.d < self.n):
            raise ValueError("Please use the finite domain N >= 10 and 9 <= d < N.")
        if not (1 <= self.chunks <= self.n and self.vocab >= 3):
            raise ValueError("Invalid chunk count or vocabulary size.")
        if not (0 < self.theta <= 0.5 and 0 <= self.beta <= 1 and 0 < self.failure < 1):
            raise ValueError("Invalid coupling, oracle radius, or failure budget.")
        if self.palette_override is not None and self.palette_override < 2:
            raise ValueError("Please use at least two colors.")
        if self.coloring_coefficient is not None and self.coloring_coefficient <= 0:
            raise ValueError("Please use a positive coefficient of log(N).")
        if 4 * self.eps + self.tail_tolerance >= self.signal:
            raise ValueError("The finite screen separation is not satisfied.")

    @property
    def eps(self):
        return self.beta / self.n ** 0.5

    @property
    def response_constant(self):
        return 10 * self.theta

    @property
    def tail_tolerance(self):
        return self.theta / 16

    @property
    def signal(self):
        return self.theta / 10

    @property
    def peel_cap(self):
        return ceil(max(0, log(2 * self.n / (self.d + 1))) / log(self.d / 8))

    @property
    def screen_cap(self):
        return self.peel_cap + 1

    @property
    def round_cap(self):
        return ceil(4 * self.n * self.peel_cap / self.d) + ceil(log2(self.n + 1)) + 2

    @property
    def palette(self):
        return 8 * (self.d + 1) if self.palette_override is None else self.palette_override

    @property
    def colorings(self):
        if self.coloring_coefficient is not None:
            minimum = ceil(self.coloring_coefficient * log(self.n))
            return minimum + (minimum % 2 == 0)
        return ceil(8 * log(self.screen_cap * self.n ** 2 / self.failure))


def public_state_codes(history, draft, colors, columns, palette):
    """Identify identical source assignments using public inputs only.

    Please use these codes only within a fixed readout chunk. Its color must
    differ from every source color, so masking does not erase a source change.
    """
    signatures = {b"": 0}
    codes = np.zeros((len(columns), palette), dtype=np.int64)
    for color in range(palette):
        group = np.flatnonzero((history < 0) & (colors == color))
        for k, column in enumerate(columns):
            changed = group[column[group] != draft[group]]
            signature = np.stack((changed, column[changed]), axis=-1).astype("<i8").tobytes()
            if signature not in signatures:
                signatures[signature] = len(signatures)
            codes[k, color] = signatures[signature]
    return codes


class StarForestOracle:
    """Exact conditionals for mu(root) prod K(leaf | root), K=mu(1+theta phi phi)."""

    def __init__(self, root_of, theta, vocab=2048, reuse_queries=False):
        self.root_of = np.asarray(root_of, dtype=np.int64)
        self.n = len(self.root_of)
        self.roots = np.flatnonzero(self.root_of == np.arange(self.n))
        if not np.all(np.isin(self.root_of, self.roots)):
            raise ValueError("Please supply a union of rooted stars, including isolates.")
        self.component = np.searchsorted(self.roots, self.root_of)
        self.leaf = self.root_of != np.arange(self.n)
        self.theta, self.vocab = theta, vocab
        self.reuse_queries = reuse_queries
        degree = np.bincount(self.component[self.leaf], minlength=len(self.roots)).max()
        if theta <= 0 or theta > 0.5 or theta * degree > 0.5 + 1e-12:
            raise ValueError("The toy's uniform signal certificate needs theta * max_degree <= 1/2.")
        self.cost = Resources()

    def _fields(self, values, included):
        leaves = self.leaf & included
        phi = feature(values[leaves])
        return np.stack([
            np.bincount(self.component[leaves], weights=np.log1p(sign * self.theta * phi),
                        minlength=len(self.roots))
            for sign in (1, -1)
        ], axis=-1)

    @staticmethod
    def _posterior(fields):
        head = MU[:2] * np.exp(fields)
        weights = np.concatenate((head, np.full(head.shape[:-1] + (1,), MU[2])), axis=-1)
        return weights / weights.sum(axis=-1, keepdims=True)

    def rows(self, state, readouts):
        """Return exact grouped rows; this unmetered helper is also used by validation."""
        state, readouts = np.asarray(state), np.asarray(readouts, dtype=np.int64)
        if np.any(state[readouts] != -1):
            raise ValueError("Readouts must be masked.")
        posterior = self._posterior(self._fields(state, state >= 0))[self.component[readouts]]
        root_values = state[self.root_of[readouts]]
        mean = np.where(root_values >= 0, feature(root_values), posterior[:, 0] - posterior[:, 1])
        leaf_rows = np.stack((0.4 * (1 + self.theta * mean),
                              0.4 * (1 - self.theta * mean), np.full(len(readouts), 0.2)), axis=-1)
        return np.where(self.leaf[readouts, None], leaf_rows, posterior)

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
        """Compile shared arithmetic for the actual packed states of one coloring.

        Compilation changes arithmetic cost, not Q. In the opt-in reuse mode,
        please identify duplicate assignments from public inputs before evaluation.
        """
        values = np.where(history >= 0, history, draft)
        base = self._fields(values, np.ones(self.n, dtype=bool))
        leaves = self.leaf & (history < 0)
        slots = self.component[leaves] * palette + colors[leaves]
        old_phi = feature(draft[leaves])
        deltas = []
        for column in columns:
            new_phi = feature(column[leaves])
            deltas.append(np.stack([
                np.bincount(slots,
                            weights=np.log1p(sign * self.theta * new_phi)
                            - np.log1p(sign * self.theta * old_phi),
                            minlength=len(self.roots) * palette).reshape(len(self.roots), palette)
                for sign in (1, -1)
            ], axis=-1))
        codes = public_state_codes(history, draft, colors, columns, palette) if self.reuse_queries else None
        return history, draft, colors, columns, base, np.stack(deltas), codes

    def _evaluate_unique_pairs(self, prepared, chunk, column_ids, sources):
        """Evaluate only the representative states, with axes (state, readout, token)."""
        history, draft, colors, columns, base, deltas, _ = prepared
        masked = np.zeros(self.n, dtype=bool)
        masked[chunk] = True
        components = self.component[chunk]
        removed = self._fields(draft, masked)
        fields = ((base - removed)[components][None, :, :]
                  + deltas[column_ids[:, None], components[None, :], sources[:, None]])
        posterior = self._posterior(fields)
        roots = self.root_of[chunk]
        mean = np.where(colors[roots][None, :] == sources[:, None],
                        feature(columns[column_ids[:, None], roots[None, :]]),
                        feature(draft[roots])[None, :])
        mean = np.where(history[roots][None, :] >= 0, feature(history[roots])[None, :], mean)
        mean = np.where(masked[roots][None, :], posterior[..., 0] - posterior[..., 1], mean)
        leaf_rows = np.stack((0.4 * (1 + self.theta * mean),
                             0.4 * (1 - self.theta * mean), np.full(mean.shape, 0.2)), axis=-1)
        return np.where(self.leaf[chunk][None, :, None], leaf_rows, posterior)

    def submit_chunk_family(self, prepared, chunk, sources):
        """Evaluate all (column, source-color) states, returning every requested row.

        The array has axes (column, readout, source color, grouped token).
        The reuse mode evaluates one representative per identical input state and
        expands its reply for the unchanged diameter and majority calculations.
        """
        history, draft, colors, columns, base, deltas, codes = prepared
        chunk = np.asarray(chunk, dtype=np.int64)
        sources = np.asarray(sources, dtype=np.int64)
        if np.any(history[chunk] >= 0) or np.any(np.isin(colors[chunk], sources)):
            raise ValueError("A probe must preserve history and separate source and readout colors.")
        nominal = len(columns) * len(sources)
        self.cost.nominal_counterfactual += nominal
        self.cost.nominal_returned_rows += nominal * len(chunk)
        self.cost.max_screen_width = max(self.cost.max_screen_width, len(chunk))
        if codes is not None:
            _, representatives, inverse = np.unique(codes[:, sources].ravel(),
                                                   return_index=True, return_inverse=True)
            column_ids = representatives // len(sources)
            source_ids = sources[representatives % len(sources)]
            unique_rows = self._evaluate_unique_pairs(prepared, chunk, column_ids, source_ids)
            self.cost.counterfactual += len(representatives)
            self.cost.returned_rows += len(representatives) * len(chunk)
            return unique_rows[inverse].reshape(len(columns), len(sources), len(chunk), 3).transpose(0, 2, 1, 3)
        masked = np.zeros(self.n, dtype=bool)
        masked[chunk] = True
        removed = self._fields(draft, masked)
        components = self.component[chunk]
        fields = (base - removed)[components][None, :, None, :] + deltas[:, components][:, :, sources]
        posterior = self._posterior(fields)
        roots = self.root_of[chunk]
        mean = np.where(colors[roots][None, :, None] == sources[None, None, :],
                        feature(columns[:, roots])[:, :, None], feature(draft[roots])[None, :, None])
        mean = np.where(history[roots][None, :, None] >= 0,
                        feature(history[roots])[None, :, None], mean)
        mean = np.where(masked[roots][None, :, None], posterior[..., 0] - posterior[..., 1], mean)
        leaf_rows = np.stack((0.4 * (1 + self.theta * mean),
                              0.4 * (1 - self.theta * mean), np.full(mean.shape, 0.2)), axis=-1)
        rows = np.where(self.leaf[chunk][None, :, None, None], leaf_rows, posterior)
        submissions = len(columns) * len(sources)
        self.cost.counterfactual += submissions
        self.cost.returned_rows += submissions * len(chunk)
        return rows


def make_forest(n, family, seed, vocab=2048, coupling=0.5, reuse_queries=False):
    """Randomize labels so the controller cannot recover edges from position order."""
    rng = np.random.default_rng(seed)
    order = rng.permutation(n)
    degree = 1 if family == "matching" else max(16, ceil(n ** 0.5))
    if family not in ("matching", "stars"):
        raise ValueError("Unknown forest family.")
    root_of = np.arange(n)
    for start in range(0, n, degree + 1):
        group = order[start:start + degree + 1]
        root_of[group] = group[0]
    return StarForestOracle(root_of, coupling / min(degree, n - 1), vocab, reuse_queries=reuse_queries)


class MajorityVotes:
    """Exact bit-sliced counters avoid a dense N-by-N matrix of Python integers."""

    def __init__(self, n, count):
        self.planes = [[0] * count.bit_length() for _ in range(n)]
        self.threshold = count // 2
        self.universe = (1 << n) - 1

    def add(self, readout, voters):
        for bit in range(len(self.planes[readout])):
            if not voters:
                break
            old = self.planes[readout][bit]
            self.planes[readout][bit] = old ^ voters
            voters &= old

    def majority_mask(self, readout, threshold=None):
        """Expose the current votes for passive diagnostics, without changing them."""
        threshold = self.threshold if threshold is None else threshold
        equal, greater = self.universe, 0
        for bit in reversed(range(len(self.planes[readout]))):
            plane = self.planes[readout][bit]
            if (threshold >> bit) & 1:
                equal &= plane
            else:
                greater |= equal & plane
                equal &= ~plane
        return greater

    def row(self, readout, cutoff):
        greater = self.majority_mask(readout)
        result = set()
        while greater:
            low = greater & -greater
            result.add(low.bit_length() - 1)
            if len(result) > cutoff:
                return set()
            greater ^= low
        return result


def preprocess(oracle, params):
    eps = params.eps
    floor = max(4 * eps, 2 * (eps + 1 / params.vocab), 8 / params.vocab)
    if floor > 1:
        raise ValueError("Infeasible threshold floor.")
    grid = {max(floor, 2.0 ** -k) for k in range(ceil(log2(1 / floor)) + 1)}
    feasible = [t for t in grid if min(1, params.response_constant * t) <= params.tail_tolerance]
    if not feasible:
        raise ValueError("Infeasible tail-response threshold.")
    threshold = max(feasible)
    rows = oracle.submit(np.full(params.n, -1), np.arange(params.n), "preprocessing")
    banks, tails, drafts = [], [], []
    for row in rows:
        full = np.concatenate((row[:2], np.full(params.vocab - 2, row[2] / (params.vocab - 2))))
        bank = np.flatnonzero(full >= threshold - eps).tolist()
        banks.append(bank)
        tails.append(next(i for i in range(params.vocab) if i not in bank))
        drafts.append(int(np.argmax(full)))
    maximum = max(map(len, banks))
    columns = [[bank[k] if k < len(bank) else drafts[i] for i, bank in enumerate(banks)]
               for k in range(maximum)]
    columns.append(tails)
    return np.asarray(drafts), np.asarray(columns), threshold, maximum


def packed_screen(oracle, params, history, draft, columns, rng, colorings=None, observer=None):
    residual = np.flatnonzero(history < 0)
    if observer is not None:
        observer.start_screen(history, draft, columns)
    if len(columns) <= 1 or not len(residual):
        return {int(j): set() for j in residual}
    count = params.colorings if colorings is None else len(colorings)
    votes = MajorityVotes(params.n, count)
    width = ceil(params.n / params.chunks)
    for tau in range(count):
        colors = (rng.integers(params.palette, size=params.n) if colorings is None
                  else np.asarray(colorings[tau]))
        groups = [residual[colors[residual] == c] for c in range(params.palette)]
        masks = [sum(1 << int(i) for i in group) for group in groups]
        if observer is not None:
            observer.observe_coloring(groups, draft, columns)
        prepared = oracle.prepare_screen_coloring(history, draft, colors, columns, params.palette)
        for readout_color, group in enumerate(groups):
            sources = np.array([c for c in range(params.palette) if c != readout_color])
            for start in range(0, len(group), width):
                chunk = group[start:start + width]
                rows = oracle.submit_chunk_family(prepared, chunk, sources)
                diameter = np.zeros((len(chunk), len(sources)))
                for first in range(len(columns)):
                    for second in range(first):
                        diameter = np.maximum(diameter, np.abs(rows[first] - rows[second]).sum(axis=-1) / 2)
                if observer is not None:
                    observer.observe_chunk(chunk, sources, diameter)
                positive_readouts, positive_sources = np.nonzero(diameter > 2 * params.eps)
                voters = [0] * len(chunk)
                for j, c in zip(positive_readouts, positive_sources):
                    voters[j] |= masks[int(sources[c])]
                for j, mask in zip(chunk, voters):
                    votes.add(int(j), mask)
        if observer is not None:
            observer.observe_prefix(tau + 1, count, votes)
    result = {int(j): votes.row(int(j), params.d) for j in residual}
    if observer is not None:
        observer.finish_screen(result)
    return result


def centroid_batch(graph):
    """Return smallest-label centroids; return None if a component has a cycle."""
    seen, batch = set(), []
    for root in sorted(graph):
        if root in seen:
            continue
        parent, order = {root: None}, [root]
        seen.add(root)
        for u in order:
            for v in sorted(graph[u]):
                if v == parent[u]:
                    continue
                if v in seen:
                    return None
                parent[v] = u
                seen.add(v)
                order.append(v)
        size = {u: 1 for u in order}
        largest = {u: 0 for u in order}
        for u in reversed(order):
            if parent[u] is not None:
                size[parent[u]] += size[u]
                largest[parent[u]] = max(largest[parent[u]], size[u])
        batch.append(min(u for u in order if max(largest[u], len(order) - size[u]) * 2 <= len(order)))
    return batch


def sample(oracle, params, controller_seed, commit_seed, observer=None,
           commit_session=None, commit_observer=None):
    """Execute the manuscript controller with optional equivalent commit arithmetic.

    Please keep the session's public history synchronized through append(). The
    commit observer is passive and must not control batch selection or draws.
    """
    rng, commit_rng = np.random.default_rng(controller_seed), np.random.default_rng(commit_seed)
    draft, columns, threshold, maximum = preprocess(oracle, params)
    history = (np.full(params.n, -1, dtype=np.int64) if commit_session is None else commit_session.history)
    if len(history) != params.n or np.any(history >= 0):
        raise ValueError("Please start with an empty commit history of the requested length.")
    screens, batches, screen_costs, fallback = [], [], [], None

    def commit(batch):
        batch = np.array(sorted(batch), dtype=np.int64)
        if not len(batch) or np.any(history[batch] >= 0):
            raise ValueError("Please commit a nonempty, previously uncommitted batch.")
        rows = (oracle.submit(history, batch, "commit") if commit_session is None
                else commit_session.submit(batch))
        uniforms = commit_rng.random(len(batch))
        values = (uniforms[:, None] > rows[:, :2].cumsum(axis=-1)).sum(axis=-1)
        tail = values == 2
        values[tail] = commit_rng.integers(2, params.vocab, size=int(tail.sum()))
        if commit_session is None:
            history[batch] = values
        else:
            commit_session.append(batch, values)
        if commit_observer is not None:
            commit_observer(batch, rows, values)
        batches.append(batch.tolist())

    for phase in range(params.screen_cap):
        if np.all(history >= 0):
            break
        before = (oracle.cost.counterfactual, oracle.cost.nominal_counterfactual, oracle.cost.returned_rows)
        rows = packed_screen(oracle, params, history, draft, columns, rng, observer=observer)
        screen_costs.append({"counterfactual": oracle.cost.counterfactual - before[0],
                             "nominal_counterfactual": oracle.cost.nominal_counterfactual - before[1],
                             "returned_rows": oracle.cost.returned_rows - before[2]})
        claims = np.zeros(params.n, dtype=np.int64)
        for neighbors in rows.values():
            for v in neighbors:
                claims[v] += 1
        peel = np.flatnonzero((history < 0) & (claims > params.d / 2)).tolist()
        screens.append({"rows": rows, "peel": peel})
        if observer is not None:
            observer.observe_controller(peel, claims, phase)
        if not peel or phase == params.peel_cap:
            graph = {j: set() for j in rows}
            for j, neighbors in rows.items():
                for i in neighbors:
                    graph[j].add(i)
                    graph[i].add(j)
            while graph:
                batch = centroid_batch(graph)
                if batch is None or len(batches) == params.round_cap - 1:
                    fallback = "nonforest" if batch is None else "round_cap"
                    commit(np.flatnonzero(history < 0))
                    graph.clear()
                    break
                commit(batch)
                for j in batch:
                    for i in graph[j]:
                        graph[i].remove(j)
                    del graph[j]
            break
        for v in peel:
            if len(batches) == params.round_cap - 1:
                fallback = "round_cap"
                commit(np.flatnonzero(history < 0))
                break
            commit([v])
    if np.any(history < 0):
        raise AssertionError("The controller did not finish its assignment.")
    return {"sample": history, "screens": screens, "batches": batches, "fallback": fallback,
            "threshold": threshold, "bank_size": maximum, "screen_costs": screen_costs}


def audit(oracle, params, result):
    """Use the hidden forest only after sampling, without altering controller decisions."""
    true_graph = {i: set() for i in range(oracle.n)}
    for leaf in np.flatnonzero(oracle.leaf):
        root = int(oracle.root_of[leaf])
        true_graph[int(leaf)].add(root)
        true_graph[root].add(int(leaf))
    checked = errors = 0
    for screen in result["screens"]:
        residual = set(screen["rows"])
        for j, neighbors in screen["rows"].items():
            truth = true_graph[j] & residual
            if len(truth) <= params.d:
                checked += 1
                errors += neighbors != truth
    terminal = result["screens"][-1]["rows"]
    residual = set(terminal)
    terminal_errors = sum(neighbors != (true_graph[j] & residual) for j, neighbors in terminal.items())
    committed, unsafe = set(), 0
    for batch in result["batches"]:
        components = []
        for j in batch:
            root = int(oracle.root_of[j])
            components.append(("isolated", j) if root in committed else ("star", root))
        unsafe += len(components) != len(set(components))
        committed.update(batch)
    return {"low_degree_rows_checked": checked, "low_degree_row_errors": int(errors),
            "terminal_row_errors": int(terminal_errors), "unsafe_batches": int(unsafe),
            "all_tokens_committed": len(committed) == params.n,
            "fallback": result["fallback"]}
