"""Exact commit arithmetic, passive density scores, and a random-batch baseline.

Target structure is used only inside the oracle cursor and the post-run scorer.
The baseline chooses its entire balanced partition without seeing the forest.
"""

from math import expm1, fsum

import numpy as np

from toy import MU, feature


class CommitCursor:
    """Oracle-internal sufficient statistics for a no-remasking commit history."""

    def __init__(self, oracle):
        self.oracle = oracle
        self._history = np.full(oracle.n, -1, dtype=np.int64)
        self.history = self._history.view()
        self.history.flags.writeable = False
        self._counts = np.zeros((len(oracle.roots), 2), dtype=np.int64)
        self._log_kernel = np.array([[np.log1p(oracle.theta), np.log1p(-oracle.theta)],
                                     [np.log1p(-oracle.theta), np.log1p(oracle.theta)]])
        self._pending = None

    def submit(self, readouts):
        readouts = np.asarray(readouts, dtype=np.int64)
        if self._pending is not None:
            raise ValueError("Please append the preceding commit before submitting another one.")
        if (not len(readouts) or np.any(readouts < 0) or np.any(readouts >= self.oracle.n)
                or len(np.unique(readouts)) != len(readouts) or np.any(self._history[readouts] >= 0)):
            raise ValueError("Please submit distinct, valid, uncommitted positions.")
        oracle = self.oracle
        counts = self._counts[oracle.component[readouts]]
        fields = (counts[:, 0, None] * self._log_kernel[0]
                  + counts[:, 1, None] * self._log_kernel[1])
        posterior = oracle._posterior(fields)
        root_values = self._history[oracle.root_of[readouts]]
        mean = np.where(root_values >= 0, feature(root_values), posterior[:, 0] - posterior[:, 1])
        leaves = np.stack((0.4 * (1 + oracle.theta * mean),
                           0.4 * (1 - oracle.theta * mean), np.full(len(readouts), 0.2)), axis=-1)
        rows = np.where(oracle.leaf[readouts, None], leaves, posterior)
        oracle.cost.rounds += 1
        oracle.cost.returned_rows += len(readouts)
        oracle.cost.nominal_returned_rows += len(readouts)
        self._pending = readouts.copy()
        return rows

    def append(self, batch, values):
        batch, values = np.asarray(batch, dtype=np.int64), np.asarray(values, dtype=np.int64)
        if self._pending is None or not np.array_equal(batch, self._pending):
            raise ValueError("Please append exactly the batch whose rows were submitted.")
        if values.shape != batch.shape or np.any(values < 0) or np.any(values >= self.oracle.vocab):
            raise ValueError("Please append one valid token value per submitted position.")
        self._history[batch] = values
        active = self.oracle.leaf[batch] & (values < 2)
        np.add.at(self._counts, (self.oracle.component[batch[active]], values[active]), 1)
        self._pending = None


class DensityRecorder:
    """Accumulate log Q_w(x)/prod mu(x_j) from the actually used commit rows."""

    def __init__(self, n):
        self._seen = np.zeros(n, dtype=bool)
        self._terms = []

    def __call__(self, batch, rows, values):
        batch = np.asarray(batch, dtype=np.int64)
        if np.any(self._seen[batch]):
            raise ValueError("A likelihood may include each token exactly once.")
        groups = np.minimum(np.asarray(values), 2)
        selected = rows[np.arange(len(batch)), groups]
        # Please cancel the uniform-tail factors before taking logs. The result
        # is the likelihood ratio for the full vocabulary, not a lossy score.
        self._terms.append(float(np.log1p((selected - MU[groups]) / MU[groups]).sum()))
        self._seen[batch] = True

    def finish(self, oracle, values):
        """Use the hidden forest only after all sampling decisions are complete."""
        if not np.all(self._seen):
            raise ValueError("Please finish committing every token before scoring.")
        phi = feature(np.asarray(values))
        edge_terms = np.log1p(oracle.theta * phi[oracle.leaf] * phi[oracle.root_of[oracle.leaf]])
        log_p_relative = fsum(map(float, edge_terms))
        log_q_relative = fsum(self._terms)
        ratio = log_q_relative - log_p_relative
        score = -expm1(-ratio) if ratio > 0 else 0.0
        return {"log_q_over_product": log_q_relative, "log_p_over_product": log_p_relative,
                "log_q_over_p": ratio, "tv_score": score,
                "tv_score_above_numerical_floor": score > 1e-10}


def balanced_batches(n, count, rng):
    """Partition a random permutation into exactly count nonempty balanced batches."""
    if not 1 <= count <= n:
        raise ValueError("Please use a nonempty batch count between 1 and N.")
    order = rng.permutation(n)
    # array_split assigns the extra positions to the first batches, e.g. 3+3+2.
    return [np.sort(part) for part in np.array_split(order, count)]


def random_batch_sample(oracle, count, order_seed, commit_seed, fast=True):
    batches = balanced_batches(oracle.n, count, np.random.default_rng(order_seed))
    session = CommitCursor(oracle) if fast else None
    history = np.full(oracle.n, -1, dtype=np.int64) if session is None else session.history
    recorder = DensityRecorder(oracle.n)
    rng = np.random.default_rng(commit_seed)
    for batch in batches:
        rows = oracle.submit(history, batch, "commit") if session is None else session.submit(batch)
        uniforms = rng.random(len(batch))
        values = (uniforms[:, None] > rows[:, :2].cumsum(axis=-1)).sum(axis=-1)
        tail = values == 2
        values[tail] = rng.integers(2, oracle.vocab, size=int(tail.sum()))
        if session is None:
            history[batch] = values
        else:
            session.append(batch, values)
        recorder(batch, rows, values)
    return {"sample": history, "batches": [batch.tolist() for batch in batches],
            **recorder.finish(oracle, history)}


def schedule_audit(oracle, batches):
    """Post-run structural diagnostic shared by both algorithms."""
    committed = np.zeros(oracle.n, dtype=bool)
    unsafe = 0
    for batch in batches:
        batch = np.asarray(batch, dtype=np.int64)
        roots = oracle.root_of[batch]
        # Committed roots split their residual leaves into separate components.
        components = np.where(committed[roots], batch, roots)
        unsafe += len(np.unique(components)) != len(batch)
        if np.any(committed[batch]):
            raise ValueError("Duplicate commits in the saved schedule.")
        committed[batch] = True
    return {"unsafe_batches": int(unsafe), "all_tokens_committed": bool(np.all(committed))}
