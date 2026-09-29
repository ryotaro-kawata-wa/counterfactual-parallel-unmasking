"""Balanced confidence batches using one current-history response per batch."""

import numpy as np

from tradeoff_core import CommitCursor, DensityRecorder, schedule_audit
from tree_oracle import TreeDensityRecorder, tree_schedule_audit


def confidence_scores(rows, vocab):
    """Please compare individual vocabulary labels, not the aggregated tail mass."""
    return np.maximum(rows[:, :2].max(axis=1), rows[:, 2]/(vocab-2))


def top_confidence(scores, tie_ranks, count):
    """Select the exact top set, resolving equal scores by a fixed random priority."""
    if not 1 <= count <= len(scores):
        raise ValueError('Please request a nonempty subset of the available positions.')
    if count == len(scores):
        return np.arange(len(scores))
    threshold = np.partition(scores, len(scores)-count)[len(scores)-count]
    above = np.flatnonzero(scores > threshold)
    tied = np.flatnonzero(scores == threshold)
    needed = count-len(above)
    if needed < len(tied):
        tied = tied[np.argpartition(tie_ranks[tied], needed-1)[:needed]]
    return np.concatenate((above, tied))


class SelectionCursor(CommitCursor):
    """Exact star-forest arithmetic allowing a subset of queried rows to commit."""

    def append_selected(self, batch, values):
        if self._pending is None or not np.all(np.isin(batch, self._pending)):
            raise ValueError('Please choose only positions in the current oracle response.')
        self._pending = np.asarray(batch).copy()
        super().append(batch, values)


def confidence_batch_sample(oracle, count, order_seed, commit_seed, fast=True, observer=None):
    if not 1 <= count <= oracle.n:
        raise ValueError('Please use a batch count between 1 and N.')
    is_tree = hasattr(oracle, 'edges')
    session = SelectionCursor(oracle) if fast and not is_tree else None
    history = np.full(oracle.n, -1, dtype=np.int64) if session is None else session.history
    recorder = TreeDensityRecorder(oracle.n) if is_tree else DensityRecorder(oracle.n)
    rng = np.random.default_rng(commit_seed)
    order = np.random.default_rng(order_seed).permutation(oracle.n)
    tie_ranks = np.empty(oracle.n, dtype=np.int64)
    tie_ranks[order] = np.arange(oracle.n)
    small, extra = divmod(oracle.n, count)
    batches = []
    for step in range(count):
        remaining = np.flatnonzero(history < 0)
        rows = oracle.submit(history, remaining, 'commit') if session is None else session.submit(remaining)
        selected = top_confidence(confidence_scores(rows, oracle.vocab), tie_ranks[remaining], small+(step < extra))
        selected = selected[np.argsort(remaining[selected])]
        batch, used = remaining[selected], rows[selected]
        values = (rng.random(len(batch))[:, None] > used[:, :2].cumsum(axis=-1)).sum(axis=-1)
        tail = values == 2
        values[tail] = rng.integers(2, oracle.vocab, size=int(tail.sum()))
        if observer is not None:
            observer(history, remaining, rows, batch, values)
        if session is None:
            history[batch] = values
        else:
            session.append_selected(batch, values)
        recorder(batch, used, values)
        batches.append(batch.tolist())
    checked = tree_schedule_audit(oracle, batches) if is_tree else schedule_audit(oracle, batches)
    return {'sample': history, 'batches': batches, **recorder.finish(oracle, history), **checked}
