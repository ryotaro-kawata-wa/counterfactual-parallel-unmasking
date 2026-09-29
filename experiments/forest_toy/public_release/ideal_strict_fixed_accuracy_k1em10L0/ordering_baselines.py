"""Marginal-only ordering and entropy-bounded parallel sampling controls.

Please evaluate probabilities on the full vocabulary. The third oracle column
is a compressed *total* tail mass, rather than a single vocabulary label.
EB follows Eq. (2) and Fig. 4 of https://arxiv.org/abs/2505.24857, with sampled
values (temperature one) and a fresh current-history response at every step.
"""
import numpy as np

from confidence import confidence_scores, top_confidence
from tradeoff_core import balanced_batches


ORDERINGS = ('confidence', 'margin', 'entropy')


def categorical_entropy(rows, vocab):
    """Please include the multiplicity of the equally probable tail labels."""
    rows = np.asarray(rows, dtype=np.float64)
    if vocab < 3 or rows.ndim != 2 or rows.shape[1] != 3:
        raise ValueError('Please supply grouped categorical rows and vocab >= 3.')
    if not np.isfinite(rows).all() or np.any(rows < 0):
        raise ValueError('Please supply finite nonnegative probabilities.')
    logs = np.zeros_like(rows)
    np.log(rows, out=logs, where=rows > 0)
    return -(rows*logs).sum(axis=1)+rows[:, 2]*np.log(vocab-2)


def ordering_scores(rows, vocab, policy):
    """Return scores for which larger means earlier unmasking."""
    if policy == 'confidence':
        return confidence_scores(rows, vocab)
    if policy == 'entropy':
        return -categorical_entropy(rows, vocab)
    if policy == 'margin':
        tail = rows[:, 2:3]/(vocab-2)
        # Please allow two distinct tail labels to occupy the two highest ranks.
        candidates = np.concatenate((rows[:, :2], tail,
                                     tail if vocab > 3 else np.zeros_like(tail)), axis=1)
        highest = np.partition(candidates, -2, axis=1)[:, -2:]
        return highest[:, 1]-highest[:, 0]
    raise ValueError('Please choose confidence, margin, or entropy ordering.')


def entropy_bounded_selection(rows, vocab, tie_ranks, policy, gamma):
    """Select the longest ordered prefix with sum(H)-max(H) <= gamma.

    The positive minimum entropy provides a conservative prefix-length bound.
    Please use it only to avoid sorting the entire row array; the resulting
    selection is identical to sorting all rows and applying the paper's rule.
    """
    if policy not in ORDERINGS or not np.isfinite(gamma) or gamma < 0 or not len(rows):
        raise ValueError('Please use a supported ordering, nonempty rows, and finite gamma >= 0.')
    entropies = categorical_entropy(rows, vocab)
    n = len(rows)
    full_bound = float(entropies.sum()-entropies.max())
    if full_bound+1e-12*max(1., full_bound) < gamma:
        return np.arange(n), full_bound, None
    minimum = float(entropies.min())
    count = n
    if minimum > 0 and gamma/minimum < n-2:
        # Please retain one extra candidate to certify that the next prefix fails.
        count = min(n, int(gamma/minimum)+2)
    scores = -entropies if policy == 'entropy' else ordering_scores(rows, vocab, policy)
    prefix = top_confidence(scores, tie_ranks, count)
    prefix = prefix[np.lexsort((tie_ranks[prefix], -scores[prefix]))]
    ordered = entropies[prefix]
    bounds = np.cumsum(ordered)-np.maximum.accumulate(ordered)
    size = int(np.searchsorted(bounds, gamma, side='right'))
    if size == len(prefix) and len(prefix) == n:
        return prefix, float(bounds[-1]), None
    if size < 1 or size == len(prefix):
        raise AssertionError('Please retain a failing next prefix unless all rows fit.')
    return prefix[:size], float(bounds[size-1]), float(bounds[size])


def sample(oracle, order_seed, commit_seed, policy, recorder, *, batches=None,
           gamma=None, observer=None):
    """Use one current-history query per commit, with no graph access or remasking.

    Fixed-count controls use the existing balanced schedule. EB has no imposed
    batch count: please report its realized query count instead of treating gamma
    as a query budget. Position selection precedes the draws of token values.
    """
    adaptive = gamma is not None
    if adaptive:
        if batches is not None or policy not in ORDERINGS or not np.isfinite(gamma) or gamma < 0:
            raise ValueError('Please specify only a finite nonnegative EB entropy budget.')
    elif (policy not in ('random', *ORDERINGS) or not isinstance(batches, int)
          or not 1 <= batches <= oracle.n):
        raise ValueError('Please specify a valid fixed batch count and ordering.')
    history = np.full(oracle.n, -1, dtype=np.int64)
    rng = np.random.default_rng(commit_seed)
    order_rng = np.random.default_rng(order_seed)
    if policy == 'random':
        schedule = balanced_batches(oracle.n, batches, order_rng)
    else:
        order = order_rng.permutation(oracle.n)
        ranks = np.empty(oracle.n, dtype=np.int64)
        ranks[order] = np.arange(oracle.n)
    if not adaptive:
        small, extra = divmod(oracle.n, batches)
    bounds, next_bounds, sizes = [], [], []
    step, remaining = 0, oracle.n
    while remaining:
        if policy == 'random':
            batch = schedule[step]
            readouts = batch
            replies = used = oracle.submit(history, batch, 'commit')
        else:
            readouts = np.flatnonzero(history < 0)
            replies = oracle.submit(history, readouts, 'commit')
            if adaptive:
                selected, bound, following = entropy_bounded_selection(
                    replies, oracle.vocab, ranks[readouts], policy, gamma)
                bounds.append(bound)
                next_bounds.append(np.nan if following is None else following)
            else:
                selected = top_confidence(ordering_scores(replies, oracle.vocab, policy),
                                          ranks[readouts], small+(step < extra))
            # Please preserve the existing mapping from value RNG draws to indices.
            selected = selected[np.argsort(readouts[selected])]
            batch, used = readouts[selected], replies[selected]
        if observer is not None:
            observer(history, readouts, replies, batch)
        values = (rng.random(len(batch))[:, None] > used[:, :2].cumsum(axis=-1)).sum(axis=-1)
        tail = values == 2
        values[tail] = rng.integers(2, oracle.vocab, size=int(tail.sum()))
        recorder(batch, used, values)
        history[batch] = values
        sizes.append(len(batch))
        step += 1
        remaining -= len(batch)
    return history, {'batch_sizes': np.asarray(sizes, dtype=np.int64),
                     'entropy_bounds': np.asarray(bounds),
                     'next_entropy_bounds': np.asarray(next_bounds)}
