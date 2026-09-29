"""Isolated row-overflow and initial-draft variants for paired experiments.

Please keep the legacy sampler unchanged. These worker-local contexts restore
every replaced interface on exit, including when a query budget interrupts a run.
"""
from contextlib import contextmanager
import hashlib

import numpy as np

import deferred_screen
import explore_minimal as base
import robustness
from draft_policy import draft_policy
from tune import RunObserver


def population(bits):
    """Please support the existing Python 3.9 environment as well."""
    return bin(bits).count('1')


def vote_planes(votes, readout):
    """Recover exact public vote counts without evaluating any oracle state."""
    planes = [0]*votes.count.bit_length()
    for pattern, masks in zip(votes.patterns[readout], votes.group_masks):
        pattern, voters = int(pattern), 0
        while pattern:
            low = pattern & -pattern
            voters |= masks[low.bit_length()-1]
            pattern ^= low
        for bit in range(len(planes)):
            if not voters:
                break
            old = planes[bit]
            planes[bit] = old ^ voters
            voters &= old
    return planes


def highest_votes(candidates, planes, count):
    """Choose the highest counts; please break equal counts by ascending index."""
    selected, remaining = 0, candidates
    for plane in reversed(planes):
        high = remaining & plane
        size = population(high)
        if size >= count:
            remaining = high
        else:
            selected |= high
            count -= size
            remaining &= ~plane
        if count == 0:
            return selected
    while count:
        low = remaining & -remaining
        if not low:
            raise AssertionError('Please request no more than the available candidates.')
        selected |= low
        remaining ^= low
        count -= 1
    return selected


def indices(bits):
    result = set()
    while bits:
        low = bits & -bits
        result.add(low.bit_length()-1)
        bits ^= low
    return result


@contextmanager
def row_cap_policy(policy):
    """Only overflow handling changes; please preserve all rows of size <= d."""
    if policy not in ('discard', 'top_votes'):
        raise ValueError('Please choose discard or top_votes.')
    original_votes, original_observer = deferred_screen.DeferredVotes, base.WeightedObserver
    capture = []

    class CapturedVotes(original_votes):
        def __init__(self, n, count):
            super().__init__(n, count)
            self.returned = {}
            capture.append(self)

        def row(self, readout, cutoff):
            candidates = self.majority_mask(readout)
            if population(candidates) <= cutoff:
                selected = candidates
            elif policy == 'discard':
                selected = 0
            else:
                selected = highest_votes(candidates, vote_planes(self, readout), cutoff)
            result = indices(selected)
            self.returned[readout] = result
            return result

    class CappedObserver(original_observer):
        def finish_screen(self, rows):
            if policy == 'discard':
                super().finish_screen(rows)
            else:
                # Please retain the original public diagnostics, adapting only
                # the assertion that previously assumed every overflow was empty.
                RunObserver.finish_screen(self, rows)
                assert self._raw_counts is not None and set(rows) == set(self._raw_counts)
                for j, neighbors in rows.items():
                    assert len(neighbors) == min(self._raw_counts[j], self.params.d)
                assert self.current['empty_decoded_rows'] == self.current['raw_empty_rows']
                self.current['complete'] = True
                self.decoded.append({'rows': rows, 'peel': []})
            self.current.update(row_cap_policy=policy,
                overflow_rows=self.current['truncated_rows'],
                overflow_rows_discarded=self.current['truncated_rows'] if policy == 'discard' else 0,
                overflow_rows_retained=self.current['truncated_rows'] if policy == 'top_votes' else 0)

    deferred_screen.DeferredVotes, base.WeightedObserver = CapturedVotes, CappedObserver
    try:
        yield capture
    finally:
        deferred_screen.DeferredVotes, base.WeightedObserver = original_votes, original_observer


def draft_seed(target, n, repeat):
    """Use a separate public random source, shared across parameter settings."""
    payload = f'row-cap-study/initial-product-draft/v1/{target}/{n}/{repeat}'.encode()
    return int.from_bytes(hashlib.sha256(payload).digest()[:8], 'little')


@contextmanager
def initial_draft(policy, seed):
    """Sample temporary values from preprocessing; please do not commit them."""
    if policy != 'initial_sample':
        with draft_policy(policy) as capture:
            yield capture
        return
    with draft_policy('argmax') as capture:
        original = robustness.preprocess

        def sampled(oracle, params):
            old_draft, old_columns, threshold, maximum = original(oracle, params)
            rows, sizes = capture['initial_rows'], capture['bank_sizes']
            rng = np.random.default_rng(seed)
            draft = (rng.random(params.n)[:, None] > rows[:, :2].cumsum(axis=1)).sum(axis=1)
            tail = draft == 2
            draft[tail] = rng.integers(2, params.vocab, size=int(tail.sum()))
            columns = old_columns.copy()
            for k in range(maximum):
                padding = sizes <= k
                columns[k, padding] = draft[padding]
            capture.update(policy=policy, draft=draft, columns=columns,
                           changed_positions=int(np.count_nonzero(draft != old_draft)))
            return draft, columns, threshold, maximum

        robustness.preprocess = sampled
        try:
            yield capture
        finally:
            robustness.preprocess = original


def save_votes(capture, output, job_name):
    """Save public screen observations for independent, zero-query decoder audits."""
    records = []
    for index, votes in enumerate(capture):
        colors = np.full((len(votes.group_masks), votes.n), 255, dtype=np.uint8)
        for t, masks in enumerate(votes.group_masks):
            for color, mask in enumerate(masks):
                packed = np.frombuffer(mask.to_bytes((votes.n+7)//8, 'little'), dtype=np.uint8)
                members = np.unpackbits(packed, bitorder='little')[:votes.n].astype(bool)
                colors[t, members] = color
        readouts = sorted(votes.returned)
        neighbors = [sorted(votes.returned[j]) for j in readouts]
        path = output/'votes'/f'{job_name}_screen{index}.npz'
        path.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(path, patterns=votes.patterns, colors=colors,
            readouts=np.asarray(readouts, dtype=np.int64),
            indptr=np.asarray([0, *np.cumsum(list(map(len, neighbors)))], dtype=np.int64),
            indices=np.asarray([v for row in neighbors for v in row], dtype=np.int64))
        raw_hash = hashlib.sha256(votes.patterns.astype('<u4').tobytes()+colors.tobytes()).hexdigest()
        records.append({'screen': index, 'started_colorings': len(votes.group_masks),
            'decoded_rows': len(readouts), 'raw_votes_sha256': raw_hash,
            'snapshot': str(path.relative_to(output)), 'additional_queries': 0})
    return records
