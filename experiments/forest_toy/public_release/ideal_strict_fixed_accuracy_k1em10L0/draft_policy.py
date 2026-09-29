"""Choose a public, screen-fixed draft without deleting bank or tail probes."""
from contextlib import contextmanager
import hashlib

import numpy as np

import robustness


POLICIES = ('argmax', 'first_bank')


def array_digest(values):
    return hashlib.sha256(np.asarray(values).astype('<i8').tobytes()).hexdigest()


@contextmanager
def draft_policy(policy):
    """Please use this isolated context within a single experiment worker.

    Only the existing preprocessing reply is read. The selected draft is fixed
    before the sampler draws any coloring and is reused across its screens.
    """
    if policy not in POLICIES:
        raise ValueError('Please choose argmax or first_bank.')
    original = robustness.preprocess
    capture = {}

    def changed(oracle, params):
        replies = []

        class PublicReplyCapture:
            def __getattr__(self, name):
                return getattr(oracle, name)

            def submit(self, state, readouts, kind):
                reply = oracle.submit(state, readouts, kind)
                if kind == 'preprocessing':
                    replies.append(np.array(reply, copy=True))
                return reply

        old_draft, old_columns, threshold, maximum = original(PublicReplyCapture(), params)
        assert len(replies) == 1
        rows = replies[0]
        cut = threshold-params.eps
        sizes = (rows[:, :2] >= cut).sum(axis=1)
        sizes += (params.vocab-2)*(rows[:, 2]/(params.vocab-2) >= cut)
        assert int(sizes.max()) == maximum
        draft, columns = old_draft.copy(), old_columns.copy()
        if policy == 'first_bank' and maximum:
            # The first column already uses the public argmax at empty banks.
            draft = old_columns[0].copy()
            # Please update only padding; every actual bank and tail value stays.
            for k in range(maximum):
                padding = sizes <= k
                columns[k, padding] = draft[padding]
            np.testing.assert_array_equal(columns[0], draft)
        capture.update(policy=policy, threshold=float(threshold), maximum_bank=int(maximum),
                       column_count=len(columns) if maximum else 0,
                       changed_positions=int(np.count_nonzero(draft != old_draft)),
                       bank_sizes=sizes, initial_rows=rows, draft=draft,
                       columns=columns, argmax_draft=old_draft, argmax_columns=old_columns)
        return draft, columns, threshold, maximum

    robustness.preprocess = changed
    try:
        yield capture
    finally:
        robustness.preprocess = original


def save_capture(capture, output, job_name):
    snapshot = output/'probes'/(job_name+'.npz')
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    keys = ('bank_sizes', 'initial_rows', 'draft', 'columns', 'argmax_draft', 'argmax_columns')
    np.savez_compressed(snapshot, **{k: capture[k] for k in keys})
    return {**{k: capture[k] for k in ('policy', 'threshold', 'maximum_bank', 'column_count', 'changed_positions')},
            'snapshot': str(snapshot.relative_to(output)),
            'draft_sha256': array_digest(capture['draft']),
            'columns_sha256': array_digest(capture['columns']), 'additional_queries': 0}
