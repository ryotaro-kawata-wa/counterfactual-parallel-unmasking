"""Stop the unchanged controller before a required submission exceeds its budget."""

from collections import Counter

import numpy as np

from explore import ExplorationObserver
from tradeoff_core import CommitCursor


class QueryBudgetExceeded(Exception):
    """A censored run has no completed sample and therefore no full-density score."""

    def __init__(self, spent, required, limit, stage):
        self.details = {"spent": spent, "next_submission_queries": required,
                        "limit": limit, "stage": stage,
                        "completion_query_lower_bound": spent + required}
        super().__init__(f"{stage}: {spent} + {required} exceeds {limit}")


class BudgetOracle:
    """Please count distinct public input states before evaluating their replies.

    A packed family is admitted as a whole. Refusing it can leave fewer than
    2*p-1 queries unused in this experiment. The spent count is never rounded
    up to N, and incomplete replies are never passed to the decoder.
    """

    def __init__(self, oracle, limit):
        if not isinstance(limit, int) or limit < 0:
            raise ValueError("Please use a nonnegative integer query limit.")
        self.oracle, self.limit = oracle, limit

    def __getattr__(self, name):
        return getattr(self.oracle, name)

    def check(self, count, stage):
        if self.cost.total + count > self.limit:
            raise QueryBudgetExceeded(self.cost.total, count, self.limit, stage)

    def submit(self, state, readouts, kind):
        self.check(1, kind)
        return self.oracle.submit(state, readouts, kind)

    def submit_chunk_family(self, prepared, chunk, sources):
        columns, codes = prepared[3], prepared[-1]
        count = (len(columns) * len(sources) if codes is None
                 else len(np.unique(codes[:, sources])))
        self.check(count, "counterfactual")
        before = self.cost.total
        rows = self.oracle.submit_chunk_family(prepared, chunk, sources)
        if self.cost.total - before != count:
            raise AssertionError("The public-input budget check disagrees with the oracle meter.")
        return rows


class BudgetCommitCursor(CommitCursor):
    def submit(self, readouts):
        # Please guard this fast path too: it does not call oracle.submit().
        self.oracle.check(1, "commit")
        return super().submit(readouts)


class BudgetObserver(ExplorationObserver):
    """Retain completed screens and progress, including when sampling is interrupted."""

    def __init__(self, params, oracle):
        super().__init__(params)
        self.oracle = oracle
        self.decoded = []

    def start_screen(self, history, draft, columns):
        super().start_screen(history, draft, columns)
        self.current.update({"complete": False, "completed_colorings": 0,
                             "counterfactual_at_start": self.oracle.cost.counterfactual})

    def observe_prefix(self, completed, total, votes):
        self.current["completed_colorings"] = completed
        super().observe_prefix(completed, total, votes)

    def finish_screen(self, rows):
        super().finish_screen(rows)
        self.current["complete"] = True
        self.decoded.append({"rows": rows, "peel": []})

    def observe_controller(self, peel, claims, phase):
        super().observe_controller(peel, claims, phase)
        self.decoded[-1]["peel"] = list(peel)

    def finish_observation(self, oracle):
        """Please inspect hidden edges only after the controller has stopped."""
        if hasattr(oracle, "adjacency"):
            adjacency = oracle.adjacency
        else:
            adjacency = [[] for _ in range(oracle.n)]
            for u in np.flatnonzero(oracle.leaf):
                v = int(oracle.root_of[u])
                adjacency[int(u)].append(v)
                adjacency[v].append(int(u))
        for i, screen in enumerate(self.screens):
            end = (self.screens[i+1]["counterfactual_at_start"]
                   if i+1 < len(self.screens) else oracle.cost.counterfactual)
            screen["counterfactual"] = end - screen["counterfactual_at_start"]
            if not screen["complete"]:
                continue
            decoded = self.decoded[i]
            residual = set(decoded["rows"])
            truth = {u: set(adjacency[u]) & residual for u in residual}
            screen.update({
                "posthoc_true_edges": sum(map(len, truth.values())) // 2,
                "posthoc_low_degree_row_errors": sum(neighbors != decoded["rows"][u]
                    for u, neighbors in truth.items() if len(neighbors) <= self.params.d),
                "posthoc_peel_degree_le_half_d": sum(len(truth[u]) <= self.params.d/2 for u in decoded["peel"]),
                "posthoc_peel_degree_gt_half_d": sum(len(truth[u]) > self.params.d/2 for u in decoded["peel"]),
                "posthoc_unpeeled_degree_gt_d": sum(len(neighbors) > self.params.d and u not in decoded["peel"]
                    for u, neighbors in truth.items()),
            })


class CommitTrace:
    """A passive wrapper; it neither changes batches nor draws random numbers."""

    def __init__(self, recorder, n):
        self.recorder = recorder
        self.history = np.full(n, -1, dtype=np.int64)
        self.batches = []

    def __call__(self, batch, rows, values):
        self.recorder(batch, rows, values)
        self.history[batch] = values
        self.batches.append(batch.tolist())

    def histogram(self):
        return {str(k): v for k, v in sorted(Counter(map(len, self.batches)).items())}
