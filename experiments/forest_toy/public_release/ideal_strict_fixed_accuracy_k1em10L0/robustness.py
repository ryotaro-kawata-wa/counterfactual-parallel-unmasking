"""Terminal-only bidirectional filtering and cycle-rank repair ablations.

Please retain the recorded controller in cycle_repair.py as the reference.
This module changes only terminal edge acceptance and singleton selection.
"""

from dataclasses import asdict
from types import SimpleNamespace

import numpy as np

from cycle_repair import RepairTrace, graph_inspection, remove_vertices, rows_digest
from deferred_screen import packed_screen
from toy import centroid_batch, preprocess


VARIANTS = ('union_degree', 'mutual_degree', 'union_rank', 'mutual_rank')


class ScreenCapture:
    """Retain the final raw votes without altering the screen or its observer."""

    def __init__(self, observer=None):
        self.observer, self.votes = observer, None

    def __getattr__(self, name):
        if self.observer is None:
            return lambda *args, **kwargs: None
        return getattr(self.observer, name)

    def start_screen(self, history, draft, columns):
        self.votes = None
        if self.observer is not None:
            self.observer.start_screen(history, draft, columns)

    def observe_prefix(self, completed, total, votes):
        if completed == total:
            self.votes = votes
        if self.observer is not None:
            self.observer.observe_prefix(completed, total, votes)


def mutual_filter(graph, votes):
    """Only remove union edges; raw reverse support may come from discarded rows."""
    filtered = {u: set() for u in graph}
    if votes is None:
        if any(graph.values()):
            raise AssertionError('Please retain raw votes for every nonempty terminal graph.')
        return filtered
    masks = {u: votes.majority_mask(u) for u in graph}
    for u, neighbors in graph.items():
        for v in neighbors:
            if u < v and ((masks[u] >> v) & 1) and ((masks[v] >> u) & 1):
                filtered[u].add(v)
                filtered[v].add(u)
    return filtered


def cycle_rank_gains(graph):
    """Compute beta(G)-beta(G-v) for all vertices in one articulation DFS.

    For v in its connected component H, the gain is deg(v)-c(H-v).
    Please count articulation pieces, so bridge attachments do not inflate gain.
    An iterative traversal also supports paths longer than Python's stack limit.
    """
    discovery, low, parent, children, separated = {}, {}, {}, {}, {}
    for root in graph:
        if root in discovery:
            continue
        parent[root] = None
        discovery[root] = low[root] = len(discovery)
        children[root] = separated[root] = 0
        stack = [(root, iter(graph[root]))]
        while stack:
            u, neighbors = stack[-1]
            v = next(neighbors, None)
            if v is None:
                stack.pop()
                p = parent[u]
                if p is not None:
                    low[p] = min(low[p], low[u])
                    if low[u] >= discovery[p]:
                        separated[p] += 1
                continue
            if v == parent[u]:
                continue
            if v not in discovery:
                parent[v] = u
                children[u] += 1
                discovery[v] = low[v] = len(discovery)
                children[v] = separated[v] = 0
                stack.append((v, iter(graph[v])))
            else:
                low[u] = min(low[u], discovery[v])
    return {u: len(graph[u])-(children[u] if parent[u] is None else 1+separated[u])
            for u in graph}


def true_edges(oracle):
    """Please call only in post-run diagnostics, never in sampling decisions."""
    if hasattr(oracle, 'edges'):
        return {tuple(sorted(map(int, edge))) for edge in oracle.edges}
    return {tuple(sorted((int(u), int(oracle.root_of[u])))) for u in np.flatnonzero(oracle.leaf)}


def edge_diagnostics(graph, truth):
    residual = set(graph)
    local_truth = {(u, v) for u, v in truth if u in residual and v in residual}
    estimated = {(u, v) for u, vs in graph.items() for v in vs if u < v}
    stats, _ = graph_inspection(graph)
    return {**stats, 'true_edges': len(local_truth), 'retained_true_edges': len(estimated & local_truth),
            'missing_edges': len(local_truth-estimated), 'extra_edges': len(estimated-local_truth),
            'precision': len(estimated & local_truth)/len(estimated) if estimated else None,
            'recall': len(estimated & local_truth)/len(local_truth) if local_truth else None}


class RobustTrace(RepairTrace):
    def __init__(self):
        super().__init__()
        self.union_graph = None
        self.prefix = None

    def before_filter(self, graph, rows, history, cost):
        self.union_graph = {u: set(vs) for u, vs in graph.items()}
        self.prefix = {'rows_sha256': rows_digest(rows), 'graph_sha256': rows_digest(graph),
                       'history': history.copy(), 'cost': asdict(cost), 'total': cost.total}

    def posthoc(self, oracle):
        # Please adapt only the passive legacy scorer; the sampler sees no parent array.
        adapter = oracle
        if hasattr(oracle, 'edges'):
            adapter = SimpleNamespace(leaf=oracle.parent >= 0,
                                      root_of=np.where(oracle.parent >= 0, oracle.parent, np.arange(oracle.n)))
        result = super().posthoc(adapter)
        if self.union_graph is None:
            return result
        import hashlib
        truth = true_edges(oracle)
        before, after = edge_diagnostics(self.union_graph, truth), edge_diagnostics(self.initial_graph, truth)
        result.update({'before_filter': before, 'after_filter': after,
                       'filter_removed_true_edges': before['retained_true_edges']-after['retained_true_edges'],
                       'filter_removed_false_edges': before['extra_edges']-after['extra_edges'],
                       'filter_extra_queries': 0,
                       'prefix': {k: v for k, v in self.prefix.items() if k != 'history'}})
        result['prefix']['history_sha256'] = hashlib.sha256(self.prefix['history'].astype('<i4').tobytes()).hexdigest()
        return result

    def save_snapshot(self, path, oracle):
        """Archive a preselected seed's graphs only after its decisions are complete."""
        if self.union_graph is None:
            return
        def edges(graph):
            return np.asarray(sorted((u, v) for u, vs in graph.items() for v in vs if u < v),
                              dtype=np.int64).reshape(-1, 2)
        path.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(path, residual=np.asarray(sorted(self.union_graph)),
                            union_edges=edges(self.union_graph), filtered_edges=edges(self.initial_graph),
                            true_edges=np.asarray(sorted(true_edges(oracle)), dtype=np.int64).reshape(-1, 2),
                            repair_vertices=np.asarray([s['vertex'] for s in self.steps], dtype=np.int64),
                            terminal_history=self.prefix['history'])


def sample_robust(oracle, params, controller_seed, commit_seed, observer=None,
                  commit_session=None, commit_observer=None, variant='union_degree', repair_trace=None):
    """Preserve preprocessing, screen, peeling, commit draws, and both existing caps."""
    if variant not in VARIANTS:
        raise ValueError('Please choose one of the four frozen ablation variants.')
    trace = RobustTrace() if repair_trace is None else repair_trace
    capture = ScreenCapture(observer)
    rng, commit_rng = np.random.default_rng(controller_seed), np.random.default_rng(commit_seed)
    draft, columns, threshold, maximum = preprocess(oracle, params)
    history = np.full(params.n, -1, dtype=np.int64) if commit_session is None else commit_session.history
    if len(history) != params.n or np.any(history >= 0):
        raise ValueError('Please start with an empty commit history.')
    screens, batches, screen_costs, fallback = [], [], [], None

    def commit(batch, role):
        batch = np.array(sorted(batch), dtype=np.int64)
        if not len(batch) or np.any(history[batch] >= 0):
            raise ValueError('Please commit a nonempty, previously uncommitted batch.')
        rows = (oracle.submit(history, batch, 'commit') if commit_session is None
                else commit_session.submit(batch))
        values = (commit_rng.random(len(batch))[:, None] > rows[:, :2].cumsum(axis=-1)).sum(axis=-1)
        tail = values == 2
        values[tail] = commit_rng.integers(2, params.vocab, size=int(tail.sum()))
        if commit_session is None:
            history[batch] = values
        else:
            commit_session.append(batch, values)
        if commit_observer is not None:
            commit_observer(batch, rows, values)
        batches.append(batch.tolist())
        trace.roles[role] += 1

    for phase in range(params.screen_cap):
        if np.all(history >= 0):
            break
        before = (oracle.cost.counterfactual, oracle.cost.nominal_counterfactual, oracle.cost.returned_rows)
        rows = packed_screen(oracle, params, history, draft, columns, rng, observer=capture)
        screen_costs.append({'counterfactual': oracle.cost.counterfactual-before[0],
                             'nominal_counterfactual': oracle.cost.nominal_counterfactual-before[1],
                             'returned_rows': oracle.cost.returned_rows-before[2]})
        claims = np.zeros(params.n, dtype=np.int64)
        for neighbors in rows.values():
            for v in neighbors:
                claims[v] += 1
        peel = np.flatnonzero((history < 0) & (claims > params.d/2)).tolist()
        screens.append({'rows': rows, 'peel': peel})
        capture.observe_controller(peel, claims, phase)
        if not peel or phase == params.peel_cap:
            graph = {j: set() for j in rows}
            for j, neighbors in rows.items():
                for i in neighbors:
                    graph[j].add(i)
                    graph[i].add(j)
            trace.before_filter(graph, rows, history, oracle.cost)
            if variant.startswith('mutual'):
                graph = mutual_filter(graph, capture.votes)
            # Please release the dense vote cache before terminal graph traversal.
            capture.votes = None
            stats, cyclic = graph_inspection(graph)
            trace.start(graph, rows, history, oracle.cost, stats)
            while graph:
                if cyclic:
                    if len(batches) == params.round_cap-1:
                        fallback = trace.terminal_fallback = 'round_cap'
                        commit(np.flatnonzero(history < 0), 'fallback')
                        graph.clear()
                        break
                    gains = cycle_rank_gains(graph) if variant.endswith('rank') else None
                    v = min(cyclic, key=lambda u: (-(gains[u] if gains is not None else 0), -len(graph[u]), u))
                    trace.pending = {'vertex': int(v), 'degree_before': len(graph[v]),
                                     'cycle_rank_before': stats['cycle_rank'], 'total_before': oracle.cost.total,
                                     'rounds_before': oracle.cost.rounds,
                                     'predicted_rank_decrease': gains[v] if gains is not None else None}
                    commit([v], 'repair')
                    remove_vertices(graph, [v])
                    next_stats, cyclic = graph_inspection(graph)
                    decrease = stats['cycle_rank']-next_stats['cycle_rank']
                    if decrease <= 0 or (gains is not None and decrease != gains[v]):
                        raise AssertionError('A cycle repair must achieve its positive rank decrease.')
                    trace.steps.append({**trace.pending, 'cycle_rank_after': next_stats['cycle_rank'],
                                        'total_after': oracle.cost.total, 'rounds_after': oracle.cost.rounds})
                    trace.pending, stats = None, next_stats
                    continue
                batch = centroid_batch(graph)
                if batch is None or len(batches) == params.round_cap-1:
                    fallback = trace.terminal_fallback = 'nonforest' if batch is None else 'round_cap'
                    commit(np.flatnonzero(history < 0), 'fallback')
                    graph.clear()
                    break
                trace.forest_transition(stats, oracle.cost)
                commit(batch, 'centroid')
                remove_vertices(graph, batch)
            break
        for v in peel:
            if len(batches) == params.round_cap-1:
                fallback = trace.terminal_fallback = 'round_cap'
                commit(np.flatnonzero(history < 0), 'fallback')
                break
            commit([v], 'peel')
    if np.any(history < 0):
        raise AssertionError('The controller did not finish its assignment.')
    return {'sample': history, 'screens': screens, 'batches': batches, 'fallback': fallback,
            'threshold': threshold, 'bank_size': maximum, 'screen_costs': screen_costs}
