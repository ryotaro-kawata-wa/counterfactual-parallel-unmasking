"""Separate terminal-repair controller; the recorded manuscript sampler is unchanged.

Please use only the public estimated graph to choose repair vertices. Hidden
target edges are inspected by RepairTrace.posthoc() after sampling has stopped.
"""

from collections import Counter
from dataclasses import asdict
import hashlib
import json

import numpy as np

from toy import centroid_batch, packed_screen, preprocess


VARIANTS = ('original', 'single_max_degree')


def graph_inspection(graph):
    """Find actual cycle vertices with iterative bridge detection, not the 2-core.

    A bridge path between two cycles also survives 2-core pruning. Please exclude
    its internal vertices: deleting one need not decrease the cycle rank.
    """
    discovery, low, parent, bridges = {}, {}, {}, set()
    components = largest = 0
    for root in graph:
        if root in discovery:
            continue
        components += 1
        size = 1
        discovery[root] = low[root] = len(discovery)
        parent[root] = None
        stack = [(root, iter(graph[root]))]
        while stack:
            u, neighbors = stack[-1]
            v = next(neighbors, None)
            if v is None:
                stack.pop()
                p = parent[u]
                if p is not None:
                    low[p] = min(low[p], low[u])
                    if low[u] > discovery[p]:
                        bridges.add((min(u, p), max(u, p)))
                continue
            if v == u or v not in graph:
                raise ValueError('Please provide a simple graph on its declared vertices.')
            if v == parent[u]:
                continue
            if v not in discovery:
                discovery[v] = low[v] = len(discovery)
                parent[v] = u
                size += 1
                stack.append((v, iter(graph[v])))
            else:
                low[u] = min(low[u], discovery[v])
        largest = max(largest, size)
    edges, cyclic = 0, set()
    for u, neighbors in graph.items():
        for v in neighbors:
            if u not in graph[v]:
                raise ValueError('Please provide symmetric undirected adjacency.')
            if u < v:
                edges += 1
                if (u, v) not in bridges:
                    cyclic.update((u, v))
    stats = {'vertices': len(graph), 'edges': edges, 'components': components,
             'cycle_rank': edges-len(graph)+components, 'largest_component': largest,
             'cycle_vertices': len(cyclic)}
    assert (stats['cycle_rank'] == 0) == (not cyclic)
    return stats, cyclic


def remove_vertices(graph, batch):
    for u in batch:
        for v in graph[u]:
            graph[v].remove(u)
        del graph[u]


def rows_digest(rows):
    payload = [[int(u), sorted(map(int, rows[u]))] for u in sorted(rows)]
    return hashlib.sha256(json.dumps(payload, separators=(',', ':')).encode()).hexdigest()


class RepairTrace:
    """Passive public snapshots and successful-commit records survive censoring."""

    def __init__(self):
        self.initial_graph = None
        self.initial = None
        self.transition = None
        self.steps = []
        self.roles = Counter()
        self.pending = None
        self.terminal_fallback = None

    def start(self, graph, rows, history, cost, stats):
        self.initial_graph = {u: set(vs) for u, vs in graph.items()}
        self.initial = {**stats, 'cost': asdict(cost), 'total': cost.total,
                        'history_sha256': hashlib.sha256(history.astype('<i4').tobytes()).hexdigest(),
                        'rows_sha256': rows_digest(rows), 'graph_sha256': rows_digest(graph)}

    def forest_transition(self, stats, cost):
        if self.transition is None:
            self.transition = {**stats, 'cost': asdict(cost), 'total': cost.total}

    def posthoc(self, oracle):
        """Please call after sampling, including after a refused budget submission."""
        output = {'initial': self.initial, 'transition': self.transition,
                  'steps': self.steps, 'pending': self.pending, 'roles': dict(self.roles),
                  'repair_tokens': len(self.steps), 'repair_invoked': bool(self.steps or self.pending),
                  'terminal_fallback': self.terminal_fallback}
        if self.initial_graph is None:
            return output
        graph = self.initial_graph
        residual = set(graph)
        true_edges = {(min(int(u), int(oracle.root_of[u])), max(int(u), int(oracle.root_of[u])))
                      for u in np.flatnonzero(oracle.leaf)
                      if int(u) in residual and int(oracle.root_of[u]) in residual}
        estimated = {(u, v) for u, vs in graph.items() for v in vs if u < v}
        missing, extra = true_edges-estimated, estimated-true_edges
        truth_neighbors = {u: set() for u in residual}
        missing_neighbors = {u: set() for u in residual}
        extra_neighbors = {u: set() for u in residual}
        for edges, adjacency in ((true_edges, truth_neighbors), (missing, missing_neighbors),
                                 (extra, extra_neighbors)):
            for u, v in edges:
                adjacency[u].add(v)
                adjacency[v].add(u)
        truth_count, missing_count, extra_count = len(true_edges), len(missing), len(extra)
        output['initial'] = {**self.initial, 'true_edges': truth_count,
                             'missing_edges': missing_count, 'extra_edges': extra_count}
        enriched = []
        for step in self.steps:
            v = step['vertex']
            truth_removed = len(truth_neighbors[v] & residual)
            missing_removed = len(missing_neighbors[v] & residual)
            extra_removed = len(extra_neighbors[v] & residual)
            residual.remove(v)
            truth_count -= truth_removed
            missing_count -= missing_removed
            extra_count -= extra_removed
            enriched.append({**step, 'true_degree_before': truth_removed,
                             'removed_missing_edges': missing_removed, 'removed_extra_edges': extra_removed,
                             'missing_edges_after': missing_count, 'extra_edges_after': extra_count})
        output['steps'] = enriched
        if self.transition is not None:
            output['transition'] = {**self.transition, 'true_edges': truth_count,
                                    'missing_edges': missing_count, 'extra_edges': extra_count,
                                    'contains_true_forest': missing_count == 0}
        output['after_completed_repairs'] = {'vertices': len(residual), 'true_edges': truth_count,
                                             'missing_edges': missing_count, 'extra_edges': extra_count}
        return output


def sample_variant(oracle, params, controller_seed, commit_seed, observer=None,
                   commit_session=None, commit_observer=None, variant='single_max_degree',
                   repair_trace=None):
    """Keep the original screen/peeling/draw order; vary only terminal nonforest handling.

    The original round cap remains in force, including before a repair commit.
    An optional BudgetOracle independently enforces the experiment's total-Q cap.
    """
    if variant not in VARIANTS:
        raise ValueError('Please choose an explicitly named terminal policy.')
    trace = RepairTrace() if repair_trace is None else repair_trace
    rng, commit_rng = np.random.default_rng(controller_seed), np.random.default_rng(commit_seed)
    draft, columns, threshold, maximum = preprocess(oracle, params)
    history = (np.full(params.n, -1, dtype=np.int64) if commit_session is None else commit_session.history)
    if len(history) != params.n or np.any(history >= 0):
        raise ValueError('Please start with an empty commit history of the requested length.')
    screens, batches, screen_costs, fallback = [], [], [], None

    def commit(batch, role):
        batch = np.array(sorted(batch), dtype=np.int64)
        if not len(batch) or np.any(history[batch] >= 0):
            raise ValueError('Please commit a nonempty, previously uncommitted batch.')
        rows = (oracle.submit(history, batch, 'commit') if commit_session is None
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
        trace.roles[role] += 1

    for phase in range(params.screen_cap):
        if np.all(history >= 0):
            break
        before = (oracle.cost.counterfactual, oracle.cost.nominal_counterfactual, oracle.cost.returned_rows)
        rows = packed_screen(oracle, params, history, draft, columns, rng, observer=observer)
        screen_costs.append({'counterfactual': oracle.cost.counterfactual-before[0],
                             'nominal_counterfactual': oracle.cost.nominal_counterfactual-before[1],
                             'returned_rows': oracle.cost.returned_rows-before[2]})
        claims = np.zeros(params.n, dtype=np.int64)
        for neighbors in rows.values():
            for v in neighbors:
                claims[v] += 1
        peel = np.flatnonzero((history < 0) & (claims > params.d/2)).tolist()
        screens.append({'rows': rows, 'peel': peel})
        if observer is not None:
            observer.observe_controller(peel, claims, phase)
        if not peel or phase == params.peel_cap:
            graph = {j: set() for j in rows}
            for j, neighbors in rows.items():
                for i in neighbors:
                    graph[j].add(i)
                    graph[i].add(j)
            stats, cyclic = graph_inspection(graph)
            trace.start(graph, rows, history, oracle.cost, stats)
            while graph:
                if variant == 'single_max_degree' and cyclic:
                    if len(batches) == params.round_cap-1:
                        fallback = 'round_cap'
                        trace.terminal_fallback = fallback
                        commit(np.flatnonzero(history < 0), 'fallback')
                        graph.clear()
                        break
                    v = min(cyclic, key=lambda u: (-len(graph[u]), u))
                    trace.pending = {'vertex': int(v), 'degree_before': len(graph[v]),
                                     'cycle_rank_before': stats['cycle_rank'],
                                     'total_before': oracle.cost.total, 'rounds_before': oracle.cost.rounds}
                    commit([v], 'repair')
                    remove_vertices(graph, [v])
                    next_stats, cyclic = graph_inspection(graph)
                    if next_stats['cycle_rank'] >= stats['cycle_rank']:
                        raise AssertionError('A cycle-vertex repair must decrease the cycle rank.')
                    trace.steps.append({**trace.pending, 'cycle_rank_after': next_stats['cycle_rank'],
                                        'total_after': oracle.cost.total, 'rounds_after': oracle.cost.rounds})
                    trace.pending = None
                    stats = next_stats
                    continue
                batch = centroid_batch(graph)
                if batch is None or len(batches) == params.round_cap-1:
                    fallback = 'nonforest' if batch is None else 'round_cap'
                    trace.terminal_fallback = fallback
                    commit(np.flatnonzero(history < 0), 'fallback')
                    graph.clear()
                    break
                trace.forest_transition(stats, oracle.cost)
                commit(batch, 'centroid')
                remove_vertices(graph, batch)
            break
        for v in peel:
            if len(batches) == params.round_cap-1:
                fallback = 'round_cap'
                trace.terminal_fallback = fallback
                commit(np.flatnonzero(history < 0), 'fallback')
                break
            commit([v], 'peel')
    if np.any(history < 0):
        raise AssertionError('The controller did not finish its assignment.')
    return {'sample': history, 'screens': screens, 'batches': batches, 'fallback': fallback,
            'threshold': threshold, 'bank_size': maximum, 'screen_costs': screen_costs}
