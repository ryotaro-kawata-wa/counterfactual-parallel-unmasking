"""Passive strength diagnostics; hidden weights are inspected only after sampling."""

import numpy as np

from budget_core import BudgetObserver
from cycle_repair import graph_inspection, remove_vertices

LEVELS = (.1, .2, .3, .4, .5, .6, .7, .8, .9, .95, 1.)
BINS = (.1, .2, .4, .6, .8, 1.0000000001)


class WeightedObserver(BudgetObserver):
    def start_screen(self, history, draft, columns):
        super().start_screen(history, draft, columns)
        self.current['commit_round_at_start'] = self.oracle.cost.rounds


def union_graph(rows):
    graph = {u: set() for u in rows}
    for u, neighbors in rows.items():
        for v in neighbors:
            graph[u].add(v)
            graph[v].add(u)
    return graph


def graph_edges(graph):
    return {(u, v) for u, neighbors in graph.items() for v in neighbors if u < v}


def strength_counts(oracle, eligible, selected):
    """Report raw numerators and denominators; an empty denominator stays null."""
    relative = oracle.edge_strengths/oracle.theta
    selected = np.asarray(selected, dtype=bool) & eligible
    def counts(mask):
        denominator, numerator = int(mask.sum()), int((mask & selected).sum())
        return {'denominator': denominator, 'numerator': numerator,
                'fraction': numerator/denominator if denominator else None}
    total = counts(eligible)
    mass = float(oracle.edge_strengths[eligible].sum())
    captured = float(oracle.edge_strengths[selected].sum())
    return {**total, 'strength_sum': mass, 'selected_strength_sum': captured,
            'strength_fraction': captured/mass if mass else None,
            'cumulative': [{'threshold': t, **counts(eligible & (relative >= t))}
                           for t in LEVELS],
            'bins': [{'low': low, 'high': min(high, 1.),
                      **counts(eligible & (relative >= low) & (relative < high))}
                     for low, high in zip(BINS[:-1], BINS[1:])]}


def edge_stage(oracle, graph, name):
    active = np.zeros(oracle.n, dtype=bool)
    active[list(graph)] = True
    eligible = active[oracle.edges[:, 0]] & active[oracle.edges[:, 1]]
    estimated = graph_edges(graph)
    found = np.fromiter((tuple(map(int, edge)) in estimated for edge in oracle.edges),
                        dtype=bool, count=len(oracle.edges))
    stats, _ = graph_inspection(graph)
    true_found = int((eligible & found).sum())
    return {'stage': name, **stats, 'false_edges': len(estimated)-true_found,
            'precision': true_found/len(estimated) if estimated else None,
            'recall': strength_counts(oracle, eligible, found)}, eligible, found


def schedule_steps(n, batches):
    steps = np.full(n, -1, dtype=np.int64)
    for step, batch in enumerate(batches):
        if np.any(steps[batch] >= 0):
            raise AssertionError('A diagnostic schedule contains duplicate commits.')
        steps[batch] = step
    return steps


def diagnose(oracle, observer, repair, batches, snapshot_path=None):
    stages, saved = [], {}
    for index, decoded in enumerate(observer.decoded):
        graph = union_graph(decoded['rows'])
        item, _, _ = edge_stage(oracle, graph, f'screen_{index}')
        item['next_action'] = observer.screens[index]['next_action']
        stages.append(item)
        if index == 0:
            saved['screen0_edges'] = np.asarray(sorted(graph_edges(graph)), dtype=np.int64).reshape(-1, 2)
            saved['screen0_vertices'] = np.asarray(sorted(graph), dtype=np.int64)
    terminal_mask = terminal_found = None
    if repair.union_graph is not None:
        for name, graph in [('terminal_union', repair.union_graph),
                            ('terminal_filtered', repair.initial_graph)]:
            item, eligible, found = edge_stage(oracle, graph, name)
            stages.append(item)
            saved[name+'_edges'] = np.asarray(sorted(graph_edges(graph)), dtype=np.int64).reshape(-1, 2)
            if name == 'terminal_filtered':
                terminal_mask, terminal_found = eligible, found
        saved['terminal_vertices'] = np.asarray(sorted(repair.initial_graph), dtype=np.int64)
        forest = {u: set(vs) for u, vs in repair.initial_graph.items()}
        for step in repair.steps:
            remove_vertices(forest, [step['vertex']])
        name = 'forest_entry' if repair.transition is not None else 'after_completed_repairs'
        stages.append(edge_stage(oracle, forest, name)[0])
        saved['forest_edges'] = np.asarray(sorted(graph_edges(forest)), dtype=np.int64).reshape(-1, 2)
        saved['forest_vertices'] = np.asarray(sorted(forest), dtype=np.int64)
    steps = schedule_steps(oracle.n, batches)
    a, b = steps[oracle.edges[:, 0]], steps[oracle.edges[:, 1]]
    both_committed = (a >= 0) & (b >= 0)
    simultaneous = both_committed & (a == b)
    result = {'stages': stages,
              'same_batch_true_edges': strength_counts(oracle, both_committed, simultaneous),
              'missing_terminal_same_batch': None,
              'committed_edge_count': int(both_committed.sum()),
              'uncommitted_edge_count': int((~both_committed).sum())}
    if terminal_mask is not None:
        # Please do not count an edge removed by a singleton commit as a new miss.
        missing = terminal_mask & ~terminal_found
        result['missing_terminal_same_batch'] = strength_counts(oracle, missing & both_committed, simultaneous)
        result['missing_terminal_unresolved_edges'] = int((missing & ~both_committed).sum())
    if snapshot_path is not None:
        snapshot_path.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(snapshot_path, true_edges=oracle.edges, strengths=oracle.edge_strengths,
                            theta_reference=oracle.theta, commit_step=steps,
                            repair_vertices=np.asarray([s['vertex'] for s in repair.steps], dtype=np.int64),
                            **saved)
    return result
