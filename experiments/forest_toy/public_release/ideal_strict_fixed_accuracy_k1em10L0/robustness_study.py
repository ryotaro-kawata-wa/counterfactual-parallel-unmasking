"""Four-tree, four-variant terminal ablation with matched random/confidence baselines."""

import argparse
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
from time import perf_counter

import numpy as np

from budget_core import BudgetCommitCursor, BudgetObserver, BudgetOracle, CommitTrace, QueryBudgetExceeded
from confidence import confidence_batch_sample
from connected_study import connected_seeds, graph_metadata
from explore import FixedColorings
from robustness import RobustTrace, VARIANTS, sample_robust
from scale_study import make_target, run_seeds, target_metadata
from toy import audit
from tradeoff import write_json
from tradeoff_core import DensityRecorder, random_batch_sample, schedule_audit
from tree_oracle import TreeDensityRecorder, load_backend, make_tree, tree_random_batch_sample
from tree_study import audit_tree
from tune import BETA
from validate import digest, freeze_json, read_runs


ROOT = Path(__file__).parent
REPEATS = 10
GRID = {'matching': (16384, 4, 9, (39, 49, 61)),
        'stars_original': (16384, 6, 17, (17, 19, 23)),
        'path': (16384, 8, 9, (97, 113, 135)),
        'binary': (65536, 12, 9, (97, 121, 145))}
SOURCES = ('toy.py', 'tree_bp.c', 'tree_oracle.py', 'tradeoff_core.py', 'confidence.py',
           'deferred_screen.py', 'cycle_repair.py', 'robustness.py', 'budget_core.py',
           'tune.py', 'explore.py', 'validate.py', 'scale_study.py', 'connected_study.py',
           'tree_study.py', 'tradeoff.py', 'budget_study.py', 'robustness_study.py')


def settings():
    return [(target, n, p, m, d) for target, (n, p, d, ms) in GRID.items() for m in ms]


def seeds_for(target, n, repeat, kind, budget=0):
    return (connected_seeds(target, n, repeat, kind, budget) if target in ('path', 'binary')
            else run_seeds(target, n, repeat, kind, budget))


def build_target(target, n, seed):
    return make_tree(n, target, seed, coupling=.5) if target in ('path', 'binary') else make_target(n, target, seed)


def metadata(oracle):
    return graph_metadata(oracle) if hasattr(oracle, 'edges') else target_metadata(oracle)


def run_job(job, output=None):
    kind, target, n, p, m, d, repeat, policy = job
    np.seterr(divide='raise', over='raise', invalid='raise')
    seeds = seeds_for(target, n, repeat, kind, m if kind == 'baseline' else 0)
    underlying = build_target(target, n, seeds[0])
    tree = hasattr(underlying, 'edges')
    common = {'job': list(job), 'kind': kind, 'phase': 'robustness', 'target': target, 'n': n,
              'repeat': repeat, 'seeds': seeds, 'theta': underlying.theta, 'vocab': underlying.vocab,
              **metadata(underlying)}
    started = perf_counter()
    if kind == 'baseline':
        if policy == 'confidence':
            result = confidence_batch_sample(underlying, m, seeds[1], seeds[2])
        elif policy == 'random':
            result = (tree_random_batch_sample(underlying, m, seeds[1], seeds[2]) if tree else
                      random_batch_sample(underlying, m, seeds[1], seeds[2]))
        else:
            raise ValueError('Please use an explicitly named baseline.')
        checked = {} if tree or policy == 'confidence' else schedule_audit(underlying, result['batches'])
        assert underlying.cost.total == underlying.cost.rounds == m <= n
        return {**common, 'baseline': policy, 'budget': m, 'depth': m, 'screen_calls': 0,
                'status': 'complete', 'seconds': perf_counter()-started,
                **{k: v for k, v in result.items() if k not in ('sample', 'batches')}, **checked,
                **asdict(underlying.cost), 'total': underlying.cost.total,
                'sample_sha256': hashlib.sha256(result['sample'].astype('<i4').tobytes()).hexdigest(),
                'batch_size_histogram': {str(k): v for k, v in sorted(Counter(map(len, result['batches'])).items())}}
    oracle = BudgetOracle(underlying, n)
    params = FixedColorings(n, oracle.theta, d=d, beta=BETA, palette_override=p, coloring_count=m)
    recorder = TreeDensityRecorder(n) if tree else DensityRecorder(n)
    observer, repair = BudgetObserver(params, oracle), RobustTrace()
    trace, stopped = CommitTrace(recorder, n), None
    try:
        result = sample_robust(oracle, params, seeds[1], seeds[2], observer=observer,
                               commit_session=None if tree else BudgetCommitCursor(oracle),
                               commit_observer=trace, variant=policy, repair_trace=repair)
    except QueryBudgetExceeded as error:
        stopped = error.details
    sample_seconds = perf_counter()-started
    observer.finish_observation(underlying)
    diagnostics = repair.posthoc(underlying)
    if stopped is None:
        score = recorder.finish(underlying, result['sample'])
        checked = audit_tree(underlying, params, result, observer) if tree else audit(underlying, params, result)
        structural = (checked['all_tokens_committed'] and checked['fallback'] is None
                      and checked['unsafe_batches'] == 0 and checked['low_degree_row_errors'] == 0
                      and checked['terminal_row_errors'] == 0)
    else:
        score = {'tv_score': None, 'log_q_over_p': None}
        checked = {'all_tokens_committed': False, 'unsafe_batches': None, 'fallback': repair.terminal_fallback}
        structural = None
    snapshot = None
    if output is not None and repeat == 0 and repair.initial_graph is not None:
        path = Path(output)/'graphs'/f'{target}_N{n}_p{p}_M{m}_d{d}_{policy}_seed0.npz'
        repair.save_snapshot(path, underlying)
        snapshot = str(path.relative_to(output))
    elapsed = perf_counter()-started
    return {**common, 'variant': policy, 'palette': p, 'colorings': m, 'parameters': asdict(params),
            'separation_lhs_over_signal': (4*params.eps+params.tail_tolerance)/params.signal,
            'status': 'censored' if stopped else 'complete', 'budget_stop': stopped, 'query_limit': n,
            'screen_calls': len(observer.screens), 'completed_screens': sum(s['complete'] for s in observer.screens),
            'screen_observations': observer.screens, 'depth': 1+len(observer.screens)+oracle.cost.rounds,
            'committed_tokens': int((trace.history >= 0).sum()), 'batch_size_histogram': trace.histogram(),
            'sample_sha256': hashlib.sha256(trace.history.astype('<i4').tobytes()).hexdigest() if stopped is None else None,
            'sample_seconds': sample_seconds, 'posthoc_seconds': elapsed-sample_seconds, 'seconds': elapsed,
            'structural_success': structural,
            'safe_schedule': checked['unsafe_batches'] == 0 if stopped is None else None,
            'repair_diagnostics': diagnostics, 'graph_snapshot': snapshot,
            **score, **checked, **asdict(oracle.cost), 'total': oracle.cost.total}


def group_key(row):
    return (row['target'], row['n'], row['palette'], row['colorings'], row['parameters']['d'], row['variant'])


def stats(values):
    a = np.asarray(values, dtype=float)
    return {'mean': float(a.mean()), 'se': float(a.std(ddof=1)/np.sqrt(len(a))) if len(a) > 1 else None,
            'median': float(np.median(a)), 'p90': float(np.quantile(a, .9))}


def summarize(proposals):
    groups, result = defaultdict(list), {'complete_settings': [], 'censored_settings': []}
    for row in proposals:
        groups[group_key(row)].append(row)
    for (target, n, p, m, d, variant), rows in sorted(groups.items()):
        assert len(rows) == REPEATS and {r['repeat'] for r in rows} == set(range(REPEATS))
        finished = [r for r in rows if r['status'] == 'complete']
        item = {'target': target, 'n': n, 'palette': p, 'colorings': m, 'd': d, 'variant': variant,
                'runs': len(rows), 'complete_runs': len(finished), 'censored_runs': len(rows)-len(finished),
                'cost': {k: stats([r[k] for r in rows]) for k in
                         ('total', 'counterfactual', 'rounds', 'depth', 'returned_rows', 'seconds')},
                'fallback_counts': dict(Counter(r['fallback'] or 'none' for r in rows))}
        complete = len(finished) == len(rows)
        item['tv'] = stats([r['tv_score'] for r in rows]) if complete else None
        item['safe_schedule_runs'] = sum(r.get('safe_schedule') is True for r in rows)
        initial = [r['repair_diagnostics'] for r in rows if r['repair_diagnostics']['initial'] is not None]
        item['terminal_observed_runs'] = len(initial)
        item['graphs'] = {stage: {k: stats([r[stage][k] for r in initial]) for k in
                                  ('vertices', 'edges', 'cycle_rank', 'missing_edges', 'extra_edges', 'retained_true_edges')}
                          for stage in ('before_filter', 'after_filter')} if initial else None
        item['repair_tokens'] = stats([r['repair_diagnostics']['repair_tokens'] for r in rows])
        item['peel_tokens'] = stats([r['repair_diagnostics']['roles'].get('peel', 0) for r in rows])
        item['centroid_rounds'] = stats([r['repair_diagnostics']['roles'].get('centroid', 0) for r in rows])
        if not complete:
            total_score = sum(r['tv_score'] for r in finished)
            item['empirical_score_bounds'] = [total_score/REPEATS, (total_score+REPEATS-len(finished))/REPEATS]
            item['stop_stages'] = dict(Counter(r['budget_stop']['stage'] for r in rows if r['budget_stop']))
        result['complete_settings' if complete else 'censored_settings'].append(item)
    return result


def match_budgets(summary):
    return [{k: row[k] for k in ('target', 'n', 'palette', 'colorings', 'd', 'variant')} |
            {'axis': axis, 'proposal_mean': row['cost'][axis]['mean'],
             'baseline_batches': int(np.floor(row['cost'][axis]['mean']+.5))}
            for row in summary['complete_settings'] for axis in ('total', 'depth')]


def compare(proposals, baselines, matches):
    output = []
    for match in matches:
        key = tuple(match[k] for k in ('target', 'n', 'palette', 'colorings', 'd', 'variant'))
        a = sorted([r for r in proposals if group_key(r) == key], key=lambda r: r['repeat'])
        for policy in ('random', 'confidence'):
            b = sorted([r for r in baselines if (r['target'], r['n'], r['budget'], r['baseline']) ==
                        (match['target'], match['n'], match['baseline_batches'], policy)], key=lambda r: r['repeat'])
            assert len(a) == len(b) == REPEATS
            assert [r['repeat'] for r in a] == [r['repeat'] for r in b] == list(range(REPEATS))
            assert all(x['seeds'][0] == y['seeds'][0] for x, y in zip(a, b))
            output.append({**match, 'baseline': policy, 'proposal_tv': stats([r['tv_score'] for r in a]),
                           'baseline_tv': stats([r['tv_score'] for r in b]),
                           'paired_baseline_minus_proposal_tv': stats([y['tv_score']-x['tv_score'] for x, y in zip(a, b)]),
                           'baseline_seconds': stats([r['seconds'] for r in b]),
                           'baseline_returned_rows': stats([r['returned_rows'] for r in b])})
    return output


def verify_quartets(proposals):
    groups = defaultdict(dict)
    for row in proposals:
        groups[tuple(row['job'][1:7])][row['variant']] = row
    for key, group in groups.items():
        assert set(group) == set(VARIANTS), key
        a = group['union_degree']
        for b in group.values():
            assert b['seeds'] == a['seeds']
            assert b['counterfactual'] == a['counterfactual'], key
            assert b['screen_observations'] == a['screen_observations'], key
            assert b['repair_diagnostics'].get('prefix') == a['repair_diagnostics'].get('prefix'), key
            assert b['repair_diagnostics']['roles'].get('peel', 0) == a['repair_diagnostics']['roles'].get('peel', 0), key
            assert b['total'] <= b['query_limit']
            if b['status'] == 'complete':
                assert b['committed_tokens'] == b['n']
                assert b['total'] == 1+b['counterfactual']+b['rounds']
            for step in b['repair_diagnostics']['steps']:
                assert step['total_after']-step['total_before'] == 1
                assert step['cycle_rank_after'] < step['cycle_rank_before']
        for edge_policy in ('union', 'mutual'):
            a, b = group[edge_policy+'_degree'], group[edge_policy+'_rank']
            assert a['repair_diagnostics'].get('after_filter') == b['repair_diagnostics'].get('after_filter')
            initial = a['repair_diagnostics']['initial']
            if initial is not None and initial['cycle_rank'] == 0:
                for field in ('sample_sha256', 'tv_score', 'total', 'rounds', 'batch_size_histogram'):
                    assert a[field] == b[field], (key, field)
    return {'quartets': len(groups), 'runs': len(proposals), 'same_terminal_prefix': True,
            'same_screen_and_peeling': True, 'filter_extra_queries': 0, 'repair_query_accounting': True}


def execute(jobs, path, workers, output, reuse=()):
    records = read_runs(path)
    wanted, done = set(jobs), {tuple(r['job']) for r in records}
    if len(done) != len(records) or not done <= wanted:
        raise ValueError('Please retain the frozen job list and all recorded seeds when resuming.')
    with path.open('a') as stream:
        for source in reuse:
            for row in read_runs(source):
                job = tuple(row['job'])
                if job in wanted and job not in done:
                    row = {**row, 'reuse_source': str(source.resolve())}
                    records.append(row)
                    stream.write(json.dumps(row, separators=(',', ':'))+'\n')
                    done.add(job)
    pending = [job for job in jobs if job not in done]
    if not pending:
        return records
    load_backend()
    started = perf_counter()
    with ProcessPoolExecutor(max_workers=workers) as pool, path.open('a') as stream:
        futures = [pool.submit(run_job, job, output) for job in pending]
        for future in as_completed(futures):
            row = future.result()
            records.append(row)
            stream.write(json.dumps(row, separators=(',', ':'))+'\n')
            stream.flush()
            if len(records) % 10 == 0 or len(pending) < 10 or len(records) == len(jobs):
                print(f"{path.stem}: {len(records)}/{len(jobs)} {row['target']} {row['job'][3:]} "
                      f"Q={row['total']} TV={row['tv_score']} {row['status']} "
                      f"elapsed={perf_counter()-started:.1f}s", flush=True)
    execution = path.with_name(path.stem+'_execution.json')
    history = json.loads(execution.read_text()) if execution.exists() else []
    history.append({'new_runs': len(pending), 'workers': workers, 'seconds': perf_counter()-started})
    write_json(execution, history)
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=8)
    parser.add_argument('--stage', choices=('pilot', 'all', 'proposal', 'baseline'), default='all')
    parser.add_argument('--output', type=Path, default=ROOT/'results'/'robustness_study')
    args = parser.parse_args()
    if args.workers < 1:
        raise ValueError('Please use at least one process.')
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    protocol = {'version': 1, 'settings': settings(), 'repeats': REPEATS, 'variants': VARIANTS,
                'baseline_policies': ['random', 'confidence'],
                'design': 'User-approved 12-setting boundary pilot; same p/M/d and existing seed domains across four variants. '
                          'Retune only after the paired ablation; retain every run. No fresh held-out accuracy claim.',
                'target': 'Existing matching/star N16384, path N16384, binary N65536. theta=.5/maximum_degree, '
                          'head masses .4/.4, total uniform-tail mass .2, vocabulary 2048; target labels permuted.',
                'control': 'Latest union graph plus global single_max_degree cycle repair, not the oldest all-token fallback.',
                'filter': 'Apply after unchanged terminal screen/peeling. Retain only existing union edges with raw '
                          'support >M//2 in both directions, including reverse support from discarded rows. '
                          'No new edges, no coloring-alignment requirement, zero extra oracle submissions.',
                'repair': 'Singleton maximizing cycle-rank decrease, then current degree, then smallest public idx. '
                          'Delete committed vertex; reuse unchanged centroid after forest transition. '
                          'Retain original round cap and outer Q cap.',
                'budget': 'Q=1+Qcf+R<=N, atomic family admission. Any censored seed moves the whole setting to a separate '
                          'table; no completed-seed-only TV curve. Main mean Q, auxiliary median/p90 and T=1+screens+R.',
                'error': 'TV density score only: estimate E_{graph,w} TV(Q_{graph,w},P_graph), '
                         'not the TV of the seed-mixture distribution. Ten zero scores do not prove zero TV. '
                         'Likelihood terms are retained to audit TV; no KL/N metric or figure.',
                'baseline': 'B=round-half-up(mean Q), separately mean T. Ten paired graph seeds, same baseline '
                            'order/value seed domains for random and confidence. Balanced nonempty batches (extras first). '
                            'Confidence=max individual-label conditional mass; fixed random priority breaks ties. '
                            'One current all-remaining response selects positions and samples values; no stale response. '
                            'Reuse exact equal-budget jobs; Q=T=B. Record returned rows and seconds independently.',
                'snapshots': 'Save all four terminal graph variants for repeat 0 at every setting, selected before outcomes.',
                'runtime': 'First one union_degree and same realized-Q confidence run per tree; then multiprocessing. '
                           'Exact deferred screen for all variants; legacy replay tests guard query/arithmetic equivalence.',
                'fixed': {'beta': BETA, 'chunks': 1, 'vocab': 2048, 'coupling': .5},
                'source_sha256': {name: digest(ROOT/name) for name in SOURCES}}
    freeze_json(args.output/'protocol.json', protocol)
    if args.stage == 'pilot':
        pilot_settings = [(t, n, p, ms[0], d) for t, (n, p, d, ms) in GRID.items()]
        jobs = [('proposal', *s, 0, 'union_degree') for s in pilot_settings]
        proposals = execute(jobs, args.output/'pilot_proposals.jsonl', min(args.workers, 4), args.output)
        jobs = [('baseline', r['target'], r['n'], 0, r['total'], 0, 0, 'confidence')
                for r in proposals if r['status'] == 'complete']
        execute(jobs, args.output/'pilot_baselines.jsonl', min(args.workers, 4), args.output)
        return
    jobs = [('proposal', *s, repeat, variant) for s in settings()
            for repeat in range(REPEATS) for variant in VARIANTS]
    path = args.output/'proposal_runs.jsonl'
    proposals = (read_runs(path) if args.stage == 'baseline' else
                 execute(jobs, path, args.workers, args.output, [args.output/'pilot_proposals.jsonl']))
    assert {tuple(r['job']) for r in proposals} == set(jobs)
    verification = verify_quartets(proposals)
    summary = summarize(proposals)
    freeze_json(args.output/'summary.json', summary)
    matches = match_budgets(summary)
    freeze_json(args.output/'matched_budgets.json', matches)
    write_json(args.output/'verification.json', verification)
    if args.stage == 'proposal':
        return
    jobs = sorted({('baseline', r['target'], r['n'], 0, r['baseline_batches'], 0, repeat, policy)
                   for r in matches for repeat in range(REPEATS) for policy in ('random', 'confidence')})
    baselines = execute(jobs, args.output/'baseline_runs.jsonl', args.workers, args.output,
                        [args.output/'pilot_baselines.jsonl'])
    assert {tuple(r['job']) for r in baselines} == set(jobs)
    freeze_json(args.output/'comparisons.json', compare(proposals, baselines, matches))
    verification.update({'baseline_runs': len(baselines), 'matched_budgets': len(matches),
                         'completed_settings': len(summary['complete_settings']),
                         'censored_settings': len(summary['censored_settings'])})
    write_json(args.output/'verification.json', verification)
    print(f'Finished {len(proposals)} proposal and {len(baselines)} baseline runs.', flush=True)


if __name__ == '__main__':
    main()
