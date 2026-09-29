"""Explore connected paths and binary trees under the unchanged Q<=N sampler."""

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
from time import perf_counter

import numpy as np

from budget_core import BudgetObserver, BudgetOracle, CommitTrace, QueryBudgetExceeded
from budget_study import SOURCES as BUDGET_SOURCES
from explore import FixedColorings
from scale_study import baseline_key, comparisons, match_budgets, row_key, summarize as cost_summary
from toy import sample
from tradeoff import write_json
from tree_oracle import TreeDensityRecorder, load_backend, make_tree, tree_random_batch_sample
from tree_study import TREE_IDS, TREE_SEED, audit_tree
from tune import BETA
from validate import digest, freeze_json, read_runs


N, REPEATS = 16384, 10
GRID = {'path': {8: (97, 113, 129, 135), 10: (61, 73, 85)},
        'binary': {10: (69, 85), 12: (47, 59), 16: (33,)}}
SOURCES = (*BUDGET_SOURCES, 'scale_study.py', 'connected_study.py')
EDGE_METRICS = ('directed_false_claims', 'directed_missing_claims', 'sym_false_edges',
                'sym_missing_edges', 'sym_cycle_rank', 'sym_components', 'row_error_fraction')


def connected_seeds(target, n, repeat, kind, budget=0):
    graph = int(np.random.SeedSequence([TREE_SEED, 0, TREE_IDS[target], n, repeat]).generate_state(1)[0])
    source = [TREE_SEED, 1 if kind == 'proposal' else 2, TREE_IDS[target], n, repeat]
    if kind != 'proposal':
        source.append(budget)
    return [graph, *np.random.SeedSequence(source).generate_state(2).tolist()]


def graph_metadata(oracle):
    return {'max_degree': oracle.max_degree, 'edge_count': len(oracle.edges),
            'edges_sha256': hashlib.sha256(oracle.edges.astype('<i8').tobytes()).hexdigest()}


def add_edge_diagnostics(observer, oracle):
    """Please inspect hidden edges only after all sampler decisions have ended."""
    for screen, decoded in zip(observer.screens, observer.decoded):
        assert screen['complete']
        rows = decoded['rows']
        residual = set(rows)
        truth = {u: set(oracle.adjacency[u]) & residual for u in residual}
        true_edges = {(min(u, v), max(u, v)) for u, vs in truth.items() for v in vs}
        recovered = {(min(u, v), max(u, v)) for u, vs in rows.items() for v in vs}
        parent = {u: u for u in residual}

        def root(u):
            while parent[u] != u:
                parent[u] = parent[parent[u]]
                u = parent[u]
            return u

        components = len(residual)
        for u, v in recovered:
            a, b = root(u), root(v)
            if a != b:
                parent[a] = b
                components -= 1
        screen.update({
            'directed_false_claims': sum(len(rows[u]-truth[u]) for u in residual),
            'directed_missing_claims': sum(len(truth[u]-rows[u]) for u in residual),
            'sym_false_edges': len(recovered-true_edges), 'sym_missing_edges': len(true_edges-recovered),
            'sym_cycle_rank': len(recovered)-len(residual)+components, 'sym_components': components,
            'row_error_fraction': sum(rows[u] != truth[u] for u in residual)/len(residual)})


def run_job(job):
    kind, target, n, p, m, d, repeat = job
    np.seterr(divide='raise', over='raise', invalid='raise')
    seeds = connected_seeds(target, n, repeat, kind, m if kind == 'baseline' else 0)
    underlying = make_tree(n, target, seeds[0], coupling=.5)
    started = perf_counter()
    common = {'job': list(job), 'kind': kind, 'phase': 'connected_exploration', 'target': target,
              'n': n, 'repeat': repeat, 'seeds': seeds, 'theta': underlying.theta,
              'vocab': underlying.vocab, **graph_metadata(underlying)}
    if kind == 'baseline':
        result = tree_random_batch_sample(underlying, m, seeds[1], seeds[2])
        assert underlying.cost.total == m <= n
        return {**common, 'budget': m, 'depth': m, 'screen_calls': 0,
                'seconds': perf_counter()-started,
                **{k: v for k, v in result.items() if k not in ('sample', 'batches')},
                **asdict(underlying.cost), 'total': underlying.cost.total,
                'sample_sha256': hashlib.sha256(result['sample'].astype('<i4').tobytes()).hexdigest(),
                'batch_size_histogram': {str(k): v for k, v in sorted(Counter(map(len, result['batches'])).items())}}
    oracle = BudgetOracle(underlying, n)
    params = FixedColorings(n, oracle.theta, d=d, beta=BETA, palette_override=p, coloring_count=m)
    recorder, observer = TreeDensityRecorder(n), BudgetObserver(params, oracle)
    trace, stopped = CommitTrace(recorder, n), None
    try:
        result = sample(oracle, params, seeds[1], seeds[2], observer=observer, commit_observer=trace)
    except QueryBudgetExceeded as error:
        stopped = error.details
    sample_seconds = perf_counter()-started
    observer.finish_observation(underlying)
    add_edge_diagnostics(observer, underlying)
    if stopped is None:
        score = recorder.finish(underlying, result['sample'])
        checked = audit_tree(underlying, params, result, observer)
        structural = (checked['all_tokens_committed'] and checked['fallback'] is None
                      and checked['unsafe_batches'] == 0 and checked['low_degree_row_errors'] == 0
                      and checked['terminal_row_errors'] == 0)
    else:
        score = {'tv_score': None, 'log_q_over_p': None}
        checked = {'all_tokens_committed': False, 'unsafe_batches': None, 'fallback': None}
        structural = None
    elapsed = perf_counter()-started
    return {**common, 'palette': p, 'colorings': m, 'parameters': asdict(params),
            'separation_lhs_over_signal': (4*params.eps+params.tail_tolerance)/params.signal,
            'status': 'censored' if stopped else 'complete', 'budget_stop': stopped, 'query_limit': n,
            'screen_calls': len(observer.screens), 'completed_screens': sum(s['complete'] for s in observer.screens),
            'screen_cap': params.screen_cap, 'screen_cap_reached': len(observer.screens) == params.screen_cap,
            'screen_observations': observer.screens, 'depth': 1+len(observer.screens)+oracle.cost.rounds,
            'committed_tokens': int((trace.history >= 0).sum()), 'batch_size_histogram': trace.histogram(),
            'sample_sha256': hashlib.sha256(trace.history.astype('<i4').tobytes()).hexdigest() if stopped is None else None,
            'sample_seconds': sample_seconds, 'posthoc_seconds': elapsed-sample_seconds, 'seconds': elapsed,
            'structural_success': structural, **score, **checked, **asdict(oracle.cost), 'total': oracle.cost.total}


def summarize(records):
    summary = cost_summary(records)
    diagnostics = []
    for setting in sorted({row_key(r)[:5] for r in records}):
        group = [r for r in records if row_key(r)[:5] == setting]
        first = [r['screen_observations'][0] for r in group if r['screen_observations'][0]['complete']]
        diagnostics.append({'target': setting[0], 'n': setting[1], 'palette': setting[2],
                            'colorings': setting[3], 'd': setting[4], 'first_screen_observed_runs': len(first),
                            **{k: float(np.mean([s[k] for s in first])) if first else None for k in
                               (*EDGE_METRICS, 'truncation_fraction', 'posthoc_low_degree_row_errors',
                                'posthoc_peel_degree_le_half_d')}})
    summary['diagnostic_settings'] = diagnostics
    return summary


def execute(jobs, path, workers, reused=None):
    records = read_runs(path)
    done = {tuple(r['job']) for r in records}
    if len(done) != len(records) or not done <= set(jobs):
        raise ValueError('Please retain the frozen settings and all recorded seeds when resuming.')
    with path.open('a') as stream:
        for job in jobs:
            if job in done or job[0] != 'baseline' or not reused:
                continue
            key = (job[1], job[2], job[4], job[6])
            if key in reused:
                old, source = reused[key]
                row = {**old, 'job': list(job), 'reuse_source': source}
                records.append(row)
                stream.write(json.dumps(row, separators=(',', ':'))+'\n')
                done.add(job)
    pending = [job for job in jobs if job not in done]
    if not pending:
        return records
    load_backend()
    started = perf_counter()
    with ProcessPoolExecutor(max_workers=workers) as pool, path.open('a') as stream:
        futures = [pool.submit(run_job, job) for job in pending]
        for future in as_completed(futures):
            try:
                row = future.result()
            except BaseException:
                for other in futures:
                    other.cancel()
                raise
            records.append(row)
            stream.write(json.dumps(row, separators=(',', ':'))+'\n')
            stream.flush()
            if len(records) % 10 == 0 or len(records) == len(jobs):
                print(f"{path.stem}: {len(records)}/{len(jobs)} {row['target']} {row['job'][2:6]} "
                      f"{row.get('status', 'baseline')} Q={row['total']} TVscore={row['tv_score']} "
                      f"elapsed={perf_counter()-started:.1f}s", flush=True)
    execution_path = path.with_name(path.stem+'_execution.json')
    invocations = json.loads(execution_path.read_text()) if execution_path.exists() else []
    invocations.append({'workers': workers, 'new_runs': len(pending), 'seconds': perf_counter()-started})
    write_json(execution_path, invocations)
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=8)
    parser.add_argument('--stage', choices=('all', 'proposal', 'baseline'), default='all')
    parser.add_argument('--settings', type=Path, help='Optional additional [target,N,p,M,d] settings.')
    parser.add_argument('--design-observation', type=Path)
    parser.add_argument('--reuse-baselines', type=Path, nargs='*', default=[])
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('results')/'connected_coarse')
    args = parser.parse_args()
    settings = (sorted(tuple(s) for s in json.loads(args.settings.read_text())) if args.settings else
                sorted((target, N, p, m, 9) for target, ps in GRID.items() for p, ms in ps.items() for m in ms))
    if args.workers < 1 or len(settings) != len(set(settings)):
        raise ValueError('Please use positive workers and distinct settings.')
    for target, n, p, m, d in settings:
        if target not in ('path', 'binary') or n not in (4096, 16384) or p < 3 or m < 1 or not m % 2 or d < 9:
            raise ValueError('Please use a connected target, N=4096 or 16384, p>=3, odd M, and d>=9.')
    args.output.mkdir(parents=True, exist_ok=True)
    reuse = {}
    for path in args.reuse_baselines:
        for row in read_runs(path):
            reuse[baseline_key(row)] = (row, str(path.resolve()))
    prior = Path(__file__).with_name('results')
    observations = [args.design_observation] if args.design_observation else [
        prior/'budget_study'/'summary.json', prior/'tree_study'/'report_ja.md']
    protocol = {'settings': settings, 'repeats': REPEATS, 'master_seed': TREE_SEED,
                'purpose': 'Adaptive PDCA for connected paths and balanced binary trees at N=16384. '
                           'Matching and original stars remain provisional references. No held-out accuracy claim.',
                'design': 'Path: bracket the prior p=8 transition and compare p=10. Binary: compare p=10,12,16 '
                          'near the one-screen budget ceiling. Prior p=8 binary runs failed even at large M. '
                          'Initial d=9. Retain all settings and all ten seeds, including censoring.',
                'target': 'A randomly relabeled connected path or breadth-first binary tree; theta=0.5/max_degree. '
                          'Same exact tree oracle and same sampler, fallback, and public-input query accounting.',
                'budget': 'Hard per-run Q=1+distinct counterfactual submissions+commit rounds<=N. '
                          'Refuse a whole packed family before evaluation if it does not fit; no cap fallback. '
                          'Any censored seed moves its entire setting to the separate table; full TV is undefined there.',
                'metrics': 'Primary mean Q and mean density-score joint TV; median,p90,SE and T=1+screens+R are auxiliary. '
                           'Posthoc first-screen directed false/missing claims, symmetrized false/missing edges, '
                           'cycle rank and row error fraction are passive diagnostics, not controller inputs.',
                'baseline': 'B=round-half-up(proposal mean Q), separately mean T. Balanced nonempty random batches; '
                            'ten independent baseline draws paired by graph seed. Deduplicate equal budgets.',
                'fixed_parameters': {'beta': BETA, 'chunks': 1, 'vocab': 2048, 'coupling': .5},
                'theory': 'The finite signal certificate is checked. Empirically small p,M do not inherit the '
                          'manuscript uniform success guarantee. This fixed-N exploration does not establish sublinearity.',
                'design_observation_sha256': {str(p.resolve()): digest(p) for p in observations},
                'baseline_reuse_sha256': {str(p.resolve()): digest(p) for p in args.reuse_baselines},
                'source_sha256': {name: digest(Path(__file__).with_name(name)) for name in SOURCES}}
    freeze_json(args.output/'protocol.json', protocol)
    jobs = [('proposal', *setting, repeat) for setting in settings for repeat in range(REPEATS)]
    proposals = (execute(jobs, args.output/'proposal_runs.jsonl', args.workers) if args.stage != 'baseline'
                 else read_runs(args.output/'proposal_runs.jsonl'))
    assert {tuple(r['job']) for r in proposals} == set(jobs)
    summary = summarize(proposals)
    freeze_json(args.output/'summary.json', summary)
    matches = match_budgets(summary)
    freeze_json(args.output/'matched_budgets.json', matches)
    if args.stage == 'proposal':
        return
    jobs = sorted({('baseline', item['target'], item['n'], 0, item['baseline_batches'], 0, repeat)
                   for item in matches for repeat in range(REPEATS)})
    baselines = execute(jobs, args.output/'baseline_runs.jsonl', args.workers, reuse)
    freeze_json(args.output/'comparisons.json', comparisons(proposals, baselines, matches))
    print(f"Finished {summary['settings']} settings: {len(summary['complete_settings'])} complete; "
          f"{len(summary['censored_settings'])} in the separate table.", flush=True)


if __name__ == '__main__':
    main()
