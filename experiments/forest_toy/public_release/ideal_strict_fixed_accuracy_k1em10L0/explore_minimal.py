"""Explore p/M/d/TV on one small target seed, then freeze independent confirmation.

The sampler, exact oracle, target law, vote rule, and degree repair are reused
unchanged. Please keep all censored runs separate from completed sample scores.
"""
import argparse
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
from time import perf_counter

import numpy as np

from budget_core import BudgetOracle, QueryBudgetExceeded
from explore import FixedColorings
from minimal_oracle import MinimalRecorder, baseline_sample, load_backend, make_target
from minimal_screen import ScreenParameters, screen_threshold
from minimal_study import SOURCES as PILOT_SOURCES, initial_kl_diagnostics
from profile_minimal import SIGMA, initial_edges, weighted_summary
from robustness import RobustTrace, sample_robust
from robustness_study import stats
from tree_study import audit_tree
from tune import BETA
from validate import digest, freeze_json, read_runs
from weighted_diagnostics import WeightedObserver, diagnose
from weighted_oracle import weight_metadata

ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT / 'results' / 'minimal_hyperparameter_exploration'
PALETTES = (3, 4, 6, 8)
DEGREES = (9, 18, 36)
THRESHOLDS = (.0001, .001, .003, .01)
SCREEN_BUDGETS = (256, 512, 1024, 2048, 3072)
GOAL_KL = 1e-7
SELECTION_LEVELS = (1e-8, 1e-7, 1e-6, 1e-5)
SOURCES = tuple(dict.fromkeys((*PILOT_SOURCES, 'explore_minimal.py')))
REFERENCE = {'matching': (4, 39, 9, .01), 'path': (8, 73, 9, .01)}
SELECTION_RULE = {
    'per_precision': 'For each target and epsilon in 1e-8,1e-7,1e-6,1e-5: minimum Q among complete coarse runs with KL/token <= epsilon.',
    'per_palette': 'For every target/p: minimum Q with KL/token <= 1e-7; otherwise minimum KL among complete runs. If none complete, retain the run with the smallest completion cost lower bound.',
    'endpoint': 'Also retain the minimum-Q complete coarse setting regardless of KL.',
    'reference': 'Always retain the previous p/M/d with tau=.01: matching 4/39/9 and path 8/73/9.',
    'ties': 'Cost selection: Q, then KL floored at 1e-12, then (p,M,d,tau). Error selection: KL floored at 1e-12, then Q, then setting.',
    'confirmation': 'Freeze the union of these choices before N=16384 repeat IDs 2 and 3; do not reselect after confirmation. Baseline performance is not a selection input.',
}


def coloring_grid():
    return {p: sorted({max(9, 2*int((b/(3*p*(p-1)))/2)+1) for b in SCREEN_BUDGETS})
            for p in PALETTES}


def proposal_job(target, n, repeat, setting):
    p, m, d, tau = setting
    return ('proposal', target, n, repeat, 'union_degree', p, m, d, tau)


def coarse_jobs():
    jobs = {proposal_job(t, 4096, 0, (p, m, d, tau))
            for t in REFERENCE for p, ms in coloring_grid().items() for m in ms
            for d in DEGREES for tau in THRESHOLDS}
    jobs.update(proposal_job(t, 4096, 0, s) for t, s in REFERENCE.items())
    return sorted(jobs)


def job_name(job):
    kind, target, n, repeat, policy, p, m, d, tau = job
    return f'{kind}_{target}_N{n}_{policy}_p{p}_M{m}_d{d}_tau{tau:.8g}_seed{repeat}'


def setting_key(row):
    return tuple(row[k] for k in ('target', 'palette', 'colorings', 'd', 'screen_threshold'))


def ensure_profiles(jobs, output):
    profiles = []
    for target, n, repeat in sorted({(j[1], j[2], j[3]) for j in jobs}):
        oracle, seeds = make_target(target, n, repeat, True, True, SIGMA)
        rows, weights, total = initial_edges(oracle)
        path = output / 'target_profiles' / f'{target}_bias1_tail1_seed{repeat}.npz'
        path.parent.mkdir(parents=True, exist_ok=True)
        arrays = dict(edges=oracle.edges, theta=oracle.edge_strengths, fields=oracle.fields,
                      initial_rows=rows, initial_edge_kl=weights)
        if path.exists():
            with np.load(path) as saved:
                for key, values in arrays.items():
                    np.testing.assert_array_equal(saved[key], values)
        else:
            np.savez_compressed(path, **arrays)
        profiles.append({'target': target, 'n': n, 'repeat': repeat, 'seeds': seeds,
                         'sigma': SIGMA, 'tail_shape_b': oracle.tail_shape,
                         'all_at_once_kl_per_token': total/n,
                         'confidence': weighted_summary([rows[:, :2].max(axis=1)]),
                         'theta': weighted_summary([oracle.edge_strengths]),
                         'edge_kl': weighted_summary([weights]),
                         'snapshot': str(path.relative_to(output)), 'sha256': digest(path)})
    freeze_json(output / 'target_profiles.json', profiles)


def run_job(job, output, query_limit='target_n'):
    """Run one frozen sampler job, optionally without an external Q cap.

    ``query_limit='target_n'`` preserves every historical caller exactly.  A
    positive integer installs that explicit cap, while ``None`` leaves the
    sampler's own finite screen/peel/round guards unchanged and merely removes
    the experiment-level ``Q <= N`` censoring rule.
    """
    kind, target, n, repeat, policy, p, m, d, tau = job
    limit = n if query_limit == 'target_n' else query_limit
    if limit is not None and (not isinstance(limit, int) or limit < 0):
        raise ValueError('Please use target_n, None, or a nonnegative integer query limit.')
    np.seterr(divide='raise', over='raise', invalid='raise')
    started = perf_counter()
    oracle, seeds = make_target(target, n, repeat, True, True, SIGMA, kind,
                                m if kind == 'baseline' else 0)
    weights = weight_metadata(oracle)
    # Please do not inherit a weakest-edge certificate for the biased weak-tail law.
    weights.pop('true_signal_lower_bound')
    weights.pop('true_response_upper_bound')
    common = {'job': list(job), 'kind': kind, 'target': target, 'n': n, 'repeat': repeat,
              'biased': True, 'weak_tail': True, 'case': 'bias1_tail1', 'seeds': seeds,
              'sigma': SIGMA, 'theta_reference': oracle.theta, 'field_seed': oracle.field_seed,
              'fields_sha256': hashlib.sha256(oracle.fields.astype('<f8').tobytes()).hexdigest(),
              'tail_shape_b': oracle.tail_shape, 'target_log_z': oracle.log_z, **weights}
    recorder = MinimalRecorder(n)
    trace_path = output / 'traces' / (job_name(job)+'.npz')
    setup_seconds = perf_counter()-started
    sample_start = perf_counter()
    if kind == 'baseline':
        baseline_sample(oracle, m, seeds[1], seeds[2], policy, recorder)
        sample_seconds = perf_counter()-sample_start
        assert oracle.cost.total == oracle.cost.rounds == m
        small, extra = divmod(n, m)
        expected = n if policy == 'random' else sum(n-small*k-min(k, extra) for k in range(m))
        assert oracle.cost.returned_rows == expected
        score = recorder.finish(oracle, trace_path)
        return {**common, 'baseline': policy, 'status': 'complete', 'budget': m, 'depth': m,
                'setup_seconds': setup_seconds, 'sample_seconds': sample_seconds,
                'seconds': perf_counter()-started, 'trace': str(trace_path.relative_to(output)),
                'batch_size_histogram': dict(Counter(map(len, recorder.batches))),
                **score, **asdict(oracle.cost), 'total': oracle.cost.total}
    params = FixedColorings(n, oracle.theta, d=d, beta=BETA, palette_override=p, coloring_count=m)
    measured = oracle if limit is None else BudgetOracle(oracle, limit)
    observer = WeightedObserver(ScreenParameters(params, tau), measured)
    repair, stopped = RobustTrace(), None
    try:
        with screen_threshold(tau):
            result = sample_robust(measured, params, seeds[1], seeds[2], observer=observer,
                                   commit_observer=recorder, variant=policy, repair_trace=repair)
    except QueryBudgetExceeded as error:
        stopped = error.details
    sample_seconds = perf_counter()-sample_start
    observer.finish_observation(oracle)
    repair_diagnostics = repair.posthoc(oracle)
    if stopped is None:
        score = recorder.finish(oracle, trace_path)
        checked = audit_tree(oracle, params, result, observer)
    else:
        score = {'kl_nats': None, 'kl_per_token': None, 'tv_score': None,
                 'log_q_over_p': None, 'evaluation_seconds': 0.}
        checked = {'unsafe_batches': None, 'all_tokens_committed': False,
                   'fallback': repair.terminal_fallback}
    graph_path = output / 'graphs' / (job_name(job)+'.npz')
    strengths = diagnose(oracle, observer, repair, recorder.batches, graph_path)
    initial = initial_kl_diagnostics(oracle, observer, repair, True, True, target,
                                     repeat, recorder.batches, output)
    if limit is not None:
        assert oracle.cost.total <= limit
    return {**common, 'variant': policy, 'palette': p, 'colorings': m, 'd': d,
            'screen_threshold': tau, 'parameters': asdict(params), 'oracle_exact': True,
            'all_edge_certificate_claimed': False, 'status': 'censored' if stopped else 'complete',
            'budget_stop': stopped, 'query_limit': limit, 'screen_calls': len(observer.screens),
            'screen_observations': observer.screens,
            'depth': 1+len(observer.screens)+oracle.cost.rounds,
            'committed_tokens': int((recorder.history >= 0).sum()),
            'setup_seconds': setup_seconds, 'sample_seconds': sample_seconds,
            'seconds': perf_counter()-started, 'repair_diagnostics': repair_diagnostics,
            'strength_diagnostics': strengths, 'initial_kl_diagnostics': initial,
            'trace': str(trace_path.relative_to(output)) if stopped is None else None,
            'graph_snapshot': str(graph_path.relative_to(output)),
            'batch_size_histogram': dict(Counter(map(len, recorder.batches))),
            **score, **checked, **asdict(oracle.cost), 'total': oracle.cost.total}


def execute(jobs, path, workers, output):
    rows = read_runs(path)
    wanted, done = set(jobs), {tuple(r['job']) for r in rows}
    if len(done) != len(rows) or not done <= wanted:
        raise ValueError('Please retain the frozen job list when resuming.')
    pending = [j for j in jobs if j not in done]
    if not pending:
        return rows
    load_backend()
    start = perf_counter()
    with ProcessPoolExecutor(max_workers=workers) as pool, path.open('a') as stream:
        futures = [pool.submit(run_job, j, output) for j in pending]
        for future in as_completed(futures):
            row = future.result()
            rows.append(row)
            stream.write(json.dumps(row, separators=(',', ':'), allow_nan=False)+'\n')
            stream.flush()
            if len(rows) % 10 == 0 or len(rows) == len(jobs):
                print(f'{output.name}/{path.stem} {len(rows)}/{len(jobs)} '
                      f'{job_name(row["job"])} Q={row["total"]} KL/N={row["kl_per_token"]} '
                      f'{row["status"]} elapsed={perf_counter()-start:.1f}s', flush=True)
    execution = path.with_name(path.stem+'_execution.json')
    history = json.loads(execution.read_text()) if execution.exists() else []
    history.append({'new_runs': len(pending), 'workers': workers, 'seconds': perf_counter()-start})
    execution.write_text(json.dumps(history, indent=2)+'\n')
    return rows


def summarize(rows, repeats):
    groups, result = defaultdict(list), {'complete_settings': [], 'censored_settings': []}
    for row in rows:
        groups[setting_key(row)].append(row)
    for key, group in sorted(groups.items()):
        group.sort(key=lambda r: r['repeat'])
        assert [r['repeat'] for r in group] == list(repeats)
        complete = all(r['status'] == 'complete' for r in group)
        item = dict(zip(('target', 'palette', 'colorings', 'd', 'screen_threshold'), key))
        item.update({'n': group[0]['n'], 'runs': len(group), 'repeats': list(repeats),
                     'censored_runs': sum(r['status'] == 'censored' for r in group),
                     'jobs': [r['job'] for r in group],
                     'cost': {k: stats([r[k] for r in group]) for k in
                              ('total', 'counterfactual', 'rounds', 'depth', 'sample_seconds', 'evaluation_seconds')},
                     'kl': stats([r['kl_per_token'] for r in group]) if complete else None,
                     'kl_individual': [r['kl_per_token'] for r in group],
                     'repair_tokens': stats([r['repair_diagnostics']['repair_tokens'] for r in group])})
        result['complete_settings' if complete else 'censored_settings'].append(item)
    return result


def select_candidates(rows):
    chosen = {}
    def add(target, setting, reason, row=None):
        key = (target, *setting)
        if key not in chosen:
            chosen[key] = {'target': target, 'palette': setting[0], 'colorings': setting[1],
                           'd': setting[2], 'screen_threshold': setting[3], 'reasons': [],
                           'coarse_job': row['job'] if row else None}
        chosen[key]['reasons'].append(reason)
    cost_key = lambda r: (r['total'], max(1e-12, r['kl_per_token']), *setting_key(r)[1:])
    error_key = lambda r: (max(1e-12, r['kl_per_token']), r['total'], *setting_key(r)[1:])
    for target, reference in REFERENCE.items():
        all_rows = [r for r in rows if r['target'] == target]
        good = [r for r in all_rows if r['status'] == 'complete']
        for epsilon in SELECTION_LEVELS:
            eligible = [r for r in good if r['kl_per_token'] <= epsilon]
            if eligible:
                row = min(eligible, key=cost_key)
                add(target, setting_key(row)[1:], f'min_Q_at_KL_le_{epsilon:g}', row)
        for p in PALETTES:
            local = [r for r in good if r['palette'] == p]
            eligible = [r for r in local if r['kl_per_token'] <= GOAL_KL]
            if local:
                row = min(eligible, key=cost_key) if eligible else min(local, key=error_key)
            else:
                local = [r for r in all_rows if r['palette'] == p]
                row = min(local, key=lambda r: (r['budget_stop']['completion_query_lower_bound'], *setting_key(r)[1:]))
            add(target, setting_key(row)[1:], f'representative_p{p}', row)
        if good:
            row = min(good, key=cost_key)
            add(target, setting_key(row)[1:], 'minimum_Q_endpoint', row)
        source = next((r for r in all_rows if setting_key(r)[1:] == reference), None)
        add(target, reference, 'previous_reference', source)
    return [chosen[k] for k in sorted(chosen)]


def match_budgets(summary):
    return [{**{k: r[k] for k in ('target', 'palette', 'colorings', 'd', 'screen_threshold', 'n')},
             'axis': axis, 'proposal_mean': r['cost'][axis]['mean'],
             'baseline_batches': int(np.floor(r['cost'][axis]['mean']+.5))}
            for r in summary['complete_settings'] for axis in ('total', 'depth')]


def compare(proposals, baselines, matches, repeats):
    a_lookup = {(setting_key(r), r['repeat']): r for r in proposals}
    b_lookup = {(r['target'], r['repeat'], r['baseline'], r['budget']): r for r in baselines}
    comparisons = []
    for match in matches:
        key = setting_key(match)
        aa = [a_lookup[key, seed] for seed in repeats]
        for policy in ('random', 'confidence'):
            bb = [b_lookup[match['target'], seed, policy, match['baseline_batches']] for seed in repeats]
            for a, b in zip(aa, bb):
                for field in ('edges_sha256', 'weights_sha256', 'fields_sha256'):
                    assert a[field] == b[field]
            comparisons.append({**match, 'baseline': policy,
                                'proposal_kl': stats([r['kl_per_token'] for r in aa]),
                                'baseline_kl': stats([r['kl_per_token'] for r in bb]),
                                'proposal_kl_individual': [r['kl_per_token'] for r in aa],
                                'baseline_kl_individual': [r['kl_per_token'] for r in bb],
                                'paired_baseline_minus_proposal_kl':
                                [b['kl_per_token']-a['kl_per_token'] for a, b in zip(aa, bb)]})
    return comparisons


def protocol(jobs, stage):
    return {'version': 1, 'stage': stage, 'proposal_jobs': jobs,
            'n': sorted({j[2] for j in jobs}), 'repeat_ids': sorted({j[3] for j in jobs}),
            'coloring_grid': coloring_grid(), 'screen_budget_design': SCREEN_BUDGETS,
            'degrees': DEGREES, 'thresholds': THRESHOLDS, 'goal_kl_per_token': GOAL_KL,
            'selection_rule': SELECTION_RULE, 'target': 'Bias on, zero tail; sigma=8.85, same law as minimal_pilot.',
            'algorithm': 'Unchanged union_degree; majority vote, preprocessing/bank, peeling and centroid unchanged.',
            'budget': 'Total Q<=N; atomic submission families; censored settings kept separate without KL.',
            'comparison': 'Baseline B=round-half-up(mean Q), and separately mean T; balanced batches, stochastic values. Extra fixed anchors 32,128,256,512,1024,2048,3072.',
            'seed_note': 'Same target and starting proposal RNG seeds within N/repeat; changing control flow need not preserve tokenwise draws. Baseline RNG also depends on B.',
            'source_sha256': {name: digest(ROOT/name) for name in SOURCES}}


def run_stage(jobs, output, workers, stage):
    output.mkdir(parents=True, exist_ok=True)
    freeze_json(output/'protocol.json', protocol(jobs, stage))
    ensure_profiles(jobs, output)
    repeats = sorted({j[3] for j in jobs})
    proposals = execute(jobs, output/'proposal_runs.jsonl', workers, output)
    summary = summarize(proposals, repeats)
    freeze_json(output/'summary.json', summary)
    matches = match_budgets(summary)
    freeze_json(output/'matched_budgets.json', matches)
    if stage == 'coarse':
        # Please freeze candidates before either baseline ranking or confirmation is observed.
        freeze_json(output.parent/'selection.json', {'rule': SELECTION_RULE,
                    'coarse_runs_sha256': digest(output/'proposal_runs.jsonl'),
                    'candidates': select_candidates(proposals)})
    baselines = {('baseline', r['target'], r['n'], repeat, policy, 0, r['baseline_batches'], 0, 0.)
                 for r in matches for repeat in repeats for policy in ('random', 'confidence')}
    baselines.update(('baseline', target, jobs[0][2], repeat, policy, 0, b, 0, 0.)
                     for target in REFERENCE for repeat in repeats for policy in ('random', 'confidence')
                     for b in (32, 128, 256, 512, 1024, 2048, 3072) if b <= jobs[0][2])
    baseline_jobs = sorted(baselines)
    freeze_json(output/'baseline_jobs.json', baseline_jobs)
    records = execute(baseline_jobs, output/'baseline_runs.jsonl', workers, output)
    freeze_json(output/'comparisons.json', compare(proposals, records, matches, repeats))
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', choices=('coarse', 'confirm', 'all'), default='all')
    parser.add_argument('--workers', type=int, default=6)
    parser.add_argument('--output', type=Path, default=OUTPUT)
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('Please use a positive process count.')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if args.stage in ('coarse', 'all'):
        run_stage(coarse_jobs(), output/'coarse_n4096', args.workers, 'coarse')
    if args.stage in ('confirm', 'all'):
        selected = json.loads((output/'selection.json').read_text())
        assert digest(output/'coarse_n4096'/'proposal_runs.jsonl') == selected['coarse_runs_sha256']
        jobs = sorted(proposal_job(r['target'], 16384, repeat, setting_key(r)[1:])
                      for r in selected['candidates'] for repeat in (2, 3))
        run_stage(jobs, output/'confirm_n16384', args.workers, 'confirm')
    print(json.dumps({'finished_stage': args.stage, 'output': str(output)}), flush=True)


if __name__ == '__main__':
    main()
