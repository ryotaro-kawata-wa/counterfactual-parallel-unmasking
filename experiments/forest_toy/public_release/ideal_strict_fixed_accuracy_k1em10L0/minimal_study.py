"""Frozen 2x2 minimal-reproduction pilot, with two paired seeds per setting."""
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
from minimal_oracle import (MinimalRecorder, baseline_sample, load_backend, make_target)
from minimal_screen import ScreenParameters, screen_threshold
from profile_minimal import SIGMA
from robustness import RobustTrace, sample_robust
from robustness_study import SOURCES as LEGACY_SOURCES, stats
from tradeoff import write_json
from tree_study import audit_tree
from tune import BETA
from validate import digest, freeze_json, read_runs
from weighted_diagnostics import WeightedObserver, diagnose, graph_edges, union_graph
from weighted_oracle import weight_metadata

ROOT = Path(__file__).parent
OUTPUT = ROOT/'results'/'minimal_pilot'
N, REPEATS = 16384, 2
GRID = {'matching': (4, (23, 39, 61)), 'path': (8, (49, 73, 97))}
THRESHOLDS = (2*BETA/N**.5, .001, .01, .05)
SOURCES = tuple(dict.fromkeys((*LEGACY_SOURCES, 'weighted_oracle.py', 'weighted_diagnostics.py',
          'weighted_tree_bp.c', 'minimal_tree_bp.c', 'minimal_oracle.py',
          'minimal_screen.py', 'minimal_study.py', 'profile_minimal.py')))


def case_name(biased, weak_tail):
    return f'bias{int(biased)}_tail{int(weak_tail)}'


def job_name(job):
    kind, target, biased, tail, repeat, policy, m, threshold = job
    return f'{kind}_{target}_{case_name(biased, tail)}_{policy}_M{m}_tau{threshold:.8g}_seed{repeat}'


def proposal_jobs():
    return [('proposal', target, biased, tail, repeat, variant, m, threshold)
            for target, (_, ms) in GRID.items() for biased in (False, True)
            for tail in (False, True) for m in ms for threshold in THRESHOLDS
            for variant in (('union_degree', 'mutual_rank') if m == ms[1] else ('mutual_rank',))
            for repeat in range(REPEATS)]


def initial_kl_diagnostics(oracle, observer, repair, biased, tail, target, repeat, batches, output):
    profile = np.load(output/'target_profiles'/f'{target}_{case_name(biased, tail)}_seed{repeat}.npz')
    np.testing.assert_array_equal(profile['edges'], oracle.edges)
    np.testing.assert_array_equal(profile['theta'], oracle.edge_strengths)
    np.testing.assert_array_equal(profile['fields'], oracle.fields)
    weights = profile['initial_edge_kl']
    initial = float(weights.sum())
    graphs = [(f'screen_{i}', union_graph(x['rows'])) for i, x in enumerate(observer.decoded)]
    if repair.union_graph is not None:
        graphs += [('terminal_union', repair.union_graph), ('terminal_filtered', repair.initial_graph)]
    result = []
    for name, graph in graphs:
        active = np.zeros(oracle.n, dtype=bool)
        active[list(graph)] = True
        eligible = active[oracle.edges[:, 0]] & active[oracle.edges[:, 1]]
        edges = graph_edges(graph)
        found = np.array([tuple(map(int, e)) in edges for e in oracle.edges])
        mass = float(weights[eligible].sum())
        kept = float(weights[eligible & found].sum())
        relative = oracle.edge_strengths/oracle.theta
        result.append({'stage': name, 'initial_kl_mass': mass, 'retained_kl_mass': kept,
                       'kl_recall': kept/mass if mass else None,
                       'weak_edges_below_point1': int((eligible & (relative < .1)).sum()),
                       'retained_weak_edges_below_point1': int((eligible & found & (relative < .1)).sum())})
    return {'all_initial_edge_kl': initial, 'stages': result}


def run_job(job, output):
    kind, target, biased, tail, repeat, policy, m, threshold = job
    np.seterr(divide='raise', over='raise', invalid='raise')
    started = perf_counter()
    underlying, seeds = make_target(target, N, repeat, biased, tail, SIGMA, kind,
                                    m if kind == 'baseline' else 0)
    weights = weight_metadata(underlying)
    # Please omit the previous symmetric-unary signal certificate: it is not valid
    # as a weakest-edge lower bound for this new biased, zero-reaching target.
    weights.pop('true_signal_lower_bound')
    weights.pop('true_response_upper_bound')
    common = {'job': list(job), 'kind': kind, 'target': target, 'n': N, 'repeat': repeat,
              'biased': biased, 'weak_tail': tail, 'case': case_name(biased, tail),
              'seeds': seeds, 'theta_reference': underlying.theta,
              'sigma': SIGMA if biased else 0., 'field_seed': underlying.field_seed,
              'fields_sha256': hashlib.sha256(underlying.fields.astype('<f8').tobytes()).hexdigest(),
              'tail_shape_b': underlying.tail_shape, 'target_log_z': underlying.log_z,
              **weights}
    recorder = MinimalRecorder(N)
    trace_path = output/'traces'/(job_name(job)+'.npz')
    setup_seconds = perf_counter()-started
    sample_start = perf_counter()
    if kind == 'baseline':
        sample = baseline_sample(underlying, m, seeds[1], seeds[2], policy, recorder)
        sample_seconds = perf_counter()-sample_start
        assert underlying.cost.total == underlying.cost.rounds == m
        small, extra = divmod(N, m)
        expected = N if policy == 'random' else sum(N-small*k-min(k, extra) for k in range(m))
        assert underlying.cost.returned_rows == expected
        score = recorder.finish(underlying, trace_path)
        return {**common, 'baseline': policy, 'status': 'complete', 'budget': m,
                'depth': m, 'setup_seconds': setup_seconds, 'sample_seconds': sample_seconds,
                'seconds': perf_counter()-started, 'trace': str(trace_path.relative_to(output)),
                'batch_size_histogram': dict(Counter(map(len, recorder.batches))),
                **score, **asdict(underlying.cost), 'total': underlying.cost.total}
    p = GRID[target][0]
    params = FixedColorings(N, underlying.theta, d=9, beta=BETA,
                            palette_override=p, coloring_count=m)
    oracle = BudgetOracle(underlying, N)
    observer = WeightedObserver(ScreenParameters(params, threshold), oracle)
    repair, stopped = RobustTrace(), None
    try:
        with screen_threshold(threshold):
            result = sample_robust(oracle, params, seeds[1], seeds[2], observer=observer,
                                   commit_observer=recorder, variant=policy, repair_trace=repair)
    except QueryBudgetExceeded as error:
        stopped = error.details
    sample_seconds = perf_counter()-sample_start
    observer.finish_observation(underlying)
    repair_diagnostics = repair.posthoc(underlying)
    if stopped is None:
        score = recorder.finish(underlying, trace_path)
        checked = audit_tree(underlying, params, result, observer)
    else:
        score = {'kl_nats': None, 'kl_per_token': None, 'tv_score': None,
                 'log_q_over_p': None, 'evaluation_seconds': 0.}
        checked = {'unsafe_batches': None, 'all_tokens_committed': False,
                   'fallback': repair.terminal_fallback}
    graph_path = output/'graphs'/(job_name(job)+'.npz') if repeat == 0 else None
    strengths = diagnose(underlying, observer, repair, recorder.batches, graph_path)
    initial = initial_kl_diagnostics(underlying, observer, repair, biased, tail,
                                     target, repeat, recorder.batches, output)
    assert underlying.cost.total <= N
    return {**common, 'variant': policy, 'palette': p, 'colorings': m, 'screen_threshold': threshold,
            'parameters': asdict(params), 'oracle_exact': True, 'all_edge_certificate_claimed': False,
            'status': 'censored' if stopped else 'complete', 'budget_stop': stopped,
            'query_limit': N, 'screen_calls': len(observer.screens),
            'screen_observations': observer.screens,
            'depth': 1+len(observer.screens)+oracle.cost.rounds,
            'committed_tokens': int((recorder.history >= 0).sum()),
            'setup_seconds': setup_seconds, 'sample_seconds': sample_seconds,
            'seconds': perf_counter()-started,
            'repair_diagnostics': repair_diagnostics, 'strength_diagnostics': strengths,
            'initial_kl_diagnostics': initial,
            'trace': str(trace_path.relative_to(output)) if stopped is None else None,
            'graph_snapshot': str(graph_path.relative_to(output)) if graph_path else None,
            'batch_size_histogram': dict(Counter(map(len, recorder.batches))),
            **score, **checked, **asdict(oracle.cost), 'total': oracle.cost.total}


def group_key(row):
    return tuple(row[k] for k in ('target', 'biased', 'weak_tail', 'variant',
                                  'colorings', 'screen_threshold'))


def summarize(proposals):
    groups = defaultdict(list)
    for row in proposals:
        groups[group_key(row)].append(row)
    output = {'complete_settings': [], 'censored_settings': []}
    for key, rows in sorted(groups.items()):
        rows.sort(key=lambda x: x['repeat'])
        assert len(rows) == REPEATS and [r['repeat'] for r in rows] == [0, 1]
        complete = all(r['status'] == 'complete' for r in rows)
        item = {**dict(zip(('target', 'biased', 'weak_tail', 'variant', 'colorings',
                            'screen_threshold'), key)),
                'n': N, 'case': rows[0]['case'], 'palette': rows[0]['palette'],
                'runs': len(rows), 'censored_runs': sum(r['status'] == 'censored' for r in rows),
                'cost': {k: stats([r[k] for r in rows]) for k in
                         ('total', 'counterfactual', 'rounds', 'depth', 'sample_seconds', 'evaluation_seconds')},
                'kl': stats([r['kl_per_token'] for r in rows]) if complete else None,
                'tv': stats([r['tv_score'] for r in rows]) if complete else None,
                'kl_individual': [r['kl_per_token'] for r in rows],
                'tv_individual': [r['tv_score'] for r in rows],
                'repair_tokens': stats([r['repair_diagnostics']['repair_tokens'] for r in rows]),
                'fallbacks': dict(Counter(r['fallback'] or 'none' for r in rows))}
        output['complete_settings' if complete else 'censored_settings'].append(item)
    return output


def match_budgets(summary):
    return [{**{k: row[k] for k in ('target', 'biased', 'weak_tail', 'case', 'variant',
                                     'colorings', 'screen_threshold')},
             'axis': axis, 'proposal_mean': row['cost'][axis]['mean'],
             'baseline_batches': int(np.floor(row['cost'][axis]['mean']+.5))}
            for row in summary['complete_settings'] for axis in ('total', 'depth')]


def compare(proposals, baselines, matches):
    lookup = {tuple(r['job']): r for r in baselines}
    result = []
    for match in matches:
        key = tuple(match[k] for k in ('target', 'biased', 'weak_tail', 'variant',
                                       'colorings', 'screen_threshold'))
        a = sorted([r for r in proposals if group_key(r) == key], key=lambda r: r['repeat'])
        for policy in ('random', 'confidence'):
            b = [lookup[('baseline', match['target'], match['biased'], match['weak_tail'],
                          repeat, policy, match['baseline_batches'], 0.)] for repeat in range(REPEATS)]
            for x, y in zip(a, b):
                for field in ('edges_sha256', 'weights_sha256', 'fields_sha256'):
                    assert x[field] == y[field]
            result.append({**match, 'baseline': policy,
                'proposal_kl': stats([r['kl_per_token'] for r in a]),
                'baseline_kl': stats([r['kl_per_token'] for r in b]),
                'proposal_tv': stats([r['tv_score'] for r in a]),
                'baseline_tv': stats([r['tv_score'] for r in b]),
                'paired_baseline_minus_proposal_kl':
                    [y['kl_per_token']-x['kl_per_token'] for x, y in zip(a, b)]})
    return result


def execute(jobs, path, workers, output, reuse=()):
    rows = read_runs(path)
    wanted, done = set(jobs), {tuple(r['job']) for r in rows}
    if len(done) != len(rows) or not done <= wanted:
        raise ValueError('Please preserve the frozen job list when resuming.')
    with path.open('a') as stream:
        for source in reuse:
            for row in read_runs(source):
                job = tuple(row['job'])
                if job in wanted and job not in done:
                    rows.append(row)
                    stream.write(json.dumps(row, separators=(',', ':'))+'\n')
                    done.add(job)
    pending = [job for job in jobs if job not in done]
    if not pending:
        return rows
    load_backend()
    start = perf_counter()
    with ProcessPoolExecutor(max_workers=workers) as pool, path.open('a') as stream:
        futures = [pool.submit(run_job, job, output) for job in pending]
        for future in as_completed(futures):
            row = future.result()
            rows.append(row)
            stream.write(json.dumps(row, separators=(',', ':'), allow_nan=False)+'\n')
            stream.flush()
            print(f"{path.stem} {len(rows)}/{len(jobs)} {job_name(row['job'])} "
                  f"Q={row['total']} KL/N={row['kl_per_token']} {row['status']} "
                  f"sample={row['sample_seconds']:.2f}s eval={row['evaluation_seconds']:.2f}s "
                  f"elapsed={perf_counter()-start:.1f}s", flush=True)
    execution = path.with_name(path.stem+'_execution.json')
    history = json.loads(execution.read_text()) if execution.exists() else []
    history.append({'new_runs': len(pending), 'workers': workers, 'seconds': perf_counter()-start})
    write_json(execution, history)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', choices=('pilot', 'all', 'proposal', 'baseline'), default='all')
    parser.add_argument('--workers', type=int, default=6)
    parser.add_argument('--output', type=Path, default=OUTPUT)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    jobs = proposal_jobs()
    protocol = {'version': 1, 'n': N, 'repeats': REPEATS, 'sigma': SIGMA,
                'grid': GRID, 'thresholds': THRESHOLDS, 'd': 9,
                'proposal_jobs': [list(j) for j in jobs],
                'variant_design': 'mutual_rank at all M; legacy union_degree control at each family middle M.',
                'conditions': 'Unary bias off/on x prior LogUniform[.1,1]/continuous zero-reaching Beta tail. '
                              'Same canonical-edge uniforms; match realized mean theta separately in every graph. '
                              'theta_reference=.5/maxdegree, unchanged factor 1+theta_e*phi_i*phi_j.',
                'calibration': 'Sigma rounded from DocRED equal-document median initial confidence; '
                               'no fitting to sampler outcomes. Exact oracle, no noise. No weakest-edge certificate.',
                'threshold': 'TV-diameter test only. Preprocessing uses unchanged BETA and bank rule. '
                             'Controller caps, majority vote, peeling, filter, repair and centroid otherwise unchanged.',
                'budget': 'Q=Qpre+Qcf+R<=N, atomic submission families; incomplete settings separately. '
                          'Primary mean Q, median and p90 supplementary; T=1+screens+R. '
                          'Match B=round-half-up(mean Q) and separately mean T.',
                'baselines': 'Current-history max individual-token confidence or random positions; balanced '
                             'batch sizes, stochastic values, no remasking; Q=T=B. Additional anchors B=32,256,2048.',
                'error': 'Primary sum_t KL(product exact marginals || exact target batch marginal | history)/N. '
                         'Exact within each observed history, MC only over generated histories/controller/target seeds. '
                         'Expectation is E_W KL(Q_W||P)/N; mixture KL can be smaller. '
                         'TV density score secondary. Tail collapse is exact for both metrics.',
                'diagnostics': 'Hidden theta and initial edge reverse-KL used after generation only. '
                               'Save all completed trajectories and seed0 graphs. Preserve censored runs.',
                'source_sha256': {name: digest(ROOT/name) for name in SOURCES},
                'data_input_sha256': digest(output/'data_profile_input.json'),
                'data_profile_sha256': digest(output/'data_profile.json')}
    freeze_json(output/'protocol.json', protocol)
    if args.stage == 'pilot':
        selected = [j for j in jobs if j[4] == 0 and j[5] == 'mutual_rank'
                    and j[6] == GRID[j[1]][1][1] and j[7] == .01]
        rows = execute(selected, output/'pilot_proposals.jsonl', min(args.workers, 4), output)
        bj = [('baseline', r['target'], r['biased'], r['weak_tail'], 0, policy, r['total'], 0.)
              for r in rows if r['status'] == 'complete' for policy in ('random', 'confidence')]
        execute(bj, output/'pilot_baselines.jsonl', min(args.workers, 4), output)
        return
    proposals = (read_runs(output/'proposal_runs.jsonl') if args.stage == 'baseline' else
                 execute(jobs, output/'proposal_runs.jsonl', args.workers, output,
                         [output/'pilot_proposals.jsonl']))
    assert {tuple(r['job']) for r in proposals} == set(jobs)
    summary = summarize(proposals)
    matches = match_budgets(summary)
    freeze_json(output/'summary.json', summary)
    freeze_json(output/'matched_budgets.json', matches)
    if args.stage == 'proposal':
        return
    bj = {('baseline', r['target'], r['biased'], r['weak_tail'], repeat, policy,
            r['baseline_batches'], 0.) for r in matches for repeat in range(REPEATS)
            for policy in ('random', 'confidence')}
    bj.update({('baseline', target, bias, tail, repeat, policy, b, 0.)
               for target in GRID for bias in (False, True) for tail in (False, True)
               for repeat in range(REPEATS) for policy in ('random', 'confidence') for b in (32, 256, 2048)})
    baselines = execute(sorted(bj), output/'baseline_runs.jsonl', args.workers, output,
                        [output/'pilot_baselines.jsonl'])
    freeze_json(output/'comparisons.json', compare(proposals, baselines, matches))
    print(f'Finished {len(proposals)} proposals and {len(baselines)} baselines.', flush=True)


if __name__ == '__main__':
    main()
