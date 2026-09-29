"""Check the strong-path pivot with separate target and sampler repeat IDs.

Please run this adapter in its own process. The target law, oracle, sampler,
query accounting, and previous experiment files are kept unchanged.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path
import shutil
from time import perf_counter
import traceback

import numpy as np

import explore_minimal as base
import minimal_study
import row_cap_grid_study as grid
import strong_path_study as strong
from draft_policy import draft_policy, save_capture
from minimal_oracle import load_backend
from profile_minimal import initial_edges, weighted_summary
from robustness_study import seeds_for
from row_cap_variants import row_cap_policy, save_votes
from validate import digest, freeze_json, read_runs


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT/'results'/'strong_path_pivot_study'
PIVOT = ('path', 8, 53, 18, .001)
RADIX = 1000000
BASE_TARGET = strong.make_target
BASE_RUN = base.run_job
SOURCES = tuple(dict.fromkeys((*strong.SOURCES, 'strong_path_pivot_study.py',
                             'report_strong_path_pivot.py', 'test_strong_path_pivot.py')))


def repeat_id(data_repeat, algorithm_repeat):
    if not (isinstance(data_repeat, int) and isinstance(algorithm_repeat, int)
            and 0 <= data_repeat < RADIX and 0 <= algorithm_repeat < RADIX):
        raise ValueError('Please use nonnegative repeat IDs smaller than one million.')
    return data_repeat*RADIX+algorithm_repeat


def seed_pair(repeat):
    data, algorithm = divmod(int(repeat), RADIX)
    if repeat_id(data, algorithm) != repeat:
        raise ValueError('Please use a valid encoded repeat ID.')
    return data, algorithm


def make_target(target, n, repeat, biased=True, weak_tail=False, sigma=None,
                kind='proposal', budget=0):
    data, algorithm = seed_pair(repeat)
    oracle, data_seeds = BASE_TARGET(target, n, data, kind=kind, budget=budget)
    sampler_seeds = seeds_for(target, n, algorithm, kind, budget)
    return oracle, [data_seeds[0], *sampler_seeds[1:]]


def tag(row):
    strong.tag(row)
    data, algorithm = seed_pair(row['repeat'])
    row.update(data_repeat=data, algorithm_repeat=algorithm,
               graph_seed=row['seeds'][0], controller_seed=row['seeds'][1],
               commit_seed=row['seeds'][2], seed_design='separate target and algorithm repeat IDs')
    return row


@contextmanager
def target_context():
    saved = base.make_target, minimal_study.case_name
    base.make_target = make_target
    minimal_study.case_name = lambda *_: strong.CASE
    try:
        yield
    finally:
        base.make_target, minimal_study.case_name = saved


def ensure_profiles(jobs, output):
    profiles, cache = [], {}
    for target, n, repeat in sorted({(j[1], j[2], j[3]) for j in jobs}):
        data, algorithm = seed_pair(repeat)
        oracle, seeds = make_target(target, n, repeat)
        key = target, n, data
        if key not in cache:
            cache[key] = initial_edges(oracle)
        rows, weights, total = cache[key]
        path = output/'target_profiles'/f'{target}_{strong.CASE}_seed{repeat}.npz'
        path.parent.mkdir(parents=True, exist_ok=True)
        arrays = dict(edges=oracle.edges, theta=oracle.edge_strengths, fields=oracle.fields,
                      initial_rows=rows, initial_edge_kl=weights)
        if path.exists():
            with np.load(path) as saved:
                for name, values in arrays.items():
                    np.testing.assert_array_equal(saved[name], values)
        else:
            np.savez_compressed(path, **arrays)
        profiles.append({'target': target, 'target_law': strong.CASE, 'n': n,
            'repeat': repeat, 'data_repeat': data, 'algorithm_repeat': algorithm,
            'seeds': seeds, 'field_seed': oracle.field_seed,
            'all_at_once_kl_per_token': total/n,
            'confidence': weighted_summary([rows[:, :2].max(axis=1)]),
            'edge_kl': weighted_summary([weights]),
            'snapshot': str(path.relative_to(output)), 'sha256': digest(path)})
    freeze_json(output/'target_profiles.json', profiles)


def run_proposal(job, output, variant, full_votes=False):
    with target_context(), row_cap_policy(grid.POLICIES[variant]) as votes, draft_policy('first_bank') as capture:
        row = BASE_RUN(job, output)
    row.update(study_variant=variant, row_cap_policy=grid.POLICIES[variant],
               draft_policy='first_bank', chunks=1,
               draft_metadata=save_capture(capture, output, base.job_name(job)),
               first_screen_raw_sha256=grid.first_screen_hash(votes[0]) if votes else None,
               vote_metadata=save_votes(votes, output, base.job_name(job)) if full_votes else [],
               full_votes_saved=full_votes)
    return tag(row)


def run_baseline(job, output):
    if job[0] != 'baseline':
        raise ValueError('Please use the proposal adapter for sampler jobs.')
    with target_context():
        return tag(BASE_RUN(job, output))


@contextmanager
def runner_context():
    saved = base.ensure_profiles, grid.run_proposal
    base.ensure_profiles, grid.run_proposal = ensure_profiles, run_proposal
    try:
        yield
    finally:
        base.ensure_profiles, grid.run_proposal = saved


def settings(smoke=False):
    if smoke:
        return [('path', 3, 9, 9, .001), ('path', 6, 9, 18, .001)]
    chosen = {('path', p, m, 18, .001)
              for p in (7, 8, 9) for m in (41, 45, 49, 53, 57, 61)}
    chosen.update(('path', p, 53, 18, .001) for p in (6, 10))
    chosen.update(('path', 8, 53, d, .001) for d in (9, 12, 24, 36))
    chosen.update(('path', 8, m, 18, tau)
                  for m in (45, 53, 61) for tau in (.0003, .003, .01, .03))
    return sorted(chosen)


def design(smoke=False):
    pivot = settings(True)[1] if smoke else PIVOT
    pivot_pairs = [(100, 200), (100, 201)] if smoke else [
        (data, algorithm) for data in range(100, 105) for algorithm in (200, 201)]
    fixed = settings(True) if smoke else [PIVOT, ('path', 8, 45, 18, .001),
        ('path', 7, 53, 18, .001), ('path', 9, 53, 18, .001),
        ('path', 8, 53, 9, .001), ('path', 8, 53, 18, .03)]
    return {'version': 1, 'n': 1024 if smoke else strong.N, 'smoke': smoke,
        'pivot': pivot, 'settings': settings(smoke), 'fixed_confirmation': fixed,
        'pivot_seeds': [repeat_id(*p) for p in pivot_pairs],
        'explore_seeds': [repeat_id(110, 210)] if smoke else [repeat_id(110, 210), repeat_id(111, 211)],
        'confirm_seeds': [repeat_id(120, 220), repeat_id(121, 221)],
        'seed_encoding': {'radix': RADIX, 'rule': 'repeat = radix * data_repeat + algorithm_repeat'},
        'seed_roles': {
            'data': 'Random path relabeling and iid Uniform[-1,1] unary fields. Theta is always 0.25.',
            'algorithm': 'Proposal colorings and sampled commit values. Baseline order/tie-breaking and values; baseline RNG also depends on batch budget.',
            'pairing': 'Same target within each data repeat for every algorithm repeat, policy and budget. Same initial proposal RNG within each algorithm repeat across targets and hyperparameters.',
            'inference': 'The 10 pivot runs form 5 targets x 2 algorithm repeats, not 10 independent target draws. Report descriptive per-target and crossed results without iid confidence intervals.'},
        'target_law': strong.CASE, 'theta': .25, 'fields': 'iid Uniform[-1,1]',
        'draft': 'first_bank', 'J': 1, 'variants': grid.POLICIES,
        'selection': 'Always retain six fixed controls. For EACH policy additionally retain the minimum mean Q setting with all exploratory runs complete and mean KL/token <=1e-6 or <=1e-12. Tie by mean KL and setting. Maximum ten confirmation settings. No baseline results enter selection.',
        'baseline_scope': 'Pivot and frozen confirmation settings only, using rounded cohort mean total Q and separately mean T; matched target/algorithm repeat pairs and balanced random/confidence sampling.',
        'budget': 'Only per-run Q<=N. Censored rows remain separate with no imputed KL; internal round-cap fallback is reported separately.',
        'source_sha256': {name: digest(ROOT/name) for name in SOURCES}}


def select(records, config):
    from report_row_cap_grid import aggregate
    chosen = {tuple(setting): ['fixed_control'] for setting in config['fixed_confirmation']}
    for variant, rows in records.items():
        groups = aggregate(rows)
        for epsilon in (1e-6, 1e-12):
            eligible = [r for r in groups if not r['censored'] and r['KL'] <= epsilon]
            if eligible:
                row = min(eligible, key=lambda r: (r['Q'], r['KL'], tuple(r['key'])))
                chosen.setdefault(tuple(row['key']), []).append(f'{variant}_min_mean_Q_KL_le_{epsilon:g}')
    return {'rule': config['selection'], 'settings': sorted(chosen),
            'reasons': [{'setting': key, 'reasons': value} for key, value in sorted(chosen.items())]}


def baselines(out, config, records, seeds, phase, workers, state):
    stage = out/phase
    jobs, matches = set(), {}
    for variant in grid.POLICIES:
        matches[variant] = json.loads((stage/variant/'matched_budgets.json').read_text())
        jobs.update(('baseline', r['target'], config['n'], seed, policy, 0,
                     r['baseline_batches'], 0, 0.)
                    for r in matches[variant] for seed in seeds for policy in ('random', 'confidence'))
    local = stage/'baselines'
    local.mkdir(exist_ok=True)
    jobs = sorted(jobs)
    freeze_json(local/'jobs.json', jobs)
    path = local/'baseline_runs.jsonl'
    rows = read_runs(path)
    done = {tuple(r['job']) for r in rows}
    assert len(done) == len(rows) and done <= set(jobs)
    state.update(stage=phase+'_baselines', stage_jobs=len(jobs), stage_finished=len(rows), updated_utc=grid.utc())
    grid.atomic_json(out/'status.json', state)
    with ProcessPoolExecutor(max_workers=workers) as pool, path.open('a') as stream:
        futures = [pool.submit(run_baseline, job, local) for job in jobs if job not in done]
        for future in as_completed(futures):
            row = future.result()
            rows.append(row)
            stream.write(json.dumps(row, separators=(',', ':'), allow_nan=False)+'\n')
            stream.flush()
            state.update(stage_finished=len(rows), updated_utc=grid.utc())
            grid.atomic_json(out/'status.json', state)
            if len(rows) % 10 == 0 or len(rows) == len(jobs):
                print(f'{phase} baselines {len(rows)}/{len(jobs)}', flush=True)
    for variant in grid.POLICIES:
        freeze_json(stage/variant/'comparisons.json', base.compare(records[variant], rows, matches[variant], seeds))
    return rows


def audit(out, cohorts, baselines_by_phase):
    """Please validate seed isolation and saved cost/trajectory accounting."""
    targets, streams, counts = {}, {}, {}
    for phase, records in cohorts.items():
        groups = {**records, 'baselines': baselines_by_phase.get(phase, [])}
        for variant, rows in groups.items():
            local = out/phase/variant
            checked = censored = 0
            for row in rows:
                data, algorithm = seed_pair(row['repeat'])
                assert (data, algorithm) == (row['data_repeat'], row['algorithm_repeat'])
                target_key = row['n'], data
                target_hashes = tuple(row[k] for k in ('edges_sha256', 'weights_sha256', 'fields_sha256'))
                assert targets.setdefault(target_key, target_hashes) == target_hashes
                stream_key = row['n'], algorithm, row['kind'], row.get('budget', 0)
                assert streams.setdefault(stream_key, row['seeds'][1:]) == row['seeds'][1:]
                assert row['seeds'][1:] == seeds_for('path', row['n'], algorithm, row['kind'], row.get('budget', 0))[1:]
                assert row['total'] == row['preprocessing']+row['counterfactual']+row['rounds'] <= row['n']
                if row['kind'] == 'proposal':
                    assert row['depth'] == 1+row['screen_calls']+row['rounds']
                    assert sum(s['counterfactual'] for s in row['screen_observations']) == row['counterfactual']
                    assert sum(row['repair_diagnostics']['roles'].values()) == row['rounds']
                if row['status'] != 'complete':
                    assert row['kl_per_token'] is row['trace'] is None
                    assert row['budget_stop']['spent'] == row['total']
                    assert row['total']+row['budget_stop']['next_submission_queries'] > row['n']
                    censored += 1
                    continue
                with np.load(local/row['trace']) as saved:
                    steps, values, kl = (saved[k] for k in ('commit_step', 'values', 'batch_kl'))
                    assert steps.shape == values.shape == (row['n'],)
                    assert (values >= 0).all() and (values < 2048).all()
                    assert set(steps) == set(range(row['rounds']))
                    sizes = np.bincount(steps)
                    assert len(kl) == row['rounds'] and np.isfinite(kl).all() and (kl >= 0).all()
                    assert abs(float(np.sum(kl))/row['n']-row['kl_per_token']) < 1e-14
                    assert (kl[sizes == 1] == 0).all()
                    if row['kind'] == 'baseline':
                        small, extra = divmod(row['n'], row['budget'])
                        np.testing.assert_array_equal(sizes, [small+(i < extra) for i in range(row['budget'])])
                checked += 1
            counts[phase+'/'+variant] = {'completed_traces': checked, 'censored': censored}
    result = {'target_hashes_consistent': True, 'algorithm_streams_independent_of_target': True,
              'distinct_targets': len(targets), 'counts': counts}
    freeze_json(out/'audit.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=6)
    parser.add_argument('--output', type=Path, default=OUTPUT)
    parser.add_argument('--smoke', action='store_true')
    parser.add_argument('--plan-only', action='store_true')
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('Please use at least one worker.')
    config = design(args.smoke)
    if args.plan_only:
        print(json.dumps(config, indent=2))
        return
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    with (out/'runner.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        freeze_json(out/'design.json', config)
        source_dir = out/'sources'
        source_dir.mkdir(exist_ok=True)
        for name, checksum in config['source_sha256'].items():
            destination = source_dir/name
            if not destination.exists():
                shutil.copyfile(ROOT/name, destination)
            assert digest(destination) == checksum
        state = {'status': 'running', 'stage': 'preparing', 'pid': os.getpid(),
                 'workers': args.workers, 'started_utc': grid.utc(), 'output': str(out)}
        grid.atomic_json(out/'status.json', state)
        started = perf_counter()
        try:
            load_backend()
            with runner_context():
                pivot = grid.execute_proposals(out, config, [config['pivot']], config['pivot_seeds'], 'pivot', args.workers, state)
                exploratory = grid.execute_proposals(out, config, config['settings'], config['explore_seeds'], 'explore', args.workers, state)
                selection = select(exploratory, config)
                freeze_json(out/'selection.json', selection)
                confirmed = grid.execute_proposals(out, config, selection['settings'], config['confirm_seeds'], 'confirm', args.workers, state)
            pivot_baselines = baselines(out, config, pivot, config['pivot_seeds'], 'pivot', args.workers, state)
            confirm_baselines = baselines(out, config, confirmed, config['confirm_seeds'], 'confirm', args.workers, state)
            state.update(stage='audit_and_reporting', updated_utc=grid.utc())
            grid.atomic_json(out/'status.json', state)
            cohorts = {'pivot': pivot, 'explore': exploratory, 'confirm': confirmed}
            audit(out, cohorts, {'pivot': pivot_baselines, 'confirm': confirm_baselines})
            from report_strong_path_pivot import report
            report(out)
            assert {name: digest(ROOT/name) for name in SOURCES} == config['source_sha256']
            state.update(status='complete', stage='complete', finished_utc=grid.utc(), seconds=perf_counter()-started,
                         proposal_runs=sum(len(rows) for records in cohorts.values() for rows in records.values()),
                         baseline_runs=len(pivot_baselines)+len(confirm_baselines),
                         confirmation_settings=len(selection['settings']))
            freeze_json(out/'execution.json', state)
        except BaseException:
            state.update(status='failed', failed_utc=grid.utc(), traceback=traceback.format_exc())
            raise
        finally:
            grid.atomic_json(out/'status.json', state)
        print(json.dumps(state), flush=True)


if __name__ == '__main__':
    main()
