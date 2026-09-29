"""Confirm fixed-absolute-KL scaling on fresh target and sampler seeds.

All settings are frozen from the exact-oracle phase-1 outcomes before any
confirmation run is evaluated.  For each (tree, N), the study retains a cheap
fixed-threshold frontier setting and a cheap exact-zero setting.  The absolute
threshold for a tree is 1e-3 times its phase-1 L0 at N=2048 and is unchanged
across N and confirmation seeds.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
import fcntl
import json
import os
from pathlib import Path
import shutil
from time import perf_counter
import traceback

import numpy as np

import row_cap_grid_study as grid
import standard_tree_study as standard
import strong_path_baseline_study as controls
import strong_path_pivot_study as pivot
import sublinear_pilot_study as phase1
from forest_kl import initial_edges, load_backend as load_forest_backend
from minimal_oracle import load_backend as load_oracle_backend
from profile_minimal import weighted_summary
from validate import digest, freeze_json, read_runs


ROOT = Path(__file__).resolve().parent
PHASE1 = ROOT/'results'/'sublinear_pilot_study'
OUTPUT = ROOT/'results'/'fixed_accuracy_confirmation'
CASE = 'fixed_absolute_kl_fresh_seed_confirmation'
TARGETS = phase1.TARGETS
N_GRID = phase1.N_GRID
DATA_REPEATS = (171, 172, 173)
ALGORITHM_REPEATS = (271, 272)
THRESHOLD_FRACTION = 1e-3
ROLES = ('frontier', 'exact')
SOURCES = tuple(dict.fromkeys((*standard.SOURCES, 'sublinear_pilot_study.py',
    'fixed_accuracy_confirmation.py', 'report_fixed_accuracy_confirmation.py',
    'test_fixed_accuracy_confirmation.py')))


def load_json(path):
    return json.loads(Path(path).read_text())


def phase1_inputs():
    required = ('design.json', 'target_profiles.json', 'proposal_plan.json',
                'proposal_runs.jsonl', 'comparisons.json', 'audit.json')
    missing = [name for name in required if not (PHASE1/name).exists()]
    if missing:
        raise FileNotFoundError(f'Please complete phase 1 first: {missing}')
    return {name: digest(PHASE1/name) for name in required}


def thresholds_from_phase1():
    profiles = load_json(PHASE1/'target_profiles.json')
    base_n = min(row['n'] for row in profiles)
    thresholds = {}
    for target in TARGETS:
        profile = next(row for row in profiles
                       if row['target'] == target and row['n'] == base_n)
        thresholds[target] = THRESHOLD_FRACTION*profile['L0_total']
    return base_n, thresholds


def stages_for(key, plan):
    return sorted({origin['stage'] for origin in plan[key]['origins']})


def exact_zero(row):
    return (row['status'] == 'complete' and row['kl_nats'] == 0.
            and row.get('positive_kl_batches') == 0
            and row.get('kl_mc_se_per_token', 0.) == 0.)


def censored_cost(row):
    stop = row.get('budget_stop') or {}
    return (stop.get('completion_query_lower_bound', float('inf')),
            row['total'], tuple(row['study_job']['setting']))


def select_settings(thresholds):
    """Freeze both roles using phase-1 proposal outcomes and no random scores."""
    comparisons = load_json(PHASE1/'comparisons.json')
    raw_rows = read_runs(PHASE1/'proposal_runs.jsonl')
    raw = {controls.job_key(row['study_job']): row for row in raw_rows}
    plan = load_json(PHASE1/'proposal_plan.json')['jobs']
    selected = {}
    for target in TARGETS:
        for n in N_GRID:
            local = [row for row in comparisons
                     if row['target'] == target and row['n'] == n]
            complete = [row for row in local if row['status'] == 'complete']
            eligible = [row for row in complete
                        if row['KL_total'] <= thresholds[target]]
            zeros = [row for row in complete if exact_zero(raw[row['proposal_job_key']])]

            def choose(role):
                pool = eligible if role == 'frontier' else zeros
                if pool:
                    row = min(pool, key=lambda x: (x['Q'], x['KL_total'],
                                                   x['p'], x['M'], x['d'], x['lambda']))
                    reason = ('minimum Q attaining frozen K threshold' if role == 'frontier'
                              else 'minimum Q attaining structural exact zero')
                    attained = True
                elif complete:
                    row = min(complete, key=lambda x: (x['KL_total'], x['Q'],
                                                       x['p'], x['M'], x['d'], x['lambda']))
                    reason = f'{role} unattained; minimum phase-1 K fallback'
                    attained = False
                else:
                    raw_local = [raw[row['proposal_job_key']] for row in local]
                    chosen_raw = min(raw_local, key=censored_cost)
                    key = controls.job_key(chosen_raw['study_job'])
                    row = next(item for item in local if item['proposal_job_key'] == key)
                    reason = f'{role} unattained; lowest completion-cost censor fallback'
                    attained = False
                return {'setting': list(raw[row['proposal_job_key']]['study_job']['setting']),
                        'phase1_job_key': row['proposal_job_key'],
                        'phase1_status': row['status'], 'phase1_Q': row['Q'],
                        'phase1_K': row['KL_total'], 'phase1_rho': row['relative_KL'],
                        'phase1_attained_role': attained, 'reason': reason,
                        'phase1_stages': stages_for(row['proposal_job_key'], plan)}

            selected[f'{target}|{n}'] = {
                'target': target, 'n': n, 'K_threshold': thresholds[target],
                'frontier': choose('frontier'), 'exact': choose('exact')}
    return selected


def design(smoke=False):
    base_n, thresholds = thresholds_from_phase1()
    data = DATA_REPEATS[:1] if smoke else DATA_REPEATS
    algorithms = ALGORITHM_REPEATS[:1] if smoke else ALGORITHM_REPEATS
    return {'version': 1, 'study': CASE, 'smoke': smoke,
        'targets': list(TARGETS), 'n_grid': list(N_GRID[:2] if smoke else N_GRID),
        'data_repeats': list(data), 'algorithm_repeats': list(algorithms),
        'pairs': [[d, a] for d in data for a in algorithms],
        'oracle': 'exact', 'edge_law': 'constant', 'query_cap': 'Q<=N',
        'accuracy': {
            'rule': 'Per tree K_star=1e-3*phase1 L0_total at N=2048; K_star is absolute and fixed across N and fresh seeds.',
            'base_n': base_n, 'fraction': THRESHOLD_FRACTION,
            'K_thresholds': thresholds,
            'primary_success': 'complete and K+2*conditional_MC_SE_total <= K_star',
            'secondary': 'raw K<=K_star and structural exact-zero rates'},
        'roles': {
            'frontier': 'Minimum phase-1 Q attaining K_star; otherwise best available frozen fallback.',
            'exact': 'Minimum phase-1 Q with structural exact zero; otherwise best available frozen fallback.'},
        'selection': 'Uses phase-1 proposal outcomes only. Frozen before all fresh-seed outcomes; no confirmation retuning.',
        'fields': 'Within each fresh data repeat, one Uniform[-1,1] master prefix is shared across targets and N.',
        'claim_gate': 'Fit a descriptive log-log slope only over N with 6/6 conservative threshold successes. Report failures without imputation.',
        'phase_boundary': 'Stop after fixed-accuracy confirmation; do not start Beta-tail or noisy-oracle experiments.',
        'phase1_inputs_sha256': phase1_inputs(),
        'source_sha256': {name: digest(ROOT/name) for name in SOURCES}}


def confirmation_job(config, target, n, setting, data, algorithm):
    return {'kind': 'proposal', 'target': target, 'n': int(n),
            'data': int(data), 'algorithm': int(algorithm), 'setting': list(setting),
            'evaluation_samples': (32 if config['smoke'] else phase1.EVALUATION_SAMPLES),
            'evaluation_exact_arity': phase1.EVALUATION_EXACT_ARITY}


def make_jobs(config, selection):
    jobs = {}
    role_map = defaultdict(list)
    for cell, item in selection.items():
        if item['n'] not in config['n_grid']:
            continue
        for role in ROLES:
            setting = item[role]['setting']
            setting_key = json.dumps(setting, separators=(',', ':'))
            role_map[(item['target'], item['n'], setting_key)].append(role)
            for data, algorithm in config['pairs']:
                job = confirmation_job(config, item['target'], item['n'], setting,
                                       data, algorithm)
                jobs[controls.job_key(job)] = job
    return sorted(jobs.values(), key=controls.job_key), role_map


def run_one(job, output):
    row = phase1.run_one(job, output)
    row['confirmation_study'] = CASE
    return row


def atomic_json(path, value):
    grid.atomic_json(Path(path), value)


def ensure_profiles(out, config, jobs):
    directory = out/'target_profiles'
    directory.mkdir(exist_ok=True)
    profiles = []
    cells = sorted({(job['target'], job['n'], job['data']) for job in jobs})
    algorithms_by_cell = defaultdict(set)
    for job in jobs:
        algorithms_by_cell[(job['target'], job['n'], job['data'])].add(job['algorithm'])
    for target, n, data in cells:
        algorithm = min(algorithms_by_cell[(target, n, data)])
        repeat = pivot.repeat_id(data, algorithm)
        oracle, seeds = phase1.make_target(target, n, repeat)
        rows, weights, total = initial_edges(oracle)
        arrays = {'edges': oracle.edges, 'theta': oracle.edge_strengths,
                  'fields': oracle.fields, 'initial_rows': rows,
                  'initial_edge_kl': weights}
        snapshot = directory/f'{target}_N{n}_data{data}.npz'
        if snapshot.exists():
            with np.load(snapshot) as saved:
                for name, values in arrays.items():
                    np.testing.assert_array_equal(saved[name], values)
        else:
            np.savez_compressed(snapshot, **arrays)
        profiles.append({'target': target, 'n': n, 'data_repeat': data,
            'field_seed': oracle.field_seed,
            'fields_sha256': controls.array_hash(oracle.fields, '<f8'),
            'theta': oracle.theta, 'maximum_degree': oracle.max_degree,
            'edge_count': len(oracle.edges), 'L0_total': float(total),
            'L0_per_token': float(total/n), 'edge_KL': weighted_summary([weights]),
            'snapshot': str(snapshot.relative_to(out)), 'sha256': digest(snapshot)})
        for sampler_algorithm in algorithms_by_cell[(target, n, data)]:
            full_repeat = pivot.repeat_id(data, sampler_algorithm)
            legacy = (out/'artifacts'/target/f'N{n}'/'target_profiles'/
                      f'{target}_{standard.CASE}_seed{full_repeat}.npz')
            legacy.parent.mkdir(parents=True, exist_ok=True)
            if legacy.exists():
                with np.load(legacy) as saved:
                    for name, values in arrays.items():
                        np.testing.assert_array_equal(saved[name], values)
            else:
                np.savez_compressed(legacy, **arrays)
    # Please verify public-position pairing independently for each fresh target seed.
    for data in config['data_repeats']:
        master = np.random.default_rng(phase1.master_field_seed(data)).uniform(
            -1., 1., max(config['n_grid']))
        for item in profiles:
            if item['data_repeat'] != data:
                continue
            with np.load(out/item['snapshot']) as saved:
                np.testing.assert_array_equal(saved['fields'], master[:item['n']])
    freeze_json(out/'target_profiles.json', profiles)
    return profiles


def execute(out, config, jobs, workers, state):
    freeze_json(out/'jobs.json', jobs)
    path = out/'runs.jsonl'
    rows = read_runs(path)
    done = {controls.job_key(row['study_job']): row for row in rows}
    if len(done) != len(rows):
        raise ValueError('Please remove duplicate confirmation rows before resuming.')
    wanted = {controls.job_key(job) for job in jobs}
    if not set(done) <= wanted:
        raise ValueError('The frozen confirmation job list changed.')
    pending = [job for job in jobs if controls.job_key(job) not in done]
    state.update(stage='confirmation', stage_jobs=len(jobs),
                 stage_finished=len(jobs)-len(pending), updated_utc=grid.utc())
    atomic_json(out/'status.json', state)
    started = perf_counter()
    if pending:
        with ProcessPoolExecutor(max_workers=workers) as pool, path.open('a') as stream:
            futures = [pool.submit(run_one, job,
                        out/'artifacts'/job['target']/f'N{job["n"]}') for job in pending]
            for future in as_completed(futures):
                row = future.result()
                rows.append(row)
                stream.write(json.dumps(row, separators=(',', ':'), allow_nan=False)+'\n')
                stream.flush()
                state['stage_finished'] += 1
                state['updated_utc'] = grid.utc()
                atomic_json(out/'status.json', state)
                if state['stage_finished'] % 10 == 0 or state['stage_finished'] == len(jobs):
                    print(f'confirmation {state["stage_finished"]}/{len(jobs)} '
                          f'{row["target"]} N={row["n"]} Q={row["total"]} '
                          f'K={row.get("kl_nats")} {row["status"]}', flush=True)
    # Please append a small execution ledger so an interrupted run can resume
    # without pretending that its final, zero-pending invocation was the first.
    execution_path = out/'execution.json'
    history = load_json(execution_path) if execution_path.exists() else []
    history.append({'requested_jobs': len(jobs), 'new_runs': len(pending),
                    'workers': workers, 'seconds': perf_counter()-started,
                    'finished_utc': grid.utc()})
    atomic_json(execution_path, history)
    lookup = {controls.job_key(row['study_job']): row for row in rows}
    return [lookup[controls.job_key(job)] for job in jobs]


def expand_results(rows, selection, profiles):
    profile = {(row['target'], row['n'], row['data_repeat']): row for row in profiles}
    records = []
    for row in rows:
        cell = selection[f'{row["target"]}|{row["n"]}']
        setting = json.dumps(row['study_job']['setting'], separators=(',', ':'))
        roles = [role for role in ROLES
                 if json.dumps(cell[role]['setting'], separators=(',', ':')) == setting]
        p = profile[(row['target'], row['n'], row['data_repeat'])]
        complete = row['status'] == 'complete'
        k = float(row['kl_nats']) if complete else None
        se_total = float(row.get('kl_mc_se_per_token', 0.)*row['n']) if complete else None
        threshold = cell['K_threshold']
        for role in roles:
            records.append({'target': row['target'], 'n': row['n'], 'role': role,
                'data_repeat': row['data_repeat'],
                'algorithm_repeat': row['algorithm_repeat'],
                'setting': row['study_job']['setting'], 'status': row['status'],
                'Q': row['total'], 'Q_over_N': row['total']/row['n'],
                'K': k, 'K_mc_se': se_total,
                'K_upper': k+2*se_total if complete else None,
                'KL_per_token': row['kl_per_token'] if complete else None,
                'rho': k/p['L0_total'] if complete else None,
                'K_threshold': threshold,
                'threshold_success_raw': bool(complete and k <= threshold),
                'threshold_success_conservative': bool(
                    complete and k+2*se_total <= threshold),
                'exact_zero': bool(complete and exact_zero(row)),
                'committed_fraction': row.get('committed_tokens', 0)/row['n'],
                'abort_stage': (row.get('budget_stop') or {}).get('stage'),
                'job_key': controls.job_key(row['study_job'])})
    return records


def aggregate(records, config):
    groups = defaultdict(list)
    for row in records:
        groups[(row['target'], row['n'], row['role'])].append(row)
    expected = len(config['pairs'])
    summary = []
    for (target, n, role), local in sorted(groups.items()):
        if len(local) != expected:
            raise AssertionError('Every frozen role must have all fresh seed pairs.')
        successful = [row for row in local if row['threshold_success_conservative']]
        complete = [row for row in local if row['status'] == 'complete']
        qs = np.asarray([row['Q'] for row in local], dtype=float)
        success_q = np.asarray([row['Q'] for row in successful], dtype=float)
        summary.append({'target': target, 'n': n, 'role': role,
            'runs': len(local), 'complete': len(complete),
            'threshold_success_raw': sum(row['threshold_success_raw'] for row in local),
            'threshold_success_conservative': len(successful),
            'exact_zero': sum(row['exact_zero'] for row in local),
            'K_threshold': local[0]['K_threshold'],
            'mean_Q_spent': float(qs.mean()),
            'mean_Q_success': float(success_q.mean()) if len(success_q) else None,
            'mean_Q_confirmed': float(qs.mean()) if len(successful) == expected else None,
            'Q_se_confirmed': (float(qs.std(ddof=1)/np.sqrt(len(qs)))
                               if len(successful) == expected and len(qs) > 1 else None),
            'mean_Q_over_N_confirmed': (float(qs.mean()/n)
                                        if len(successful) == expected else None),
            'maximum_K_upper': max((row['K_upper'] for row in complete), default=None),
            'selection': None})
    return summary


def slopes(summary):
    result = []
    for target in TARGETS:
        for role in ROLES:
            points = [(row['n'], row['mean_Q_confirmed']) for row in summary
                      if row['target'] == target and row['role'] == role
                      and row['mean_Q_confirmed'] is not None]
            if len(points) >= 3:
                exponent, intercept = np.polyfit(
                    np.log([x for x, _ in points]), np.log([y for _, y in points]), 1)
                endpoint = (np.log(points[-1][1]/points[0][1])/
                            np.log(points[-1][0]/points[0][0]))
                exponent, intercept, endpoint = map(float, (exponent, intercept, endpoint))
            else:
                exponent = intercept = endpoint = None
            result.append({'target': target, 'role': role, 'confirmed_points': len(points),
                'points': [[int(x), float(y)] for x, y in points],
                'OLS_exponent': exponent, 'OLS_intercept': intercept,
                'endpoint_exponent': endpoint,
                'claim': ('descriptive fresh-seed fixed-accuracy slope' if len(points) >= 3
                          else 'insufficient 6/6-success points')})
    return result


def audit(out, config, selection, rows, records, profiles):
    for row in rows:
        assert row['total'] <= row['n']
        assert row['data_repeat'] in config['data_repeats']
        assert row['algorithm_repeat'] in config['algorithm_repeats']
        if row['status'] == 'censored':
            assert row['kl_nats'] is None and row['budget_stop'] is not None
        else:
            assert row['kl_nats'] is not None
    for target in TARGETS:
        values = {selection[f'{target}|{n}']['K_threshold'] for n in config['n_grid']}
        assert len(values) == 1
    result = {'jobs': len(rows), 'expanded_role_records': len(records),
        'profiles': len(profiles), 'fresh_data_repeats': config['data_repeats'],
        'fresh_algorithm_repeats': config['algorithm_repeats'],
        'settings_frozen_from_phase1_only': True,
        'confirmation_reselection': False, 'absolute_threshold_fixed_across_N': True,
        'query_caps_verified': True, 'phase2_started': False}
    freeze_json(out/'audit.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=8)
    parser.add_argument('--output', type=Path, default=OUTPUT)
    parser.add_argument('--smoke', action='store_true')
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('Please use at least one worker.')
    config = design(args.smoke)
    selection = select_settings(config['accuracy']['K_thresholds'])
    jobs, role_map = make_jobs(config, selection)
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    with (out/'runner.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        freeze_json(out/'design.json', config)
        freeze_json(out/'selection.json', selection)
        freeze_json(out/'role_map.json', {'entries': [
            {'target': target, 'n': n, 'setting_json': setting, 'roles': roles}
            for (target, n, setting), roles in sorted(role_map.items())]})
        sources = out/'sources'
        sources.mkdir(exist_ok=True)
        for name, checksum in config['source_sha256'].items():
            destination = sources/name
            if not destination.exists():
                shutil.copyfile(ROOT/name, destination)
            assert digest(destination) == checksum
        if args.prepare_only:
            atomic_json(out/'status.json', {'status': 'prepared', 'stage': 'prepared',
                'jobs': len(jobs), 'output': str(out), 'updated_utc': grid.utc()})
            return
        started = perf_counter()
        state = {'status': 'running', 'stage': 'profiles', 'pid': os.getpid(),
                 'workers': args.workers, 'output': str(out),
                 'started_utc': grid.utc()}
        atomic_json(out/'status.json', state)
        try:
            load_oracle_backend()
            load_forest_backend()
            profiles = ensure_profiles(out, config, jobs)
            rows = execute(out, config, jobs, args.workers, state)
            records = expand_results(rows, selection, profiles)
            summary = aggregate(records, config)
            for item in summary:
                item['selection'] = selection[f'{item["target"]}|{item["n"]}'][item['role']]
            slope_rows = slopes(summary)
            atomic_json(out/'records.json', records)
            atomic_json(out/'summary.json', summary)
            atomic_json(out/'slopes.json', slope_rows)
            audit(out, config, selection, rows, records, profiles)
            from report_fixed_accuracy_confirmation import report
            report(out)
            for name, checksum in config['source_sha256'].items():
                assert digest(ROOT/name) == checksum
            state.update(status='complete', stage='fixed_accuracy_complete_stop',
                         finished_utc=grid.utc(), seconds=perf_counter()-started,
                         confirmed_cells=sum(row['mean_Q_confirmed'] is not None
                                             for row in summary),
                         phase2_started=False)
            atomic_json(out/'status.json', state)
            print(json.dumps(state, indent=2), flush=True)
        except BaseException as error:
            state.update(status='failed', error=repr(error),
                         traceback=traceback.format_exc(), updated_utc=grid.utc(),
                         seconds=perf_counter()-started)
            atomic_json(out/'status.json', state)
            raise


if __name__ == '__main__':
    main()
