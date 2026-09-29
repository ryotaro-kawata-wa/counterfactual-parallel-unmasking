"""Retune failed fixed-accuracy cells, then confirm on untouched seeds.

The screen deliberately uses the hardest previously observed seed pair for
each failed cell.  Eight diverse candidates per cell are then evaluated on all
six development pairs.  The final per-cell setting is frozen before any of the
fresh confirmation pairs are run.
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

import fixed_accuracy_confirmation as fixed
import row_cap_grid_study as grid
import strong_path_baseline_study as controls
import strong_path_pivot_study as pivot
import sublinear_pilot_study as phase1
from forest_kl import initial_edges, load_backend as load_forest_backend
from minimal_oracle import load_backend as load_oracle_backend
from profile_minimal import weighted_summary
from validate import digest, freeze_json, read_runs


ROOT = Path(__file__).resolve().parent
INPUT = ROOT/'results'/'fixed_accuracy_confirmation'
OUTPUT = ROOT/'results'/'fixed_accuracy_rescue'
CASE = 'fixed_accuracy_cellwise_extensive_rescue'
SCREEN_R = (.15, .30, .45, .60, .75, .90)
TOP_K = 8
CONFIRMATION_DATA = (174, 175, 176)
CONFIRMATION_ALGORITHMS = (273, 274)
SOURCES = tuple(dict.fromkeys((*fixed.SOURCES, 'fixed_accuracy_rescue.py',
    'report_fixed_accuracy_rescue.py', 'test_fixed_accuracy_rescue.py')))


def load_json(path):
    return json.loads(Path(path).read_text())


def input_digests():
    names = ('design.json', 'selection.json', 'records.json', 'summary.json',
             'slopes.json', 'audit.json', 'report_manifest.json')
    missing = [name for name in names if not (INPUT/name).exists()]
    if missing:
        raise FileNotFoundError(f'Please finish fixed-accuracy confirmation first: {missing}')
    return {name: digest(INPUT/name) for name in names}


def failed_cells():
    """Keep a cell only when neither frozen role passed all development pairs."""
    summary = load_json(INPUT/'summary.json')
    result = []
    for target in phase1.TARGETS:
        for n in phase1.N_GRID:
            local = [row for row in summary if row['target'] == target and row['n'] == n]
            if not any(row['mean_Q_confirmed'] is not None for row in local):
                result.append((target, n))
    return result


def hardest_pairs(cells):
    """Choose the pair with the worst best-existing normalized upper KL."""
    rows = load_json(INPUT/'records.json')
    result = {}
    for target, n in cells:
        local = [row for row in rows if row['target'] == target and row['n'] == n]
        by_pair = defaultdict(list)
        for row in local:
            by_pair[(row['data_repeat'], row['algorithm_repeat'])].append(row)
        scored = []
        for pair, values in by_pair.items():
            ratios = [(row['K_upper']/row['K_threshold'])
                      for row in values if row['K_upper'] is not None]
            # Please judge a pair by its best existing role; tuning may improve it.
            best_ratio = min(ratios, default=float('inf'))
            scored.append((best_ratio, pair))
        result[f'{target}|{n}'] = list(max(scored, key=lambda item: (item[0], item[1]))[1])
    return result


def tuning_facets(target):
    return phase1.rescue_spec(target)['facets']


def screen_candidates(target, n, *, smoke=False):
    facets = tuning_facets(target)[:2] if smoke else tuning_facets(target)
    rs = SCREEN_R[:2] if smoke else SCREEN_R
    lambdas = phase1.lambda_grid(target)[:2] if smoke else phase1.lambda_grid(target)
    settings = set()
    for p, d in facets:
        for r in rs:
            m = phase1.m_for_r(n, p, r)
            if m is None:
                continue
            for lam in lambdas:
                settings.add((p, m, d, float(lam*phase1.coupling_cap(target, n))))
    previous = load_json(INPUT/'selection.json')[f'{target}|{n}']
    for role in fixed.ROLES:
        settings.add(tuple(previous[role]['setting']))
    return sorted(settings)


def make_job(target, n, setting, pair, samples):
    data, algorithm = pair
    return {'kind': 'proposal', 'target': target, 'n': int(n),
            'data': int(data), 'algorithm': int(algorithm), 'setting': list(setting),
            'evaluation_samples': int(samples),
            'evaluation_exact_arity': phase1.EVALUATION_EXACT_ARITY}


def design(smoke=False):
    cells = failed_cells()
    if smoke:
        cells = cells[:2]
    hardest = hardest_pairs(cells)
    development_pairs = load_json(INPUT/'design.json')['pairs']
    confirmation_pairs = [[data, algorithm] for data in CONFIRMATION_DATA
                          for algorithm in CONFIRMATION_ALGORITHMS]
    if smoke:
        hardest_values = [hardest[f'{target}|{n}'] for target, n in cells]
        available_pairs = development_pairs
        development_pairs = []
        for pair in hardest_values+available_pairs:
            if pair not in development_pairs:
                development_pairs.append(pair)
            if len(development_pairs) == 2:
                break
        confirmation_pairs = confirmation_pairs[:1]
    thresholds = load_json(INPUT/'design.json')['accuracy']['K_thresholds']
    return {'version': 1, 'study': CASE, 'smoke': smoke,
        'cells': [{'target': target, 'n': n} for target, n in cells],
        'thresholds': thresholds, 'screen_r': list(SCREEN_R[:2] if smoke else SCREEN_R),
        'lambda_grid': {target: list(phase1.lambda_grid(target)[:2] if smoke
                                    else phase1.lambda_grid(target))
                        for target in phase1.TARGETS},
        'facets': {target: [list(x) for x in
                            (tuning_facets(target)[:2] if smoke else tuning_facets(target))]
                   for target in phase1.TARGETS},
        'hardest_development_pair': hardest,
        'development_pairs': development_pairs,
        'confirmation_pairs': confirmation_pairs,
        'screen_samples': 16 if smoke else 32,
        'development_samples': 16 if smoke else 32,
        'confirmation_samples': 32 if smoke else phase1.EVALUATION_SAMPLES,
        'top_k': 2 if smoke else TOP_K,
        'query_cap': 'Q<=N; every over-budget run remains censored.',
        'selection': {
            'screen': 'Dense target-specific (p,d) x q0/N x lambda surface on the hardest old pair.',
            'development': 'Four global leaders plus facet-diverse leaders, at most eight; all six old pairs.',
            'final': 'Minimum mean Q among 6/6 conservative successes; otherwise deterministic best fallback.',
            'independence': 'Final settings are frozen before data 174:176 x algorithm 273:274.'},
        'success': 'complete and K+2*conditional_MC_SE_total <= frozen K_star',
        'oracle': 'exact', 'edge_law': 'constant',
        'phase_boundary': 'Finish cellwise rescue and fresh confirmation before any Beta-tail or noisy-oracle run.',
        'input_sha256': input_digests(),
        'source_sha256': {name: digest(ROOT/name) for name in SOURCES}}


def screen_jobs(config):
    jobs = {}
    for cell in config['cells']:
        target, n = cell['target'], cell['n']
        pair = config['hardest_development_pair'][f'{target}|{n}']
        for setting in screen_candidates(target, n, smoke=config['smoke']):
            job = make_job(target, n, setting, pair, config['screen_samples'])
            jobs[controls.job_key(job)] = job
    return sorted(jobs.values(), key=controls.job_key)


def normalized_lambda(job):
    return job['setting'][3]/phase1.coupling_cap(job['target'], job['n'])


def record(row, thresholds):
    complete = row['status'] == 'complete'
    k = float(row['kl_nats']) if complete else None
    se = float(row.get('kl_mc_se_per_token', 0.)*row['n']) if complete else None
    upper = k+2*se if complete else None
    threshold = thresholds[row['target']]
    p, m, d, tau = row['study_job']['setting']
    return {'target': row['target'], 'n': row['n'],
        'data_repeat': row['data_repeat'], 'algorithm_repeat': row['algorithm_repeat'],
        'setting': row['study_job']['setting'], 'setting_key': json.dumps(
            row['study_job']['setting'], separators=(',', ':')),
        'p': p, 'M': m, 'd': d, 'tau': tau,
        'lambda': normalized_lambda(row['study_job']),
        'q0': phase1.q0(p, m), 'q0_over_N': phase1.actual_r(row['n'], p, m),
        'status': row['status'], 'Q': row['total'], 'Q_over_N': row['total']/row['n'],
        'K': k, 'K_mc_se': se, 'K_upper': upper, 'K_threshold': threshold,
        'normalized_K_upper': upper/threshold if complete else None,
        'success': bool(complete and upper <= threshold),
        'exact_zero': bool(complete and fixed.exact_zero(row)),
        'committed_fraction': row.get('committed_tokens', 0)/row['n'],
        'abort_stage': (row.get('budget_stop') or {}).get('stage'),
        'job_key': controls.job_key(row['study_job'])}


def screen_rank_key(row):
    if row['success']:
        return (0, row['Q'], not row['exact_zero'], row['normalized_K_upper'],
                row['p'], row['M'], row['d'], row['lambda'])
    if row['status'] == 'complete':
        return (1, row['normalized_K_upper'], row['Q'], not row['exact_zero'],
                row['p'], row['M'], row['d'], row['lambda'])
    return (2, -row['committed_fraction'], row['Q'], True,
            row['p'], row['M'], row['d'], row['lambda'])


def select_development_candidates(screen_records, config):
    result = {}
    for cell in config['cells']:
        target, n = cell['target'], cell['n']
        local = sorted([row for row in screen_records
                        if row['target'] == target and row['n'] == n],
                       key=screen_rank_key)
        chosen = local[:min(4, config['top_k'])]
        used_settings = {row['setting_key'] for row in chosen}
        used_facets = {(row['p'], row['d']) for row in chosen}
        # Please retain facet diversity after the strongest global candidates.
        for row in local:
            if len(chosen) >= config['top_k']:
                break
            facet = row['p'], row['d']
            if row['setting_key'] not in used_settings and facet not in used_facets:
                chosen.append(row)
                used_settings.add(row['setting_key'])
                used_facets.add(facet)
        for row in local:
            if len(chosen) >= config['top_k']:
                break
            if row['setting_key'] not in used_settings:
                chosen.append(row)
                used_settings.add(row['setting_key'])
        result[f'{target}|{n}'] = [{
            'setting': row['setting'], 'screen_rank': index+1,
            'screen_success': row['success'], 'screen_Q': row['Q'],
            'screen_K_upper': row['K_upper'], 'screen_pair': [
                row['data_repeat'], row['algorithm_repeat']]}
            for index, row in enumerate(chosen)]
    return result


def development_jobs(config, candidates):
    jobs = {}
    for cell in config['cells']:
        key = f'{cell["target"]}|{cell["n"]}'
        for item in candidates[key]:
            for pair in config['development_pairs']:
                job = make_job(cell['target'], cell['n'], item['setting'], pair,
                               config['development_samples'])
                jobs[controls.job_key(job)] = job
    return sorted(jobs.values(), key=controls.job_key)


def aggregate_development(records, config):
    groups = defaultdict(list)
    for row in records:
        groups[(row['target'], row['n'], row['setting_key'])].append(row)
    expected = len(config['development_pairs'])
    result = []
    for (target, n, setting_key), local in sorted(groups.items()):
        if len(local) != expected:
            raise AssertionError('Every development candidate must retain every seed pair.')
        complete = [row for row in local if row['status'] == 'complete']
        ratios = [row['normalized_K_upper'] for row in complete]
        result.append({'target': target, 'n': n,
            'setting': local[0]['setting'], 'setting_key': setting_key,
            'p': local[0]['p'], 'M': local[0]['M'], 'd': local[0]['d'],
            'lambda': local[0]['lambda'], 'q0_over_N': local[0]['q0_over_N'],
            'runs': len(local), 'complete': len(complete),
            'successes': sum(row['success'] for row in local),
            'exact_zeros': sum(row['exact_zero'] for row in local),
            'mean_Q': float(np.mean([row['Q'] for row in local])),
            'maximum_normalized_K_upper': (max(ratios) if len(complete) == expected
                                           else None),
            'eligible': bool(len(complete) == expected
                             and all(row['success'] for row in local))})
    return result


def final_rank_key(row):
    if row['eligible']:
        return (0, row['mean_Q'], -row['exact_zeros'],
                row['maximum_normalized_K_upper'], row['p'], row['M'], row['d'],
                row['lambda'])
    ratio = (row['maximum_normalized_K_upper'] if
             row['maximum_normalized_K_upper'] is not None else float('inf'))
    return (1, -row['successes'], -row['complete'], -row['exact_zeros'], ratio,
            row['mean_Q'], row['p'], row['M'], row['d'], row['lambda'])


def select_final(aggregates, config):
    result = {}
    for cell in config['cells']:
        target, n = cell['target'], cell['n']
        local = [row for row in aggregates if row['target'] == target and row['n'] == n]
        chosen = min(local, key=final_rank_key)
        result[f'{target}|{n}'] = {**chosen,
            'reason': ('minimum mean Q among all-pair conservative successes'
                       if chosen['eligible'] else
                       'fallback maximizing development successes/completion')}
    return result


def confirmation_jobs(config, selected):
    jobs = []
    for cell in config['cells']:
        item = selected[f'{cell["target"]}|{cell["n"]}']
        for pair in config['confirmation_pairs']:
            jobs.append(make_job(cell['target'], cell['n'], item['setting'], pair,
                                 config['confirmation_samples']))
    return sorted(jobs, key=controls.job_key)


def ensure_profiles(out, jobs, stage):
    profiles = []
    canonical = {}
    arrays_by_target = {}
    artifact_root = out/'artifacts'/stage
    # Please build each target/seed snapshot once; hyperparameter jobs share it.
    identities = {(job['target'], job['n'], job['data'], job['algorithm']): job
                  for job in jobs}
    for job in identities.values():
        key = job['target'], job['n'], job['data']
        repeat = pivot.repeat_id(job['data'], job['algorithm'])
        oracle, _ = phase1.make_target(job['target'], job['n'], repeat)
        if key not in canonical:
            rows, weights, total = initial_edges(oracle)
            arrays = {'edges': oracle.edges, 'theta': oracle.edge_strengths,
                      'fields': oracle.fields, 'initial_rows': rows,
                      'initial_edge_kl': weights}
            path = (out/'target_profiles'/stage/
                    f'{job["target"]}_N{job["n"]}_data{job["data"]}.npz')
            path.parent.mkdir(parents=True, exist_ok=True)
            if path.exists():
                with np.load(path) as saved:
                    for name, values in arrays.items():
                        np.testing.assert_array_equal(saved[name], values)
            else:
                np.savez_compressed(path, **arrays)
            canonical[key] = path
            profiles.append({'stage': stage, 'target': job['target'], 'n': job['n'],
                'data_repeat': job['data'], 'field_seed': oracle.field_seed,
                'fields_sha256': controls.array_hash(oracle.fields, '<f8'),
                'L0_total': float(total), 'L0_per_token': float(total/job['n']),
                'edge_KL': weighted_summary([weights]),
                'snapshot': str(path.relative_to(out)), 'sha256': digest(path)})
            arrays_by_target[key] = arrays
        else:
            arrays = arrays_by_target[key]
            np.testing.assert_array_equal(oracle.edges, arrays['edges'])
            np.testing.assert_array_equal(oracle.edge_strengths, arrays['theta'])
            np.testing.assert_array_equal(oracle.fields, arrays['fields'])
        legacy = (artifact_root/job['target']/f'N{job["n"]}'/'target_profiles'/
                  f'{job["target"]}_{fixed.standard.CASE}_seed{repeat}.npz')
        legacy.parent.mkdir(parents=True, exist_ok=True)
        if legacy.exists():
            with np.load(legacy) as saved:
                for name, values in arrays.items():
                    np.testing.assert_array_equal(saved[name], values)
        else:
            np.savez_compressed(legacy, **arrays)
    return profiles


def run_one(job, output):
    row = phase1.run_one(job, output)
    row['rescue_study'] = CASE
    return row


def execute(out, jobs, stage, workers, state):
    freeze_json(out/f'{stage}_jobs.json', jobs)
    path = out/f'{stage}_runs.jsonl'
    rows = read_runs(path)
    done = {controls.job_key(row['study_job']): row for row in rows}
    wanted = {controls.job_key(job) for job in jobs}
    if len(done) != len(rows) or not set(done) <= wanted:
        raise ValueError(f'Saved {stage} rows disagree with the frozen jobs.')
    pending = [job for job in jobs if controls.job_key(job) not in done]
    state.update(stage=stage, stage_jobs=len(jobs),
                 stage_finished=len(jobs)-len(pending), updated_utc=grid.utc())
    grid.atomic_json(out/'status.json', state)
    started = perf_counter()
    if pending:
        with ProcessPoolExecutor(max_workers=workers) as pool, path.open('a') as stream:
            futures = {pool.submit(run_one, job,
                out/'artifacts'/stage/job['target']/f'N{job["n"]}'): job
                for job in pending}
            for future in as_completed(futures):
                try:
                    row = future.result()
                except BaseException:
                    for item in futures:
                        item.cancel()
                    raise
                rows.append(row)
                stream.write(json.dumps(row, separators=(',', ':'), allow_nan=False)+'\n')
                stream.flush()
                state['stage_finished'] += 1
                state['updated_utc'] = grid.utc()
                grid.atomic_json(out/'status.json', state)
                if state['stage_finished'] % 25 == 0 or state['stage_finished'] == len(jobs):
                    print(f'{stage} {state["stage_finished"]}/{len(jobs)} '
                          f'{row["target"]} N={row["n"]} Q={row["total"]} '
                          f'K={row.get("kl_nats")} {row["status"]}', flush=True)
    history_path = out/'execution_history.json'
    history = load_json(history_path) if history_path.exists() else []
    history.append({'stage': stage, 'jobs': len(jobs), 'new_runs': len(pending),
                    'workers': workers, 'seconds': perf_counter()-started,
                    'finished_utc': grid.utc()})
    grid.atomic_json(history_path, history)
    lookup = {controls.job_key(row['study_job']): row for row in rows}
    return [lookup[controls.job_key(job)] for job in jobs]


def aggregate_confirmation(records, config, selected):
    groups = defaultdict(list)
    for row in records:
        groups[(row['target'], row['n'])].append(row)
    expected = len(config['confirmation_pairs'])
    result = []
    for (target, n), local in sorted(groups.items()):
        if len(local) != expected:
            raise AssertionError('Each rescue confirmation cell needs every fresh pair.')
        successful = [row for row in local if row['success']]
        qs = np.asarray([row['Q'] for row in local], dtype=float)
        result.append({'target': target, 'n': n, 'runs': len(local),
            'complete': sum(row['status'] == 'complete' for row in local),
            'successes': len(successful),
            'exact_zeros': sum(row['exact_zero'] for row in local),
            'confirmed': len(successful) == expected,
            'mean_Q': float(qs.mean()),
            'Q_se': float(qs.std(ddof=1)/np.sqrt(len(qs))) if len(qs) > 1 else None,
            'mean_Q_over_N': float(qs.mean()/n),
            'setting': selected[f'{target}|{n}']['setting'],
            'development_eligible': selected[f'{target}|{n}']['eligible']})
    return result


def combined_scaling(rescue_summary):
    original = load_json(INPUT/'summary.json')
    rescue = {(row['target'], row['n']): row for row in rescue_summary}
    points = []
    slopes = []
    for target in phase1.TARGETS:
        for n in phase1.N_GRID:
            if (target, n) in rescue:
                row = rescue[(target, n)]
                confirmed = row['confirmed']
                q, se = (row['mean_Q'], row['Q_se']) if confirmed else (None, None)
                spent = row['mean_Q']
                source = 'fresh rescue confirmation'
                successes, runs = row['successes'], row['runs']
            else:
                row = next(item for item in original if item['target'] == target
                           and item['n'] == n and item['role'] == 'frontier')
                confirmed = row['mean_Q_confirmed'] is not None
                q, se = row['mean_Q_confirmed'], row['Q_se_confirmed']
                spent = row['mean_Q_spent']
                source = 'original fresh confirmation'
                successes, runs = row['threshold_success_conservative'], row['runs']
            points.append({'target': target, 'n': n, 'confirmed': confirmed,
                'mean_Q': q, 'mean_Q_spent': spent, 'Q_se': se,
                'mean_Q_over_N': q/n if q is not None else None,
                'successes': successes, 'runs': runs, 'source': source})
        local = [(row['n'], row['mean_Q']) for row in points
                 if row['target'] == target and row['confirmed']]
        if len(local) >= 3:
            exponent, intercept = np.polyfit(
                np.log([x for x, _ in local]), np.log([y for _, y in local]), 1)
            endpoint = np.log(local[-1][1]/local[0][1])/np.log(local[-1][0]/local[0][0])
            exponent, intercept, endpoint = map(float, (exponent, intercept, endpoint))
        else:
            exponent = intercept = endpoint = None
        slopes.append({'target': target, 'confirmed_points': len(local),
            'points': [[int(n), float(q)] for n, q in local],
            'OLS_exponent': exponent, 'OLS_intercept': intercept,
            'endpoint_exponent': endpoint})
    return points, slopes


def audit(out, config, stages, screen_records, development_records,
          confirmation_records, selected):
    for name, rows in stages.items():
        keys = [controls.job_key(row['study_job']) for row in rows]
        assert len(keys) == len(set(keys))
        assert all(row['total'] <= row['n'] for row in rows)
        if name == 'confirmation':
            assert all([row['data_repeat'], row['algorithm_repeat']]
                       in config['confirmation_pairs'] for row in rows)
    assert not ({tuple(pair) for pair in config['development_pairs']}
                & {tuple(pair) for pair in config['confirmation_pairs']})
    for cell in config['cells']:
        key = f'{cell["target"]}|{cell["n"]}'
        setting = selected[key]['setting']
        assert all(row['setting'] == setting for row in confirmation_records
                   if row['target'] == cell['target'] and row['n'] == cell['n'])
    result = {'failed_cells': len(config['cells']),
        'screen_runs': len(screen_records),
        'development_runs': len(development_records),
        'confirmation_runs': len(confirmation_records),
        'development_confirmation_seeds_disjoint': True,
        'final_settings_frozen_before_confirmation': True,
        'query_caps_verified': True, 'oracle': 'exact', 'edge_law': 'constant',
        'noise_started': False}
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
    jobs_screen = screen_jobs(config)
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    with (out/'runner.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        freeze_json(out/'design.json', config)
        freeze_json(out/'screen_jobs.json', jobs_screen)
        sources = out/'sources'
        sources.mkdir(exist_ok=True)
        for name, checksum in config['source_sha256'].items():
            destination = sources/name
            if not destination.exists():
                shutil.copyfile(ROOT/name, destination)
            assert digest(destination) == checksum
        if args.prepare_only:
            grid.atomic_json(out/'status.json', {'status': 'prepared',
                'stage': 'prepared', 'screen_jobs': len(jobs_screen),
                'output': str(out), 'updated_utc': grid.utc()})
            return
        started = perf_counter()
        state = {'status': 'running', 'stage': 'profiles', 'pid': os.getpid(),
                 'workers': args.workers, 'output': str(out),
                 'started_utc': grid.utc()}
        grid.atomic_json(out/'status.json', state)
        try:
            load_oracle_backend()
            load_forest_backend()
            all_profiles = []
            all_profiles.extend(ensure_profiles(out, jobs_screen, 'screen'))
            screen_rows = execute(out, jobs_screen, 'screen', args.workers, state)
            screen_records = [record(row, config['thresholds']) for row in screen_rows]
            grid.atomic_json(out/'screen_records.json', screen_records)
            candidates = select_development_candidates(screen_records, config)
            freeze_json(out/'development_candidates.json', candidates)

            jobs_development = development_jobs(config, candidates)
            all_profiles.extend(ensure_profiles(out, jobs_development, 'development'))
            development_rows = execute(out, jobs_development, 'development',
                                       args.workers, state)
            development_records = [record(row, config['thresholds'])
                                   for row in development_rows]
            development_summary = aggregate_development(development_records, config)
            grid.atomic_json(out/'development_records.json', development_records)
            grid.atomic_json(out/'development_summary.json', development_summary)
            selected = select_final(development_summary, config)
            freeze_json(out/'final_selection.json', selected)

            jobs_confirmation = confirmation_jobs(config, selected)
            all_profiles.extend(ensure_profiles(out, jobs_confirmation, 'confirmation'))
            confirmation_rows = execute(out, jobs_confirmation, 'confirmation',
                                        args.workers, state)
            confirmation_records = [record(row, config['thresholds'])
                                    for row in confirmation_rows]
            confirmation_summary = aggregate_confirmation(
                confirmation_records, config, selected)
            grid.atomic_json(out/'confirmation_records.json', confirmation_records)
            grid.atomic_json(out/'confirmation_summary.json', confirmation_summary)
            points, slopes = combined_scaling(confirmation_summary)
            grid.atomic_json(out/'combined_scaling.json',
                             {'points': points, 'slopes': slopes})
            freeze_json(out/'target_profiles.json', all_profiles)
            audit(out, config, {'screen': screen_rows,
                                'development': development_rows,
                                'confirmation': confirmation_rows},
                  screen_records, development_records, confirmation_records, selected)
            from report_fixed_accuracy_rescue import report
            report(out)
            for name, checksum in config['source_sha256'].items():
                assert digest(ROOT/name) == checksum
            state.update(status='complete', stage='rescue_complete_stop_before_noise',
                         finished_utc=grid.utc(), seconds=perf_counter()-started,
                         confirmed_rescue_cells=sum(row['confirmed']
                                                    for row in confirmation_summary),
                         noise_started=False)
            grid.atomic_json(out/'status.json', state)
            print(json.dumps(state, indent=2), flush=True)
        except BaseException as error:
            state.update(status='failed', error=repr(error),
                         traceback=traceback.format_exc(), updated_utc=grid.utc(),
                         seconds=perf_counter()-started)
            grid.atomic_json(out/'status.json', state)
            raise


if __name__ == '__main__':
    main()
