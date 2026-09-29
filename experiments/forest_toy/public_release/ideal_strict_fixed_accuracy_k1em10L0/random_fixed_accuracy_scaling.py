"""Measure the raw fixed-accuracy query complexity of balanced random batches.

The study uses the same constant-edge targets and frozen per-tree absolute
``K_star`` values as the proposal scaling study.  A development cohort locates
the smallest stable successful random-batch budget on a common normalized
coarse grid and a local grid with width at most about one percent of ``N``.
The selected budget is frozen before the first fresh cohort is evaluated.

Cells that fail the first fresh cohort may use that cohort only as rescue
development data.  Their replacement budget is then frozen and evaluated on a
second untouched cohort.  Development and fresh observations are never pooled.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
import fcntl
import json
from math import ceil
import os
from pathlib import Path
import shutil
from time import perf_counter

import numpy as np

import fixed_accuracy_confirmation as fixed
import row_cap_grid_study as grid
import strong_path_baseline_study as controls
import sublinear_pilot_study as phase1
from validate import digest, freeze_json, read_runs


ROOT = Path(__file__).resolve().parent
FIXED = ROOT/'results'/'fixed_accuracy_confirmation'
RESCUE = ROOT/'results'/'fixed_accuracy_rescue'
PLAN = ROOT/'ROBUSTNESS_SCALING_PLAN_2026-09-19.md'
OUTPUT = ROOT/'results'/'random_fixed_accuracy_scaling'
CASE = 'ideal_random_fixed_accuracy_scaling'

COARSE_RATIOS = (1/64, 1/32, 1/16, 1/8, 1/4, 1/2,
                 3/4, 7/8, 15/16, 31/32, 1.)
DEVELOPMENT_DATA = (184, 185, 186)
DEVELOPMENT_ALGORITHMS = (284, 285)
CONFIRMATION_DATA = (187, 188, 189)
CONFIRMATION_ALGORITHMS = (286, 287)
RESCUE_CONFIRMATION_DATA = (190, 191, 192)
RESCUE_CONFIRMATION_ALGORITHMS = (288, 289)
SOURCES = tuple(dict.fromkeys((*phase1.SOURCES,
    'fixed_accuracy_confirmation.py', 'fixed_accuracy_rescue.py',
    'random_fixed_accuracy_scaling.py',
    'report_random_fixed_accuracy_scaling.py',
    'test_random_fixed_accuracy_scaling.py')))


def load_json(path):
    return json.loads(Path(path).read_text())


def input_digests():
    paths = {
        'fixed_design': FIXED/'design.json',
        'combined_scaling': RESCUE/'combined_scaling.json',
        'plan': PLAN,
    }
    missing = [name for name, path in paths.items() if not path.exists()]
    if missing:
        raise FileNotFoundError(f'Please restore the required inputs: {missing}')
    return {name: digest(path) for name, path in paths.items()}


def crossed(data_values, algorithm_values):
    return [[int(data), int(algorithm)] for data in data_values
            for algorithm in algorithm_values]


def design(smoke=False):
    thresholds = load_json(FIXED/'design.json')['accuracy']['K_thresholds']
    return {
        'version': 1,
        'study': CASE,
        'smoke': bool(smoke),
        'targets': list(phase1.TARGETS[:2] if smoke else phase1.TARGETS),
        'n_grid': list((512, 768) if smoke else phase1.N_GRID),
        'edge_law': 'constant',
        'oracle': 'exact',
        'thresholds': thresholds,
        'threshold_rule': ('Reuse each tree\'s absolute constant-edge K_star; '
                           'never rescale it with N.'),
        'coarse_ratios': list(COARSE_RATIOS if not smoke else (1/4, 3/4, 1.)),
        'refinement_width_fraction': .05 if smoke else .01,
        'development_pairs': (crossed(DEVELOPMENT_DATA[:1], DEVELOPMENT_ALGORITHMS[:1])
                              if smoke else crossed(DEVELOPMENT_DATA,
                                                    DEVELOPMENT_ALGORITHMS)),
        'confirmation_pairs': (crossed(CONFIRMATION_DATA[:1],
                                       CONFIRMATION_ALGORITHMS[:1])
                               if smoke else crossed(CONFIRMATION_DATA,
                                                     CONFIRMATION_ALGORITHMS)),
        'rescue_confirmation_pairs': (crossed(RESCUE_CONFIRMATION_DATA[:1],
                                              RESCUE_CONFIRMATION_ALGORITHMS[:1])
                                      if smoke else crossed(
                                          RESCUE_CONFIRMATION_DATA,
                                          RESCUE_CONFIRMATION_ALGORITHMS)),
        'success': 'complete and K + 2 * conditional_MC_SE_total <= K_star',
        'selection': {
            'development': ('First budget whose observed development successes form a '
                            'successful suffix of every evaluated larger budget.'),
            'confirmation': 'Freeze before the first untouched fresh cohort.',
            'rescue': ('A failed first confirmation cohort becomes rescue development only; '
                       'freeze a padded larger budget before a second fresh cohort.'),
        },
        'query_cap': '1 <= B=Q <= N; B=N is the exact singleton endpoint.',
        'input_sha256': input_digests(),
        'source_sha256': {name: digest(ROOT/name) for name in SOURCES},
    }


def ratio_budgets(n, ratios):
    """Convert a normalized grid to unique legal integer batch counts."""
    values = {1, int(n)}
    values.update(min(int(n), max(1, int(round(float(ratio)*n))))
                  for ratio in ratios)
    return sorted(values)


def random_job(target, n, budget, pair, role, samples):
    data, algorithm = pair
    return {
        'kind': 'baseline', 'target': target, 'n': int(n),
        'data': int(data), 'algorithm': int(algorithm),
        'family': 'fixed', 'ordering': 'random', 'parameter': int(budget),
        'role': str(role), 'evaluation_samples': int(samples),
        'evaluation_exact_arity': phase1.EVALUATION_EXACT_ARITY,
    }


def stage_jobs(config, budgets_by_cell, pairs, role):
    samples = 32 if config['smoke'] else phase1.EVALUATION_SAMPLES
    jobs = []
    for target in config['targets']:
        for n in config['n_grid']:
            for budget in budgets_by_cell[(target, n)]:
                for pair in pairs:
                    jobs.append(random_job(target, n, budget, pair, role, samples))
    return sorted(jobs, key=controls.job_key)


def run_one(job, output):
    local = (Path(output)/'artifacts'/job['role']/job['target']/
             f'N{job["n"]}')
    row = phase1.run_one(job, local)
    row.update(random_fixed_accuracy_study=CASE, search_role=job['role'])
    return row


def execute(output, jobs, workers, state, stage):
    """Run one immutable stage and append resumable, unique JSONL records."""
    jobs = sorted({controls.job_key(job): job for job in jobs}.values(),
                  key=controls.job_key)
    manifests = output/'manifests'
    manifests.mkdir(exist_ok=True)
    freeze_json(manifests/f'{stage}_jobs.json', jobs)
    path = output/f'{stage}_runs.jsonl'
    rows = read_runs(path)
    done = {controls.job_key(row['study_job']): row for row in rows}
    wanted = {controls.job_key(job) for job in jobs}
    if len(done) != len(rows) or not set(done) <= wanted:
        raise ValueError(f'Saved rows disagree with {stage} manifest.')
    pending = [job for job in jobs if controls.job_key(job) not in done]
    state.update(stage=stage, stage_jobs=len(jobs),
                 stage_finished=len(jobs)-len(pending), updated_utc=grid.utc())
    grid.atomic_json(output/'status.json', state)
    started = perf_counter()
    if pending:
        with ProcessPoolExecutor(max_workers=workers) as pool, path.open('a') as stream:
            futures = {pool.submit(run_one, job, output): job for job in pending}
            for future in as_completed(futures):
                try:
                    row = future.result()
                except BaseException:
                    for item in futures:
                        item.cancel()
                    raise
                rows.append(row)
                stream.write(json.dumps(row, separators=(',', ':'),
                                        allow_nan=False)+'\n')
                stream.flush()
                state['stage_finished'] += 1
                state['updated_utc'] = grid.utc()
                grid.atomic_json(output/'status.json', state)
                if state['stage_finished'] % 50 == 0 or state['stage_finished'] == len(jobs):
                    job = row['study_job']
                    print(f'{stage} {state["stage_finished"]}/{len(jobs)} '
                          f'{job["target"]} N={job["n"]} B={job["parameter"]} '
                          f'K={row.get("kl_nats")}', flush=True)
    history_path = output/'execution_history.json'
    history = load_json(history_path) if history_path.exists() else []
    history.append({'stage': stage, 'jobs': len(jobs), 'new_runs': len(pending),
                    'workers': workers, 'seconds': perf_counter()-started,
                    'finished_utc': grid.utc()})
    grid.atomic_json(history_path, history)
    lookup = {controls.job_key(row['study_job']): row for row in rows}
    return [lookup[controls.job_key(job)] for job in jobs]


def record(row, thresholds):
    job = row['study_job']
    complete = row['status'] == 'complete'
    k = float(row['kl_nats']) if complete else None
    se = float(row.get('kl_mc_se_per_token', 0.)*row['n']) if complete else None
    upper = k+2*se if complete else None
    threshold = float(thresholds[job['target']])
    return {
        'target': job['target'], 'n': job['n'], 'budget': int(job['parameter']),
        'data_repeat': job['data'], 'algorithm_repeat': job['algorithm'],
        'role': job['role'], 'status': row['status'], 'K': k,
        'K_mc_se': se, 'K_upper': upper, 'K_threshold': threshold,
        'success': bool(complete and upper <= threshold),
        'Q': row['total'], 'job_key': controls.job_key(job),
    }


def summarize_budgets(records, pairs):
    """Return one deterministic success summary for every cell and budget."""
    expected = {tuple(map(int, pair)) for pair in pairs}
    grouped = defaultdict(list)
    for row in records:
        grouped[(row['target'], row['n'], row['budget'])].append(row)
    result = []
    for (target, n, budget), rows in sorted(grouped.items()):
        observed = {(row['data_repeat'], row['algorithm_repeat']) for row in rows}
        if observed != expected:
            raise ValueError(f'Incomplete pair set for {(target, n, budget)}.')
        result.append({
            'target': target, 'n': n, 'budget': budget, 'runs': len(rows),
            'successes': sum(row['success'] for row in rows),
            'all_success': all(row['success'] for row in rows),
            'mean_K_upper': float(np.mean([
                row['K_upper'] if row['K_upper'] is not None else float('inf')
                for row in rows])),
            'maximum_K_upper': max((row['K_upper'] if row['K_upper'] is not None
                                    else float('inf')) for row in rows),
        })
    return result


def first_successful_suffix(local):
    """Choose the first budget for which it and every observed larger budget pass."""
    ordered = sorted(local, key=lambda row: row['budget'])
    suffix = True
    candidates = []
    for row in reversed(ordered):
        suffix = suffix and row['all_success']
        if suffix:
            candidates.append(row['budget'])
    return min(candidates) if candidates else None


def first_margin_suffix(local, upper_limit):
    """Choose a successful suffix that also stays below a strict KL margin."""
    ordered = sorted(local, key=lambda row: row['budget'])
    suffix = True
    candidates = []
    for row in reversed(ordered):
        safe = row['all_success'] and row['maximum_K_upper'] <= upper_limit
        suffix = suffix and safe
        if suffix:
            candidates.append(row['budget'])
    return min(candidates) if candidates else None


def refinement_budgets(config, coarse_summary):
    """Fill only the coarse threshold bracket on a common relative resolution."""
    result = {}
    for target in config['targets']:
        for n in config['n_grid']:
            local = [row for row in coarse_summary
                     if row['target'] == target and row['n'] == n]
            hi = first_successful_suffix(local)
            if hi is None:
                hi = n
            smaller = [row['budget'] for row in local if row['budget'] < hi]
            lo = max(smaller, default=1)
            step = max(1, int(ceil(config['refinement_width_fraction']*n)))
            values = set(range(lo+step, hi, step))
            values.add(hi)
            observed = {row['budget'] for row in local}
            result[(target, n)] = sorted(values-observed)
    return result


def select_development(config, coarse_records, refine_records):
    pairs = config['development_pairs']
    summary = summarize_budgets(coarse_records+refine_records, pairs)
    selection = {}
    for target in config['targets']:
        for n in config['n_grid']:
            local = [row for row in summary
                     if row['target'] == target and row['n'] == n]
            chosen = first_successful_suffix(local)
            if chosen is None:
                raise AssertionError('The exact B=N endpoint must always succeed.')
            lower = max((row['budget'] for row in local
                         if row['budget'] < chosen), default=0)
            selection[f'{target}|{n}'] = {
                'target': target, 'n': n, 'budget': chosen,
                'lower_observed_budget': lower,
                'bracket_width': chosen-lower,
                'bracket_width_over_N': (chosen-lower)/n,
                'development_runs': next(row['runs'] for row in local
                                         if row['budget'] == chosen),
                'rule': 'first all-success suffix on development observations',
            }
    return selection, summary


def selected_budgets(config, selection):
    return {(target, n): [selection[f'{target}|{n}']['budget']]
            for target in config['targets'] for n in config['n_grid']}


def confirmation_summary(config, selection, records, pairs, source, cells=None):
    summarized = summarize_budgets(records, pairs)
    lookup = {(row['target'], row['n'], row['budget']): row for row in summarized}
    result = []
    cells = ([(target, n) for target in config['targets'] for n in config['n_grid']]
             if cells is None else list(cells))
    for target, n in cells:
        item = selection[f'{target}|{n}']
        row = lookup[(target, n, item['budget'])]
        result.append({
            'target': target, 'n': n, 'budget': item['budget'],
            'runs': row['runs'], 'successes': row['successes'],
            'confirmed': row['all_success'], 'source': source,
            'maximum_K_upper': row['maximum_K_upper'],
            'K_threshold': config['thresholds'][target],
        })
    return result


def rescue_budgets(config, selection, first_confirmation):
    """Create the same padded upward ladder for every failed cell."""
    failed = {(row['target'], row['n']) for row in first_confirmation
              if not row['confirmed']}
    result = {(target, n): [] for target in config['targets']
              for n in config['n_grid']}
    for target, n in failed:
        start = selection[f'{target}|{n}']['budget']
        step = max(1, int(ceil(config['refinement_width_fraction']*n)))
        result[(target, n)] = sorted(set(range(start, n+1, step)) | {n})
    return result


def select_rescue(config, original, records):
    summary = summarize_budgets(records, config['confirmation_pairs'])
    result = dict(original)
    for target in config['targets']:
        for n in config['n_grid']:
            local = [row for row in summary
                     if row['target'] == target and row['n'] == n]
            if not local:
                continue
            first = first_margin_suffix(
                local, .5*float(config['thresholds'][target]))
            if first is None:
                first = n
            # A further one-step pad protects the second fresh cohort from a
            # development point that happened to lie just inside the margin.
            ordered = sorted(row['budget'] for row in local if row['budget'] >= first)
            chosen = ordered[min(1, len(ordered)-1)]
            result[f'{target}|{n}'] = {
                'target': target, 'n': n, 'budget': chosen,
                'rescue_development_first_margin_suffix': first,
                'rule': ('first rescue suffix with maximum K_upper <= 0.5 K_star, '
                         'plus one uniform grid step'),
            }
    return result, summary


def final_summary(first, rescue):
    rescued = {(row['target'], row['n']): row for row in rescue}
    result = []
    for row in first:
        replacement = rescued.get((row['target'], row['n']))
        result.append(replacement if replacement is not None else row)
    return result


def audit(output, config, all_records, development, final):
    for row in all_records:
        assert 1 <= row['budget'] == row['Q'] <= row['n']
    for target in config['targets']:
        for n in config['n_grid']:
            endpoint = [row for row in development
                        if row['target'] == target and row['n'] == n
                        and row['budget'] == n]
            assert endpoint and endpoint[0]['all_success']
    result = {
        'records': len(all_records),
        'all_query_counts_equal_batch_counts': True,
        'query_caps_verified': True,
        'exact_singleton_endpoints_verified': True,
        'development_fresh_separated': True,
        'final_confirmed_cells': sum(row['confirmed'] for row in final),
        'total_cells': len(final),
        'source_sha256': config['source_sha256'],
        'input_sha256': config['input_sha256'],
    }
    freeze_json(output/'audit.json', result)
    return result


def snapshot_sources(output, config):
    directory = output/'sources'
    directory.mkdir(exist_ok=True)
    for name, checksum in config['source_sha256'].items():
        destination = directory/name
        if not destination.exists():
            shutil.copyfile(ROOT/name, destination)
        if digest(destination) != checksum:
            raise AssertionError(f'Source snapshot mismatch: {name}')


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
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    with (output/'runner.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        freeze_json(output/'design.json', config)
        snapshot_sources(output, config)
        coarse_budgets = {(target, n): ratio_budgets(n, config['coarse_ratios'])
                          for target in config['targets'] for n in config['n_grid']}
        freeze_json(output/'coarse_budgets.json', {
            f'{target}|{n}': values for (target, n), values in coarse_budgets.items()})
        if args.prepare_only:
            grid.atomic_json(output/'status.json', {
                'status': 'prepared', 'stage': 'prepared',
                'output': str(output), 'updated_utc': grid.utc()})
            return
        state = {'status': 'running', 'stage': 'coarse', 'pid': os.getpid(),
                 'workers': args.workers, 'output': str(output),
                 'started_utc': grid.utc(), 'updated_utc': grid.utc()}
        grid.atomic_json(output/'status.json', state)
        coarse_rows = execute(output, stage_jobs(
            config, coarse_budgets, config['development_pairs'], 'development_coarse'),
            args.workers, state, 'development_coarse')
        coarse_records = [record(row, config['thresholds']) for row in coarse_rows]
        coarse_summary = summarize_budgets(coarse_records, config['development_pairs'])
        refine_budgets = refinement_budgets(config, coarse_summary)
        freeze_json(output/'refinement_budgets.json', {
            f'{target}|{n}': values for (target, n), values in refine_budgets.items()})
        refine_rows = execute(output, stage_jobs(
            config, refine_budgets, config['development_pairs'], 'development_refine'),
            args.workers, state, 'development_refine')
        refine_records = [record(row, config['thresholds']) for row in refine_rows]
        selection, development = select_development(
            config, coarse_records, refine_records)
        freeze_json(output/'development_records.json', coarse_records+refine_records)
        freeze_json(output/'development_summary.json', development)
        freeze_json(output/'selection.json', selection)

        confirmation_rows = execute(output, stage_jobs(
            config, selected_budgets(config, selection),
            config['confirmation_pairs'], 'confirmation'),
            args.workers, state, 'confirmation')
        confirmation_records = [record(row, config['thresholds'])
                                for row in confirmation_rows]
        first = confirmation_summary(config, selection, confirmation_records,
                                     config['confirmation_pairs'],
                                     'first untouched confirmation')
        freeze_json(output/'confirmation_records.json', confirmation_records)
        freeze_json(output/'first_confirmation_summary.json', first)

        ladders = rescue_budgets(config, selection, first)
        rescue_development_rows = execute(output, stage_jobs(
            config, ladders, config['confirmation_pairs'], 'rescue_development'),
            args.workers, state, 'rescue_development')
        rescue_development_records = [record(row, config['thresholds'])
                                      for row in rescue_development_rows]
        rescue_selection, rescue_development = select_rescue(
            config, selection, rescue_development_records)
        freeze_json(output/'rescue_development_records.json',
                    rescue_development_records)
        freeze_json(output/'rescue_development_summary.json', rescue_development)
        freeze_json(output/'rescue_selection.json', rescue_selection)

        failed = {(row['target'], row['n']) for row in first if not row['confirmed']}
        rescue_selected = {(target, n): [
            rescue_selection[f'{target}|{n}']['budget']]
            for target, n in failed}
        # stage_jobs expects every configured cell; empty lists safely omit unaffected cells.
        for target in config['targets']:
            for n in config['n_grid']:
                rescue_selected.setdefault((target, n), [])
        rescue_confirmation_rows = execute(output, stage_jobs(
            config, rescue_selected, config['rescue_confirmation_pairs'],
            'rescue_confirmation'), args.workers, state, 'rescue_confirmation')
        rescue_confirmation_records = [record(row, config['thresholds'])
                                       for row in rescue_confirmation_rows]
        rescue_confirmation = []
        if failed:
            raw = confirmation_summary(
                config, rescue_selection, rescue_confirmation_records,
                config['rescue_confirmation_pairs'],
                'second untouched rescue confirmation', cells=sorted(failed))
            rescue_confirmation = raw
        freeze_json(output/'rescue_confirmation_records.json',
                    rescue_confirmation_records)
        freeze_json(output/'rescue_confirmation_summary.json', rescue_confirmation)
        final = final_summary(first, rescue_confirmation)
        freeze_json(output/'final_summary.json', final)
        all_records = (coarse_records+refine_records+confirmation_records+
                       rescue_development_records+rescue_confirmation_records)
        audit(output, config, all_records, development, final)
        from report_random_fixed_accuracy_scaling import report
        report(output)
        state.update(status='complete', stage='complete',
                     cells=len(final), confirmed=sum(row['confirmed'] for row in final),
                     updated_utc=grid.utc())
        grid.atomic_json(output/'status.json', state)


if __name__ == '__main__':
    main()
