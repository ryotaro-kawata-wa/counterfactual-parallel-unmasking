"""Retune ideal forest targets without externally censoring proposal Q at N.

Only N >= 8192 is studied.  Proposal and balanced-random settings are selected
on development cohorts, frozen, and evaluated once on untouched target draws.
The proposal retains its finite internal screen, peel, and commit-round guards;
only the experiment-level ``Q <= N`` interruption is removed.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
import csv
import fcntl
import json
from math import ceil
import os
from pathlib import Path
import platform
import shutil
import socket
from time import perf_counter
import traceback

import numpy as np

import fixed_accuracy_confirmation as fixed
import fixed_accuracy_rescue as rescue
import random_fixed_accuracy_scaling as random_study
import row_cap_grid_study as grid
import strong_path_baseline_study as controls
import sublinear_pilot_study as phase1
from forest_kl import load_backend as load_forest_backend
from minimal_oracle import load_backend as load_oracle_backend
from validate import digest, freeze_json, read_runs


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT/'results'/'ideal_capless_fixed_accuracy_scaling'
PLAN = ROOT/'IDEAL_CAPLESS_FIXED_ACCURACY_PLAN_2026-09-21.md'
CASE = 'ideal_capless_fixed_accuracy_n8192plus'

TARGETS = phase1.TARGETS
N_GRID = tuple(n for n in phase1.N_GRID if n >= 8192)
SCREEN_R = (.40, .80, 1.20, 1.60, 2.00)
TOP_K = 6
RANDOM_COARSE_RATIOS = (
    1/64, 1/32, 1/16, 1/8, 1/4, 1/2, 3/4, 7/8, 15/16, 31/32, 1.)
RANDOM_REFINEMENT_FRACTION = .05
RANDOM_MAX_REFINEMENT_ROUNDS = 10

# The development streams precede the untouched confirmation streams.  The two
# methods share target draws at confirmation but never share sampler streams.
RANDOM_DEVELOPMENT_DATA = (193, 194)
RANDOM_DEVELOPMENT_ALGORITHMS = (290, 291)
CONFIRMATION_DATA = (196, 197, 198)
PROPOSAL_CONFIRMATION_ALGORITHMS = (292, 293)
RANDOM_CONFIRMATION_ALGORITHMS = (294, 295)

PAPER_FACETS = {
    'matching': ((4, 9), (6, 9), (4, 18)),
    'path': ((8, 18), (10, 18), (8, 36)),
    'binary': ((10, 36), (12, 36), (12, 72), (16, 72)),
    'stars_original': ((6, 36), (8, 36), (8, 72)),
}
PAPER_LAMBDAS = {
    'matching': (.04, .09),
    'path': (.08, .16),
    'binary': (.08, .16),
    'stars_original': (.04, .12),
}

SOURCE_NAMES = (
    'ideal_capless_fixed_accuracy_scaling.py',
    'explore_minimal.py',
    'row_cap_grid_study.py',
    'standard_tree_study.py',
    'sublinear_pilot_study.py',
    'fixed_accuracy_confirmation.py',
    'fixed_accuracy_rescue.py',
    'random_fixed_accuracy_scaling.py',
)


def load_json(path):
    return json.loads(Path(path).read_text())


def crossed(data_values, algorithm_values):
    return [[int(data), int(algorithm)] for data in data_values
            for algorithm in algorithm_values]


def tuning_facets(target, smoke=False):
    facets = list(PAPER_FACETS[target])
    return facets[:2] if smoke else facets


def tuning_lambdas(target):
    return PAPER_LAMBDAS[target]


def previous_settings(target, n):
    """Retain old paper points as candidates without privileging their scores."""
    settings = set()
    selection = load_json(fixed.OUTPUT/'selection.json')[f'{target}|{n}']
    for role in fixed.ROLES:
        settings.add(tuple(selection[role]['setting']))
    rescued = rescue.OUTPUT/'final_selection.json'
    if rescued.exists():
        item = load_json(rescued).get(f'{target}|{n}')
        if item is not None:
            settings.add(tuple(item['setting']))
    return settings


def proposal_candidates(target, n, smoke=False):
    rs = (.40, 1.60) if smoke else SCREEN_R
    lambdas = tuning_lambdas(target)
    settings = set(previous_settings(target, n))
    for p, d in tuning_facets(target, smoke):
        for ratio in rs:
            m = phase1.m_for_r(n, p, ratio)
            if m is None:
                continue
            for normalized_threshold in lambdas:
                settings.add((p, m, d, float(
                    normalized_threshold*phase1.coupling_cap(target, n))))
    return sorted(settings)


def design(smoke=False):
    targets = TARGETS[:2] if smoke else TARGETS
    n_grid = N_GRID[:1] if smoke else N_GRID
    cells = [(target, n) for target in targets for n in n_grid]
    hardest = rescue.hardest_pairs(cells)
    old_pairs = load_json(fixed.OUTPUT/'design.json')['pairs']
    proposal_development = old_pairs[:2] if smoke else old_pairs
    random_development = crossed(
        RANDOM_DEVELOPMENT_DATA[:1] if smoke else RANDOM_DEVELOPMENT_DATA,
        RANDOM_DEVELOPMENT_ALGORITHMS[:1] if smoke
        else RANDOM_DEVELOPMENT_ALGORITHMS)
    confirmation_data = CONFIRMATION_DATA[:1] if smoke else CONFIRMATION_DATA
    proposal_algorithms = (PROPOSAL_CONFIRMATION_ALGORITHMS[:1] if smoke
                           else PROPOSAL_CONFIRMATION_ALGORITHMS)
    random_algorithms = (RANDOM_CONFIRMATION_ALGORITHMS[:1] if smoke
                         else RANDOM_CONFIRMATION_ALGORITHMS)
    proposal_confirmation = crossed(confirmation_data, proposal_algorithms)
    random_confirmation = crossed(confirmation_data, random_algorithms)
    thresholds = load_json(fixed.OUTPUT/'design.json')['accuracy']['K_thresholds']
    return {
        'version': 1, 'study': CASE, 'smoke': bool(smoke),
        'targets': list(targets), 'n_grid': list(n_grid),
        'cells': [{'target': target, 'n': n} for target, n in cells],
        'oracle': 'exact', 'edge_law': 'constant',
        'normalized_edge_strength_mean': 1.,
        'edge_scale': {
            'matching': '.5', 'path': '.25', 'binary': '1/6',
            'stars_original': '.5/max(16,ceil(sqrt(N)))'},
        'thresholds': thresholds,
        'threshold_rule': (
            'Per-tree absolute K_star=1e-3 times phase-1 L0_total at N=2048; '
            'fixed across N and identical for both methods.'),
        'success': 'complete and K+2*conditional_MC_SE_total <= K_star',
        'proposal_query_limit': None,
        'query_accounting': (
            'Q=preprocessing+counterfactual+commit rounds, each counted once.'),
        'proposal_screen_r': list((.40, 1.60) if smoke else SCREEN_R),
        'proposal_facets': {
            target: [list(x) for x in tuning_facets(target, smoke)]
            for target in targets},
        'proposal_lambda_grid': {
            target: list(tuning_lambdas(target))
            for target in targets},
        'proposal_top_k': 2 if smoke else TOP_K,
        'proposal_screen_samples': 16 if smoke else 32,
        'proposal_development_samples': 32 if smoke else 64,
        'confirmation_samples': 32 if smoke else phase1.EVALUATION_SAMPLES,
        'hardest_development_pair': hardest,
        'proposal_development_pairs': proposal_development,
        # Compatibility name used by the frozen rescue selection helpers.
        'development_pairs': proposal_development,
        'proposal_confirmation_pairs': proposal_confirmation,
        'random_development_pairs': random_development,
        'random_confirmation_pairs': random_confirmation,
        'common_confirmation_target_draws': list(confirmation_data),
        'random_coarse_ratios': list(
            (1/4, 3/4, 1.) if smoke else RANDOM_COARSE_RATIOS),
        'random_refinement_fraction_of_n': (
            .05 if smoke else RANDOM_REFINEMENT_FRACTION),
        'random_maximum_refinement_rounds': (
            4 if smoke else RANDOM_MAX_REFINEMENT_ROUNDS),
        'selection': {
            'proposal': (
                'Minimum mean Q among settings succeeding on every development '
                'pair; otherwise retain a deterministic labelled fallback.'),
            'random': (
                'Minimum observed all-success suffix at K_upper<=K_star, '
                'bisected to the stated relative width; no margin or cushion.'),
            'confirmation': (
                'Settings frozen before the common untouched target draws; '
                'no confirmation-triggered reselection.')},
        'plot': {
            'axes': 'linear-linear', 'n_minimum': 8192,
            'display_x_offset_fraction': .006,
            'Q_reference': 'exact sequential-singleton reference',
            'error_bar': 'six-run minimum to maximum',
            'failure': 'hollow triangle and dashed adjacent segment'},
        'plan_sha256': digest(PLAN),
        'input_sha256': {
            'fixed_design': digest(fixed.OUTPUT/'design.json'),
            'fixed_selection': digest(fixed.OUTPUT/'selection.json'),
            'fixed_records': digest(fixed.OUTPUT/'records.json')},
        'source_sha256': {name: digest(ROOT/name) for name in SOURCE_NAMES},
    }


def proposal_screen_jobs(config):
    jobs = {}
    for cell in config['cells']:
        target, n = cell['target'], cell['n']
        pair = config['hardest_development_pair'][f'{target}|{n}']
        for setting in proposal_candidates(target, n, config['smoke']):
            job = rescue.make_job(
                target, n, setting, pair, config['proposal_screen_samples'])
            jobs[controls.job_key(job)] = job
    return sorted(jobs.values(), key=controls.job_key)


def proposal_development_jobs(config, candidates):
    jobs = []
    for cell in config['cells']:
        key = f'{cell["target"]}|{cell["n"]}'
        for candidate in candidates[key]:
            for pair in config['proposal_development_pairs']:
                jobs.append(rescue.make_job(
                    cell['target'], cell['n'], candidate['setting'], pair,
                    config['proposal_development_samples']))
    return sorted({controls.job_key(job): job for job in jobs}.values(),
                  key=controls.job_key)


def proposal_confirmation_jobs(config, selected):
    jobs = []
    for cell in config['cells']:
        key = f'{cell["target"]}|{cell["n"]}'
        for pair in config['proposal_confirmation_pairs']:
            jobs.append(rescue.make_job(
                cell['target'], cell['n'], selected[key]['setting'], pair,
                config['confirmation_samples']))
    return jobs


def random_jobs(config, budgets_by_cell, pairs, role):
    jobs = []
    for target in config['targets']:
        for n in config['n_grid']:
            for budget in budgets_by_cell[(target, n)]:
                for pair in pairs:
                    jobs.append(random_study.random_job(
                        target, n, budget, pair, role,
                        config['confirmation_samples']))
    return sorted(jobs, key=controls.job_key)


def run_one(job, output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    query_limit = None if job['kind'] == 'proposal' else 'target_n'
    row = phase1.run_one(job, output, query_limit=query_limit)
    row.update(capless_fixed_accuracy_study=CASE,
               external_query_limit_removed=(job['kind'] == 'proposal'))
    return row


def execute(output, jobs, workers, state, stage):
    """Run one immutable, resumable stage with a stage-local artifact tree."""
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
        raise ValueError(f'Saved rows disagree with the frozen {stage} jobs.')
    pending = [job for job in jobs if controls.job_key(job) not in done]
    state.update(stage=stage, stage_jobs=len(jobs),
                 stage_finished=len(jobs)-len(pending), updated_utc=grid.utc())
    grid.atomic_json(output/'status.json', state)
    started = perf_counter()
    if pending:
        with ProcessPoolExecutor(max_workers=workers) as pool, path.open('a') as stream:
            futures = {pool.submit(
                run_one, job,
                output/'artifacts'/stage/job['target']/f'N{job["n"]}'): job
                for job in pending}
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
                if (state['stage_finished'] % 50 == 0
                        or state['stage_finished'] == len(jobs)):
                    print(f'{stage} {state["stage_finished"]}/{len(jobs)} '
                          f'{row["target"]} N={row["n"]} Q={row["total"]} '
                          f'K={row.get("kl_nats")} {row["status"]}', flush=True)
    history_path = output/'execution_history.json'
    history = load_json(history_path) if history_path.exists() else []
    history.append({'stage': stage, 'jobs': len(jobs),
                    'new_runs': len(pending), 'workers': workers,
                    'seconds': perf_counter()-started,
                    'finished_utc': grid.utc()})
    grid.atomic_json(history_path, history)
    lookup = {controls.job_key(row['study_job']): row for row in rows}
    return [lookup[controls.job_key(job)] for job in jobs]


def prepare_proposal_profiles(output, jobs, stage):
    return rescue.ensure_profiles(output, jobs, stage)


def random_budget_summary(records, config, target, n):
    local = [row for row in records
             if row['target'] == target and row['n'] == n]
    return random_study.summarize_budgets(
        local, config['random_development_pairs'])


def random_bracket(summary, n):
    endpoint = next(row for row in summary if row['budget'] == n)
    if not endpoint['all_success']:
        raise AssertionError('The exact singleton endpoint must succeed.')
    hi = random_study.first_successful_suffix(summary)
    if hi is None:
        raise AssertionError('A successful random suffix must contain B=N.')
    lo = max((row['budget'] for row in summary if row['budget'] < hi),
             default=0)
    return int(lo), int(hi)


def tune_random(output, config, workers, state):
    coarse = {
        (target, n): random_study.ratio_budgets(
            n, config['random_coarse_ratios'])
        for target in config['targets'] for n in config['n_grid']}
    freeze_json(output/'random_coarse_budgets.json', {
        f'{target}|{n}': values for (target, n), values in coarse.items()})
    rows = execute(output, random_jobs(
        config, coarse, config['random_development_pairs'],
        'random_development_coarse'), workers, state,
        'random_development_coarse')
    records = [random_study.record(row, config['thresholds']) for row in rows]

    for round_index in range(config['random_maximum_refinement_rounds']):
        budgets = {(target, n): [] for target in config['targets']
                   for n in config['n_grid']}
        active = 0
        for target in config['targets']:
            for n in config['n_grid']:
                summary = random_budget_summary(records, config, target, n)
                lo, hi = random_bracket(summary, n)
                tolerance = max(1, int(ceil(
                    config['random_refinement_fraction_of_n']*n)))
                if hi-lo <= tolerance:
                    continue
                midpoint = (lo+hi)//2
                observed = {row['budget'] for row in summary}
                if midpoint in observed:
                    raise AssertionError(
                        f'Random refinement stalled at {(target, n, lo, hi)}.')
                budgets[(target, n)] = [midpoint]
                active += 1
        if not active:
            break
        stage = f'random_development_refine_{round_index}'
        new_rows = execute(output, random_jobs(
            config, budgets, config['random_development_pairs'], stage),
            workers, state, stage)
        records.extend(random_study.record(row, config['thresholds'])
                       for row in new_rows)

    selections = {}
    summaries = {}
    for target in config['targets']:
        for n in config['n_grid']:
            summary = random_budget_summary(records, config, target, n)
            lo, hi = random_bracket(summary, n)
            tolerance = max(1, int(ceil(
                config['random_refinement_fraction_of_n']*n)))
            if hi-lo > tolerance:
                raise AssertionError(
                    f'Random bracket is still too wide at {(target, n)}.')
            key = f'{target}|{n}'
            selections[key] = {
                'target': target, 'n': n, 'budget': hi,
                'lower_observed_budget': lo, 'bracket_width': hi-lo,
                'bracket_width_over_N': (hi-lo)/n,
                'one_step_cushion': 0,
                'selection_rule': (
                    'first all-success development suffix at exact K_star; '
                    'no safety margin and no cushion')}
            summaries[key] = summary
    freeze_json(output/'random_development_records.json', records)
    freeze_json(output/'random_development_summaries.json', summaries)
    freeze_json(output/'random_selection.json', selections)
    return selections, records


def summarize_confirmation(records, method, selected, expected_runs):
    grouped = defaultdict(list)
    for row in records:
        grouped[(row['target'], row['n'])].append(row)
    result = []
    for (target, n), local in sorted(grouped.items()):
        if len(local) != expected_runs:
            raise AssertionError(
                f'Confirmation cell {(target, n)} has {len(local)} runs.')
        q = np.asarray([row['Q'] for row in local], dtype=float)
        finite_k = [row['K_upper'] for row in local
                    if row['K_upper'] is not None]
        item = {
            'target': target, 'n': n, 'method': method,
            'runs': len(local), 'successes': sum(row['success'] for row in local),
            'confirmed': all(row['success'] for row in local),
            'Q': float(q.mean()), 'Q_min': float(q.min()),
            'Q_max': float(q.max()), 'Q_values': q.tolist(),
            'Q_se': (float(q.std(ddof=1)/np.sqrt(len(q)))
                     if len(q) > 1 else None),
            'K_threshold': local[0]['K_threshold'],
            'maximum_K_upper': max(finite_k, default=None),
            'fresh_target_draws': sorted({row['data_repeat'] for row in local}),
            'fresh_sampler_streams': sorted(
                {row['algorithm_repeat'] for row in local}),
        }
        selection = selected[f'{target}|{n}']
        if method == 'proposal':
            item['setting'] = selection['setting']
            item['development_eligible'] = selection['eligible']
        else:
            item['budget'] = selection['budget']
            item['development_bracket_width_over_N'] = (
                selection['bracket_width_over_N'])
        result.append(item)
    return result


def segment_styles(rows):
    ordered = sorted(rows, key=lambda row: row['n'])
    return ['-' if left['confirmed'] and right['confirmed'] else '--'
            for left, right in zip(ordered, ordered[1:])]


def draw_curve(ax, rows, color, method):
    ordered = sorted(rows, key=lambda row: row['n'])
    true_x = np.asarray([row['n'] for row in ordered], dtype=float)
    # This small symmetric displacement is visual only.  Saved data, tuning,
    # comparisons, and any fit continue to use the exact integer N values.
    display_factor = .994 if method == 'proposal' else 1.006
    x = true_x*display_factor
    y = np.asarray([row['Q'] for row in ordered], dtype=float)
    lower = y-np.asarray([row['Q_min'] for row in ordered])
    upper = np.asarray([row['Q_max'] for row in ordered])-y
    for index, style in enumerate(segment_styles(ordered)):
        ax.plot(x[index:index+2], y[index:index+2], color=color,
                linestyle=style, linewidth=2., zorder=3)
    ax.errorbar(x, y, yerr=np.vstack([lower, upper]), fmt='none',
                ecolor=color, elinewidth=.9, capsize=2.5, zorder=2)
    confirmed = np.asarray([row['confirmed'] for row in ordered], dtype=bool)
    if method == 'proposal':
        ax.scatter(x[confirmed], y[confirmed], color=color, marker='o',
                   s=42, zorder=5)
    else:
        ax.scatter(x[confirmed], y[confirmed], facecolors='white',
                   edgecolors=color, marker='s', linewidths=1.4, s=42, zorder=5)
    ax.scatter(x[~confirmed], y[~confirmed], facecolors='white',
               edgecolors=color, marker='^', linewidths=1.4, s=54, zorder=6)


def plot_results(output, config, proposal, random_rows):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    from matplotlib.ticker import FuncFormatter

    titles = {
        'matching': '(a)  Matching', 'path': '(b)  Path',
        'binary': '(c)  Binary tree', 'stars_original': '(d)  Growing stars'}
    blue, orange = '#0072B2', '#D55E00'
    fig, axes = plt.subplots(2, 2, figsize=(11.4, 8.2), sharex=True, sharey=True)
    all_rows = proposal+random_rows
    maximum = max(max(row['Q_max'] for row in all_rows), max(config['n_grid']))
    for ax, target in zip(axes.flat, config['targets']):
        p = [row for row in proposal if row['target'] == target]
        r = [row for row in random_rows if row['target'] == target]
        draw_curve(ax, p, blue, 'proposal')
        draw_curve(ax, r, orange, 'random')
        bounds = np.asarray(config['n_grid'], dtype=float)
        ax.plot(bounds, bounds, color='.45', linestyle=':', linewidth=1.5,
                zorder=1)
        ax.set_title(titles[target], fontsize=14)
        ax.grid(alpha=.23)
        ax.set_xlim(min(config['n_grid'])-450, max(config['n_grid'])+450)
        ax.set_ylim(0, maximum*1.08)
        ax.xaxis.set_major_formatter(FuncFormatter(lambda value, _pos: f'{int(value):,}'))
        ax.yaxis.set_major_formatter(FuncFormatter(lambda value, _pos: f'{int(value):,}'))
    for ax in axes[:, 0]:
        ax.set_ylabel(r'Mean raw queries $Q$', fontsize=12)
    for ax in axes[-1, :]:
        ax.set_xlabel(r'Sequence length $N$', fontsize=12)
    fig.suptitle('Raw fixed-accuracy query scaling on ideal forest targets',
                 fontsize=18, y=.985)
    fig.text(.5, .945,
             r'$\mathbb{E}[W/X]=1$, exact oracle; fixed per-tree $K_\star$',
             ha='center', va='center', fontsize=13)
    handles = [
        Line2D([0], [0], color=blue, marker='o', linewidth=2.,
               markersize=6, label='Proposal'),
        Line2D([0], [0], color=orange, marker='s', markerfacecolor='white',
               linewidth=2., markersize=6, label='Random'),
        Line2D([0], [0], color='.45', linestyle=':', linewidth=1.5,
               label='Exact sequential-singleton reference'),
        Line2D([0], [0], color='.35', marker='^', markerfacecolor='white',
               linestyle='--', linewidth=1.4, markersize=7,
               label='Fewer than all fresh runs pass'),
    ]
    fig.legend(handles=handles, loc='upper center', bbox_to_anchor=(.5, .915),
               ncol=2, frameon=False, fontsize=11)
    fig.tight_layout(rect=(0, 0, 1, .86), h_pad=2.0, w_pad=1.4)
    stem = output/'ideal_capless_fixed_accuracy_linear'
    fig.savefig(stem.with_suffix('.png'), dpi=220)
    fig.savefig(stem.with_suffix('.pdf'))
    plt.close(fig)
    freeze_json(output/'figure_data.json', {
        'proposal': proposal, 'random': random_rows,
        'subtitle': 'E[W/X]=1, exact oracle; fixed per-tree K_star',
        'axes': 'linear-linear', 'n_grid': config['n_grid'],
        'display_x_offset_fraction': config['plot']['display_x_offset_fraction'],
        'display_offset_is_visual_only': True})
    return stem.with_suffix('.png'), stem.with_suffix('.pdf')


def write_csv(path, rows):
    fields = [
        'target', 'n', 'method', 'runs', 'successes', 'confirmed', 'Q',
        'Q_min', 'Q_max', 'Q_se', 'K_threshold', 'maximum_K_upper']
    with Path(path).open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, extrasaction='ignore')
        writer.writeheader()
        writer.writerows(rows)


def snapshot_sources(output, config):
    directory = output/'sources'
    directory.mkdir(exist_ok=True)
    for name, checksum in config['source_sha256'].items():
        destination = directory/name
        if not destination.exists():
            shutil.copyfile(ROOT/name, destination)
        if digest(destination) != checksum:
            raise AssertionError(f'Source snapshot mismatch for {name}.')


def environment_metadata():
    return {
        'hostname': socket.gethostname(), 'platform': platform.platform(),
        'python': platform.python_version(), 'numpy': np.__version__,
        'logical_cpu_count': os.cpu_count(), 'pid': os.getpid(),
        'recorded_utc': grid.utc()}


def audit(output, config, stage_rows, proposal_summary, random_summary):
    for stage, rows in stage_rows.items():
        keys = [controls.job_key(row['study_job']) for row in rows]
        if len(keys) != len(set(keys)):
            raise AssertionError(f'Duplicate jobs in {stage}.')
        for row in rows:
            if row['total'] != (row.get('preprocessing', 0)
                                + row.get('counterfactual', 0)
                                + row.get('rounds', 0)):
                raise AssertionError('Raw query components do not sum to Q.')
            if row['kind'] == 'proposal':
                if row['query_limit'] is not None or row['status'] != 'complete':
                    raise AssertionError('A capless proposal was censored.')
            elif not (row['total'] == row['study_job']['parameter'] <= row['n']):
                raise AssertionError('Random Q must equal its legal batch count.')
    expected = len(config['proposal_confirmation_pairs'])
    if any(row['runs'] != expected for row in proposal_summary):
        raise AssertionError('Proposal fresh confirmation is incomplete.')
    if any(row['runs'] != len(config['random_confirmation_pairs'])
           for row in random_summary):
        raise AssertionError('Random fresh confirmation is incomplete.')
    for p_row, r_row in zip(proposal_summary, random_summary):
        if (p_row['target'], p_row['n']) != (r_row['target'], r_row['n']):
            raise AssertionError('Method summaries are misaligned.')
        if p_row['fresh_target_draws'] != r_row['fresh_target_draws']:
            raise AssertionError('Fresh target draws must be shared.')
        if set(p_row['fresh_sampler_streams']) & set(r_row['fresh_sampler_streams']):
            raise AssertionError('Fresh sampler streams must be disjoint.')
    result = {
        'status': 'pass', 'n_grid': config['n_grid'],
        'cells': len(proposal_summary),
        'proposal_fresh_confirmed_cells': sum(
            row['confirmed'] for row in proposal_summary),
        'random_fresh_confirmed_cells': sum(
            row['confirmed'] for row in random_summary),
        'proposal_external_query_limit': None,
        'query_identity_verified': True,
        'random_exact_threshold_no_margin': True,
        'random_one_step_cushion': False,
        'confirmation_reselection': False,
        'common_confirmation_target_draws': True,
        'disjoint_sampler_streams': True,
        'source_sha256': config['source_sha256'],
        'input_sha256': config['input_sha256']}
    freeze_json(output/'audit.json', result)
    return result


def write_results_note(output, config, proposal, random_rows, audit_result):
    lines = [
        '# Ideal capless fixed-accuracy result', '',
        f'- N grid: `{config["n_grid"]}`.',
        '- Target: exact oracle, constant edge strengths, `E[W/X]=1`.',
        '- Proposal: no external query cap; Q includes preprocessing, '
        'counterfactual queries, and commit rounds once each.',
        '- Random: tuned at the same per-tree K_star, with no 0.5 margin or '
        'one-step cushion.',
        f'- Fresh 6/6 proposal cells: '
        f'`{audit_result["proposal_fresh_confirmed_cells"]}/{len(proposal)}`.',
        f'- Fresh 6/6 random cells: '
        f'`{audit_result["random_fresh_confirmed_cells"]}/{len(random_rows)}`.',
        '', 'The figure is descriptive; no inferential scaling claim is added.', '']
    (output/'RESULTS.md').write_text('\n'.join(lines))


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
        if not (output/'environment.json').exists():
            freeze_json(output/'environment.json', environment_metadata())
        screen_jobs = proposal_screen_jobs(config)
        freeze_json(output/'proposal_screen_jobs.json', screen_jobs)
        if args.prepare_only:
            grid.atomic_json(output/'status.json', {
                'status': 'prepared', 'stage': 'prepared',
                'proposal_screen_jobs': len(screen_jobs),
                'output': str(output), 'updated_utc': grid.utc()})
            return

        started = perf_counter()
        state = {'status': 'running', 'stage': 'initializing',
                 'pid': os.getpid(), 'workers': args.workers,
                 'output': str(output), 'started_utc': grid.utc(),
                 'updated_utc': grid.utc()}
        grid.atomic_json(output/'status.json', state)
        stage_rows = {}
        try:
            load_oracle_backend()
            load_forest_backend()

            prepare_proposal_profiles(output, screen_jobs, 'proposal_screen')
            stage_rows['proposal_screen'] = execute(
                output, screen_jobs, args.workers, state, 'proposal_screen')
            screen_records = [rescue.record(row, config['thresholds'])
                              for row in stage_rows['proposal_screen']]
            freeze_json(output/'proposal_screen_records.json', screen_records)
            candidates = rescue.select_development_candidates(
                screen_records, {**config, 'top_k': config['proposal_top_k']})
            freeze_json(output/'proposal_development_candidates.json', candidates)

            development_jobs = proposal_development_jobs(config, candidates)
            prepare_proposal_profiles(
                output, development_jobs, 'proposal_development')
            stage_rows['proposal_development'] = execute(
                output, development_jobs, args.workers, state,
                'proposal_development')
            development_records = [
                rescue.record(row, config['thresholds'])
                for row in stage_rows['proposal_development']]
            development_summary = rescue.aggregate_development(
                development_records, config)
            proposal_selection = rescue.select_final(
                development_summary, config)
            freeze_json(output/'proposal_development_records.json',
                        development_records)
            freeze_json(output/'proposal_development_summary.json',
                        development_summary)
            freeze_json(output/'proposal_selection.json', proposal_selection)

            random_selection, _ = tune_random(
                output, config, args.workers, state)
            # Include the already executed random stages in the final audit.
            for path in sorted(output.glob('random_development*_runs.jsonl')):
                stage_rows[path.stem.removesuffix('_runs')] = read_runs(path)

            p_confirm_jobs = proposal_confirmation_jobs(
                config, proposal_selection)
            r_budgets = {
                (target, n): [random_selection[f'{target}|{n}']['budget']]
                for target in config['targets'] for n in config['n_grid']}
            r_confirm_jobs = random_jobs(
                config, r_budgets, config['random_confirmation_pairs'],
                'random_fresh_confirmation')
            prepare_proposal_profiles(
                output, p_confirm_jobs, 'fresh_confirmation')
            stage_rows['fresh_confirmation'] = execute(
                output, p_confirm_jobs+r_confirm_jobs, args.workers, state,
                'fresh_confirmation')

            p_records = [rescue.record(row, config['thresholds'])
                         for row in stage_rows['fresh_confirmation']
                         if row['kind'] == 'proposal']
            r_records = [random_study.record(row, config['thresholds'])
                         for row in stage_rows['fresh_confirmation']
                         if row['kind'] == 'baseline']
            freeze_json(output/'proposal_confirmation_records.json', p_records)
            freeze_json(output/'random_confirmation_records.json', r_records)
            proposal_summary = summarize_confirmation(
                p_records, 'proposal', proposal_selection,
                len(config['proposal_confirmation_pairs']))
            random_summary = summarize_confirmation(
                r_records, 'random', random_selection,
                len(config['random_confirmation_pairs']))
            freeze_json(output/'proposal_confirmation_summary.json',
                        proposal_summary)
            freeze_json(output/'random_confirmation_summary.json', random_summary)
            write_csv(output/'proposal_confirmation_summary.csv', proposal_summary)
            write_csv(output/'random_confirmation_summary.csv', random_summary)
            plot_results(output, config, proposal_summary, random_summary)
            audit_result = audit(
                output, config, stage_rows, proposal_summary, random_summary)
            write_results_note(
                output, config, proposal_summary, random_summary, audit_result)
            for name, checksum in config['source_sha256'].items():
                if digest(ROOT/name) != checksum:
                    raise AssertionError(f'Live source changed during run: {name}.')
            state.update(status='complete', stage='complete',
                         seconds=perf_counter()-started,
                         proposal_confirmed=audit_result[
                             'proposal_fresh_confirmed_cells'],
                         random_confirmed=audit_result[
                             'random_fresh_confirmed_cells'],
                         updated_utc=grid.utc())
            grid.atomic_json(output/'status.json', state)
            print(json.dumps(state, indent=2), flush=True)
        except BaseException as error:
            state.update(status='failed', error=repr(error),
                         traceback=traceback.format_exc(),
                         seconds=perf_counter()-started,
                         updated_utc=grid.utc())
            grid.atomic_json(output/'status.json', state)
            raise


if __name__ == '__main__':
    main()
