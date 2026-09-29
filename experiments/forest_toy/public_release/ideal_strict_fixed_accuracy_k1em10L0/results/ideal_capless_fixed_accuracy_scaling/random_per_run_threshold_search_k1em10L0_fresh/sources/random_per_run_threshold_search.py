"""Measure random fixed-accuracy complexity by searching every evaluation run.

The completed capless proposal cohort is reused unchanged.  For each random
evaluation pair, this driver searches balanced-batch count B until the same
absolute KL target is attained, with B=N as the exact terminating endpoint.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from contextlib import contextmanager
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

import ideal_capless_fixed_accuracy_scaling as parent
import random_fixed_accuracy_scaling as random_study
import row_cap_grid_study as grid
import strong_path_baseline_study as controls
import sublinear_pilot_study as phase1
from validate import digest, freeze_json, read_runs


ROOT = Path(__file__).resolve().parent
PARENT = ROOT/'results'/'ideal_capless_fixed_accuracy_scaling'
OUTPUT = PARENT/'random_per_run_threshold_search'
PLAN = ROOT/'RANDOM_PER_RUN_THRESHOLD_SEARCH_PLAN_2026-09-21.md'
CASE = 'ideal_random_per_run_fixed_accuracy_threshold'
PARENT_RELATIVE_L0_FACTOR = 1e-3
SOURCE_NAMES = (
    'random_per_run_threshold_search.py',
    'ideal_capless_fixed_accuracy_scaling.py',
    'random_fixed_accuracy_scaling.py',
    'sublinear_pilot_study.py',
)


def load_json(path):
    return json.loads(Path(path).read_text())


def record_identity(row):
    return (row['target'], int(row['n']), int(row['data_repeat']),
            int(row['algorithm_repeat']), int(row['budget']))


def pair_identity(row):
    return record_identity(row)[:4]


def design(smoke=False, threshold_scale=1., seed_records=None):
    if threshold_scale <= 0:
        raise ValueError('The threshold scale must be strictly positive.')
    source = load_json(PARENT/'design.json')
    targets = source['targets'][:2] if smoke else source['targets']
    n_grid = source['n_grid'][:1] if smoke else source['n_grid']
    pairs = source['random_confirmation_pairs'][:2] if smoke else source[
        'random_confirmation_pairs']
    ratios = ((1/4, 1/2, 3/4, 1.) if smoke
              else tuple(source['random_coarse_ratios']))
    parent_thresholds = {
        target: float(value) for target, value in source['thresholds'].items()}
    thresholds = {
        target: value*float(threshold_scale)
        for target, value in parent_thresholds.items()}
    relative_l0_factor = PARENT_RELATIVE_L0_FACTOR*float(threshold_scale)
    input_sha256 = {
        name: digest(PARENT/name) for name in (
            'design.json', 'audit.json',
            'proposal_confirmation_summary.json',
            'random_confirmation_records.json')}
    if seed_records is not None:
        seed_path = Path(seed_records).resolve()
        input_sha256['seed_records'] = digest(seed_path)
    return {
        'version': 2, 'study': CASE, 'smoke': bool(smoke),
        'targets': list(targets), 'n_grid': list(n_grid),
        'evaluation_pairs': pairs,
        'thresholds': thresholds,
        'parent_thresholds': parent_thresholds,
        'threshold_scale': float(threshold_scale),
        'relative_L0_factor': relative_l0_factor,
        'threshold_rule': (
            f'Per-tree absolute K_star={relative_l0_factor:.12g} times '
            'phase-1 L0_total at N=2048; fixed across N and identical for '
            'both methods.'),
        'success': source['success'],
        'coarse_ratios': list(ratios),
        'bracket_width_fraction_of_N': .10 if smoke else .05,
        'maximum_refinement_rounds': 5 if smoke else 10,
        'selection': (
            'For each evaluation pair independently, first observed suffix '
            'whose K+2*MCSE<=K_star at every observed larger B.'),
        'endpoint': 'B=N exact sequential-singleton sampling; K=0.',
        'estimand': (
            'Mean and range of six per-run empirical minimum-safe B values; '
            'not holdout success of one frozen B.'),
        'sampler_coupling': (
            'Within each evaluation pair, order and commit seeds are derived '
            'with budget key zero and reused across B. Balanced partitions '
            'therefore use one common random permutation. Adjacent B values '
            'are not strictly nested, so successful-suffix selection remains.'),
        'proposal_source': str(PARENT/'proposal_confirmation_summary.json'),
        'seed_records': (str(Path(seed_records).resolve())
                         if seed_records is not None else None),
        'plan_sha256': digest(PLAN),
        'input_sha256': input_sha256,
        'source_sha256': {name: digest(ROOT/name) for name in SOURCE_NAMES},
    }


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


def random_job(config, target, n, budget, pair, role):
    samples = 32 if config['smoke'] else parent.phase1.EVALUATION_SAMPLES
    return random_study.random_job(
        target, n, budget, pair, role, samples)


def coarse_jobs(config):
    jobs = []
    for target in config['targets']:
        for n in config['n_grid']:
            budgets = random_study.ratio_budgets(n, config['coarse_ratios'])
            for pair in config['evaluation_pairs']:
                for budget in budgets:
                    jobs.append(random_job(
                        config, target, n, budget, pair,
                        'per_run_threshold_coarse'))
    return jobs


_BASE_MAKE_TARGET = phase1.make_target


def coupled_make_target(target, n, repeat, biased=True, weak_tail=False,
                        sigma=None, kind='proposal', budget=0):
    """Reuse one sampler stream while preserving the target for every B."""
    del budget
    return _BASE_MAKE_TARGET(
        target, n, repeat, biased, weak_tail, sigma, kind=kind, budget=0)


@contextmanager
def coupled_sampler_context():
    saved = phase1.make_target
    phase1.make_target = coupled_make_target
    try:
        yield
    finally:
        phase1.make_target = saved


def run_one(job, output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    with coupled_sampler_context():
        row = phase1.run_one(job, output)
    row.update(per_run_threshold_study=CASE,
               random_stream_budget_key=0,
               random_stream_coupled_across_budgets=True)
    return row


def execute(output, jobs, workers, state, stage):
    """Run one resumable stage with the B-coupled random adapter."""
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
        raise ValueError(f'Saved rows disagree with {stage}.')
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
                row = future.result()
                rows.append(row)
                stream.write(json.dumps(row, separators=(',', ':'),
                                        allow_nan=False)+'\n')
                stream.flush()
                state['stage_finished'] += 1
                state['updated_utc'] = grid.utc()
                grid.atomic_json(output/'status.json', state)
                if (state['stage_finished'] % 100 == 0
                        or state['stage_finished'] == len(jobs)):
                    print(f'{stage} {state["stage_finished"]}/{len(jobs)} '
                          f'{row["target"]} N={row["n"]} '
                          f'B={row["study_job"]["parameter"]} '
                          f'K={row.get("kl_nats")}', flush=True)
    history_path = output/'execution_history.json'
    history = load_json(history_path) if history_path.exists() else []
    history.append({'stage': stage, 'jobs': len(jobs),
                    'new_runs': len(pending), 'workers': workers,
                    'seconds': perf_counter()-started,
                    'finished_utc': grid.utc()})
    grid.atomic_json(history_path, history)
    lookup = {controls.job_key(row['study_job']): row for row in rows}
    return [lookup[controls.job_key(job)] for job in jobs]


def merge_records(destination, additions):
    lookup = {record_identity(row): row for row in destination}
    if len(lookup) != len(destination):
        raise ValueError('Conflicting duplicate threshold records.')
    for row in additions:
        key = record_identity(row)
        if key in lookup:
            raise ValueError(f'Duplicate threshold observation {key}.')
        lookup[key] = row
    return list(lookup.values())


def rescore_records(records, thresholds):
    """Reapply a new accuracy threshold to threshold-independent KL records."""
    rescored = []
    for original in records:
        row = dict(original)
        threshold = float(thresholds[row['target']])
        row['K_threshold'] = threshold
        row['success'] = bool(
            row['status'] == 'complete'
            and row['K_upper'] is not None
            and float(row['K_upper']) <= threshold)
        rescored.append(row)
    return rescored


def rescore_proposal_summary(rows, thresholds):
    """Attach the strict common threshold to reused exact-zero proposals."""
    rescored = []
    for original in rows:
        row = dict(original)
        threshold = float(thresholds[row['target']])
        row['K_threshold'] = threshold
        row['confirmed'] = bool(
            row['successes'] == row['runs']
            and float(row['maximum_K_upper']) <= threshold)
        row['threshold_rescored_without_rerun'] = True
        rescored.append(row)
    return rescored


def pair_summary(records, identity):
    local = sorted(
        [row for row in records if pair_identity(row) == identity],
        key=lambda row: row['budget'])
    if not local:
        raise ValueError(f'No random observations for {identity}.')
    budgets = [row['budget'] for row in local]
    if len(budgets) != len(set(budgets)):
        raise ValueError(f'Duplicate budgets for {identity}.')
    return local


def first_successful_suffix(rows):
    suffix = True
    candidates = []
    for row in reversed(sorted(rows, key=lambda item: item['budget'])):
        suffix = suffix and bool(row['success'])
        if suffix:
            candidates.append(int(row['budget']))
    return min(candidates) if candidates else None


def bracket(rows, n):
    endpoint = next((row for row in rows if row['budget'] == n), None)
    if endpoint is None or not endpoint['success']:
        raise AssertionError('The exact B=N endpoint must be observed and pass.')
    high = first_successful_suffix(rows)
    if high is None:
        raise AssertionError('A successful suffix must include B=N.')
    low = max((row['budget'] for row in rows if row['budget'] < high),
              default=0)
    return int(low), int(high)


def all_pair_identities(config):
    return [(target, n, int(data), int(algorithm))
            for target in config['targets'] for n in config['n_grid']
            for data, algorithm in config['evaluation_pairs']]


def refine(output, config, workers, state, records):
    stage_rows = {}
    for round_index in range(config['maximum_refinement_rounds']):
        jobs = []
        for identity in all_pair_identities(config):
            target, n, data, algorithm = identity
            rows = pair_summary(records, identity)
            low, high = bracket(rows, n)
            tolerance = max(1, int(ceil(
                config['bracket_width_fraction_of_N']*n)))
            if high-low <= tolerance:
                continue
            midpoint = (low+high)//2
            if midpoint in {row['budget'] for row in rows}:
                raise AssertionError(f'Refinement stalled at {identity}.')
            jobs.append(random_job(
                config, target, n, midpoint, [data, algorithm],
                f'per_run_threshold_refine_{round_index}'))
        if not jobs:
            return records, stage_rows
        stage = f'per_run_threshold_refine_{round_index}'
        raw = execute(output, jobs, workers, state, stage)
        stage_rows[stage] = raw
        additions = [random_study.record(row, config['thresholds']) for row in raw]
        records = merge_records(records, additions)
    for identity in all_pair_identities(config):
        _low, _high = bracket(pair_summary(records, identity), identity[1])
        tolerance = max(1, int(ceil(
            config['bracket_width_fraction_of_N']*identity[1])))
        if _high-_low > tolerance:
            raise AssertionError(f'Refinement limit reached at {identity}.')
    return records, stage_rows


def selections_and_summary(config, records):
    selections, grouped = [], defaultdict(list)
    for identity in all_pair_identities(config):
        target, n, data, algorithm = identity
        rows = pair_summary(records, identity)
        low, high = bracket(rows, n)
        chosen = next(row for row in rows if row['budget'] == high)
        item = {
            'target': target, 'n': n, 'data_repeat': data,
            'algorithm_repeat': algorithm, 'budget': high,
            'lower_observed_budget': low, 'bracket_width': high-low,
            'bracket_width_over_N': (high-low)/n,
            'K': chosen['K'], 'K_upper': chosen['K_upper'],
            'K_threshold': chosen['K_threshold'], 'success': chosen['success'],
            'observed_budgets': [row['budget'] for row in rows],
        }
        selections.append(item)
        grouped[(target, n)].append(item)
    summary = []
    for (target, n), rows in sorted(grouped.items()):
        budgets = np.asarray([row['budget'] for row in rows], dtype=float)
        summary.append({
            'target': target, 'n': n, 'method': 'random',
            'runs': len(rows), 'successes': sum(row['success'] for row in rows),
            'confirmed': all(row['success'] for row in rows),
            'Q': float(budgets.mean()), 'Q_min': float(budgets.min()),
            'Q_max': float(budgets.max()), 'Q_values': budgets.tolist(),
            'Q_se': float(budgets.std(ddof=1)/np.sqrt(len(budgets))),
            'K_threshold': rows[0]['K_threshold'],
            'maximum_K_upper': max(row['K_upper'] for row in rows),
            'fresh_target_draws': sorted({row['data_repeat'] for row in rows}),
            'fresh_sampler_streams': sorted(
                {row['algorithm_repeat'] for row in rows}),
            'selection_source': 'per-run fixed-accuracy threshold search',
            'maximum_bracket_width_over_N': max(
                row['bracket_width_over_N'] for row in rows),
        })
    return selections, summary


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
    maximum = max(max(row['Q_max'] for row in proposal+random_rows),
                  max(config['n_grid']))
    for ax, target in zip(axes.flat, config['targets']):
        p_rows = [row for row in proposal if row['target'] == target]
        r_rows = [row for row in random_rows if row['target'] == target]
        parent.draw_curve(ax, p_rows, blue, 'proposal')
        parent.draw_curve(ax, r_rows, orange, 'random')
        bounds = np.asarray(config['n_grid'], dtype=float)
        ax.plot(bounds, bounds, color='.45', linestyle=':', linewidth=1.5)
        ax.set_title(titles[target], fontsize=14)
        ax.grid(alpha=.23)
        ax.set_xlim(min(config['n_grid'])-450, max(config['n_grid'])+450)
        ax.set_ylim(0, maximum*1.08)
        formatter = FuncFormatter(lambda value, _pos: f'{int(value):,}')
        ax.xaxis.set_major_formatter(formatter)
        ax.yaxis.set_major_formatter(formatter)
    for ax in axes[:, 0]:
        ax.set_ylabel(r'Mean raw queries $Q$', fontsize=12)
    for ax in axes[-1, :]:
        ax.set_xlabel(r'Sequence length $N$', fontsize=12)
    fig.suptitle('Raw fixed-accuracy query scaling on ideal forest targets',
                 fontsize=18, y=.985)
    exponent = int(round(np.log10(config['relative_L0_factor'])))
    fig.text(.5, .945,
             (r'$\mathbb{E}[W/X]=1$, exact oracle; '
              rf'$K_\star=10^{{{exponent}}}L_0$; random searched per run'),
             ha='center', va='center', fontsize=13)
    handles = [
        Line2D([0], [0], color=blue, marker='o', linewidth=2.,
               markersize=6, label='Proposal'),
        Line2D([0], [0], color=orange, marker='s', markerfacecolor='white',
               linewidth=2., markersize=6,
               label='Random per-run threshold'),
        Line2D([0], [0], color='.45', linestyle=':', linewidth=1.5,
               label='Exact sequential-singleton reference')]
    fig.legend(handles=handles, loc='upper center', bbox_to_anchor=(.5, .91),
               ncol=3, frameon=False, fontsize=10.5)
    fig.tight_layout(rect=(0, 0, 1, .86), h_pad=2., w_pad=1.4)
    stem = output/'random_per_run_threshold_linear'
    fig.savefig(stem.with_suffix('.png'), dpi=220)
    fig.savefig(stem.with_suffix('.pdf'))
    plt.close(fig)
    freeze_json(output/'figure_data.json', {
        'proposal': proposal, 'random': random_rows,
        'random_estimand': config['estimand'],
        'axes': 'linear-linear', 'n_grid': config['n_grid'],
        'display_x_offset_fraction': .006})
    return stem.with_suffix('.png'), stem.with_suffix('.pdf')


def audit(output, config, new_stage_rows, records, selections, summary,
          reused_record_count=0):
    for rows in new_stage_rows.values():
        for row in rows:
            if row['kind'] != 'baseline':
                raise AssertionError('Threshold search must contain only random baselines.')
            if row['total'] != row['study_job']['parameter']:
                raise AssertionError('Random Q must equal B.')
            if (row.get('random_stream_budget_key') != 0
                    or not row.get('random_stream_coupled_across_budgets')):
                raise AssertionError('Random sampler streams are not B-coupled.')
    if len(selections) != len(all_pair_identities(config)):
        raise AssertionError('Every evaluation run needs one selected budget.')
    if not all(row['success'] for row in selections):
        raise AssertionError('Every per-run selected endpoint must pass.')
    if any(row['bracket_width_over_N']
           > config['bracket_width_fraction_of_N']+1e-12
           for row in selections):
        raise AssertionError('A threshold bracket is wider than specified.')
    for identity in all_pair_identities(config):
        rows = pair_summary(records, identity)
        endpoint = next(row for row in rows if row['budget'] == identity[1])
        if not endpoint['success']:
            raise AssertionError('An exact singleton endpoint failed.')
    result = {
        'status': 'pass', 'cells': len(summary),
        'per_run_searches': len(selections),
        'all_selected_random_runs_pass': True,
        'all_exact_singleton_endpoints_pass': True,
        'maximum_allowed_bracket_width_over_N':
            config['bracket_width_fraction_of_N'],
        'observed_maximum_bracket_width_over_N': max(
            row['bracket_width_over_N'] for row in selections),
        'total_budget_records': len(records),
        'reused_budget_records': int(reused_record_count),
        'random_stream_budget_key': 0,
        'random_stream_coupled_across_budgets': True,
        'random_budget_selected_from_evaluation_curve': True,
        'not_untouched_fixed_B_confirmation': True,
        'query_identity_verified': True,
        'source_sha256': config['source_sha256'],
        'input_sha256': config['input_sha256']}
    freeze_json(output/'audit.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=8)
    parser.add_argument('--output', type=Path, default=OUTPUT)
    parser.add_argument('--smoke', action='store_true')
    parser.add_argument(
        '--threshold-scale', type=float, default=1.,
        help='Multiply the parent 1e-3 L0 thresholds by this positive value.')
    parser.add_argument(
        '--seed-records', type=Path,
        help=('Reuse threshold-independent KL observations from a previous '
              'per-run search, then evaluate only newly required budgets.'))
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('Please use at least one worker.')
    if args.threshold_scale <= 0:
        parser.error('--threshold-scale must be strictly positive.')
    if args.threshold_scale != 1. and args.output == OUTPUT:
        parser.error('A scaled threshold requires an explicit --output path.')
    config = design(args.smoke, args.threshold_scale, args.seed_records)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    with (output/'runner.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        freeze_json(output/'design.json', config)
        snapshot_sources(output, config)
        if not (output/'environment.json').exists():
            freeze_json(output/'environment.json', environment_metadata())
        state = {'status': 'running', 'stage': 'initializing',
                 'pid': os.getpid(), 'workers': args.workers,
                 'output': str(output), 'started_utc': grid.utc(),
                 'updated_utc': grid.utc()}
        grid.atomic_json(output/'status.json', state)
        started = perf_counter()
        try:
            new_stage_rows = {}
            reused_record_count = 0
            if args.seed_records is not None:
                records = rescore_records(
                    load_json(args.seed_records), config['thresholds'])
                reused_record_count = len(records)
            else:
                jobs = coarse_jobs(config)
                raw = execute(
                    output, jobs, args.workers, state,
                    'per_run_threshold_coarse')
                new_stage_rows['per_run_threshold_coarse'] = raw
                records = [random_study.record(row, config['thresholds'])
                           for row in raw]
            records, refinement_rows = refine(
                output, config, args.workers, state, records)
            new_stage_rows.update(refinement_rows)
            selections, summary = selections_and_summary(config, records)
            proposal = rescore_proposal_summary(
                [row for row in load_json(
                    PARENT/'proposal_confirmation_summary.json')
                 if row['target'] in config['targets']
                 and row['n'] in config['n_grid']],
                config['thresholds'])
            if not all(row['maximum_K_upper'] == 0. for row in proposal):
                raise AssertionError(
                    'Only structural exact-zero proposal results may be '
                    'reused under a stricter threshold.')
            freeze_json(output/'records.json', records)
            freeze_json(output/'selections.json', selections)
            freeze_json(output/'random_summary.json', summary)
            plot_results(output, config, proposal, summary)
            checked = audit(
                output, config, new_stage_rows, records, selections, summary,
                reused_record_count=reused_record_count)
            state.update(status='complete', stage='complete',
                         seconds=perf_counter()-started,
                         per_run_searches=checked['per_run_searches'],
                         reused_budget_records=reused_record_count,
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
