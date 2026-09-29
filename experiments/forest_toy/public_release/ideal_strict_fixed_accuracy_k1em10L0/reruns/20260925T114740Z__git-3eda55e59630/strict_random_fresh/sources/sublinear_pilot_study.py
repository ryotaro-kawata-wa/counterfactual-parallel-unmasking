"""Run the exact-oracle phase of the four-forest sublinear-query pilot.

The study separates proposal-only tuning from matched random evaluation.  It
first runs a common anchor grid at every N, then performs a dense per-(tree, N)
rescue only for the three smallest N when no anchor beats matched random by the
provisional factor-three rule.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from contextlib import contextmanager
import fcntl
import hashlib
import json
from math import ceil, log
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
from forest_kl import initial_edges, load_backend as load_forest_backend
from matching_random_expectation import same_batch_probability
from minimal_oracle import MinimalOracle, load_backend as load_oracle_backend
from profile_minimal import weighted_summary
from robustness_study import seeds_for
from validate import digest, freeze_json, read_runs
from weighted_oracle import make_weighted_target


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT/'results'/'sublinear_pilot_study'
CASE = 'sublinear_phase1_constant_exact_prefix_fields'
TARGETS = ('matching', 'path', 'binary', 'stars_original')
N_GRID = (2048, 4096, 6144, 8192, 10240, 12288, 14336, 16384)
SMALL_N = (2048, 4096, 6144)
DATA_REPEAT = 170
PROPOSAL_ALGORITHM = 270
RANDOM_ALGORITHMS = tuple(range(280, 288))
EVALUATION_SAMPLES = 128
EVALUATION_EXACT_ARITY = 4
PROPOSAL_RESCUE_CAP = 480
RANDOM_RESCUE_CAP = 3840

SOURCES = tuple(dict.fromkeys((*standard.SOURCES, 'matching_random_expectation.py',
    'sublinear_pilot_study.py', 'report_sublinear_pilot.py',
    'test_sublinear_pilot.py')))


def named_seed(label: str, value: int) -> int:
    """Please derive stable independent streams without Python's salted hash."""
    payload = f'sublinear-pilot-v1|{label}|{value}'.encode()
    return int.from_bytes(hashlib.sha256(payload).digest()[:8], 'little')


def master_field_seed(data_repeat: int) -> int:
    return named_seed('master-fields', data_repeat)


def coupling_cap(target: str, n: int) -> float:
    if target == 'matching':
        return .5
    if target == 'path':
        return .25
    if target == 'binary':
        return 1/6
    if target == 'stars_original':
        return .5/max(16, ceil(n**.5))
    raise ValueError('Please use one of the four frozen forest targets.')


def make_target(target, n, repeat, biased=True, weak_tail=False, sigma=None,
                kind='proposal', budget=0):
    """Use one unary master prefix while retaining target-specific hidden graphs."""
    del biased, weak_tail, sigma
    data, algorithm = pivot.seed_pair(repeat)
    prototype, data_seeds = make_weighted_target(
        target, n, data, 'original_uniform', kind, budget)
    fields = np.random.default_rng(master_field_seed(data)).uniform(-1., 1., max(N_GRID))[:n]
    oracle = MinimalOracle(n, prototype.edges, prototype.edge_strengths,
                           prototype.theta, fields, vocab=2048)
    oracle.weight_seed = prototype.weight_seed
    oracle.field_seed = master_field_seed(data)
    oracle.tail_shape = None
    oracle.target_law = CASE
    sampler = seeds_for('path', n, algorithm, kind, budget)
    return oracle, [data_seeds[0], *sampler[1:]]


@contextmanager
def prefix_target_context():
    """Please patch only inside a worker-local call and restore immediately."""
    saved = standard.make_target
    standard.make_target = make_target
    try:
        yield
    finally:
        standard.make_target = saved


def q0(p: int, m: int) -> int:
    return p*(2*p-1)*m


def odd_round(value: float) -> int:
    """Round to the nearest positive odd integer, resolving ties upward."""
    lower = int(np.floor(value))
    if lower % 2 == 0:
        lower -= 1
    lower = max(1, lower)
    upper = lower+2
    return lower if value-lower < upper-value else upper


def scaled_m(anchor: int, n: int) -> int:
    return max(3, odd_round(anchor*log(n)/log(16384)))


def m_for_r(n: int, p: int, target_r: float):
    """Return the largest feasible odd M whose nominal q0 does not exceed rN."""
    maximum = int(np.floor(target_r*n/(p*(2*p-1))))
    if maximum % 2 == 0:
        maximum -= 1
    return maximum if maximum >= 3 else None


def actual_r(n: int, p: int, m: int) -> float:
    return q0(p, m)/n


def lambda_grid(target: str):
    if target == 'matching':
        return (.02, .04, .06, .09, .12)
    if target == 'stars_original':
        return (.02, .04, .08, .12, .20)
    return (.04, .08, .12, .16, .20)


def rescue_spec(target: str):
    if target == 'matching':
        return {'facets': ((3, 9), (4, 9), (6, 9), (8, 9), (4, 18)),
                'screen_r': (.30, .60, .85), 'lambda0': .06,
                'dense_r': (.15, .92)}
    if target == 'path':
        return {'facets': ((6, 18), (7, 18), (8, 18), (9, 18), (10, 18),
                           (8, 12), (8, 36)),
                'screen_r': (.35, .60, .80), 'lambda0': .12,
                'dense_r': (.20, .85)}
    if target == 'binary':
        return {'facets': ((6, 18), (8, 18), (10, 18), (12, 18), (16, 18),
                           (10, 9), (10, 36), (12, 36)),
                'screen_r': (.35, .60, .80), 'lambda0': .12,
                'dense_r': (.20, .85)}
    if target == 'stars_original':
        return {'facets': ((4, 36), (6, 36), (8, 36), (10, 36), (6, 17)),
                'screen_r': (.15, .275, .40), 'lambda0': .12,
                'dense_r': (.10, .42)}
    raise ValueError('Please use a supported rescue target.')


def anchor_settings(target: str, n: int):
    """Return the common full-N anchors plus the agreed small-N sentinels."""
    if target == 'matching':
        base = [(4, m, 9, .06) for m in (49, 57, 65)]
    elif target == 'path':
        base = [(7, 61, 18, .12), (8, 45, 18, .12),
                (8, 53, 18, .12), (8, 61, 18, .12)]
    elif target == 'binary':
        base = [(10, 41, 18, .12), (10, 53, 18, .12),
                (12, 33, 36, .06), (12, 41, 18, .06)]
    elif target == 'stars_original':
        base = [(4, 33, 36, .12), (6, 17, 36, .12), (6, 21, 36, .12),
                (6, 25, 36, .12), (8, 13, 36, .12)]
    else:
        raise ValueError('Please use a supported target.')
    settings = {(p, scaled_m(m, n), d, lam) for p, m, d, lam in base}
    sentinels = {
        ('path', 2048): ((7, 17, 18, .12), (8, 13, 18, .12), (9, 9, 18, .12)),
        ('path', 4096): ((7, 35, 18, .12), (8, 27, 18, .12), (9, 21, 18, .12)),
        ('path', 6144): ((7, 53, 18, .12), (8, 41, 18, .12),
                         (8, 45, 18, .12), (9, 31, 18, .12)),
        ('binary', 2048): ((8, 13, 18, .12), (10, 7, 18, .12), (12, 5, 18, .12)),
        ('binary', 4096): ((8, 27, 18, .12), (10, 17, 18, .12), (12, 11, 18, .12)),
        ('binary', 6144): ((8, 39, 18, .12), (10, 25, 18, .12),
                           (12, 17, 18, .12), (12, 17, 36, .06)),
    }
    settings.update(sentinels.get((target, n), ()))
    return sorted(settings)


def design(smoke=False):
    n_grid = (512, 768) if smoke else N_GRID
    small_n = (512,) if smoke else SMALL_N
    random_algorithms = (280, 281) if smoke else RANDOM_ALGORITHMS
    return {
        'version': 1, 'study': 'four_forest_sublinear_phase1', 'smoke': smoke,
        'targets': list(TARGETS), 'n_grid': list(n_grid), 'small_n': list(small_n),
        'vocab': 2048, 'oracle': 'exact', 'edge_law': 'constant',
        'coupling': {'matching': '.5', 'path': '.25', 'binary': '1/6',
                     'stars_original': '.5/max(16,ceil(sqrt(N)))'},
        'fields': 'One iid Uniform[-1,1] master vector, prefix-coupled across all targets and N.',
        'data_repeat': DATA_REPEAT, 'proposal_algorithm_repeat': PROPOSAL_ALGORITHM,
        'random_algorithm_repeats': list(random_algorithms),
        'query_cap': 'Each proposal is censored immediately before a submission would make Q>N.',
        'metrics': ['KL_per_token', 'KL_total', 'relative_KL=L/L0'],
        'provisional_win': 'complete, Q<N, and proposal KL/token <= matched-random mean / 3',
        'selection_independence': 'Stage-A/B/C facet selection uses proposal outcomes only. Random is evaluated after proposal grids are frozen.',
        'rescue': {'trigger': 'No provisional anchor win at a small-N (tree,N) cell.',
                   'proposal_job_cap': 40 if smoke else PROPOSAL_RESCUE_CAP,
                   'random_schedule_cap': 80 if smoke else RANDOM_RESCUE_CAP,
                   'stages': 'A facet screen; B lambda pilot on top two; C dense r-lambda ribbon on top one.'},
        'evaluation': {'samples_per_large_factor': 16 if smoke else EVALUATION_SAMPLES,
                       'exact_boundary_arity': EVALUATION_EXACT_ARITY},
        'phase_boundary': 'Stop after exact-oracle constant-edge phase 1; do not start edge/noise sweeps.',
        'source_sha256': {name: digest(ROOT/name) for name in SOURCES},
    }


def proposal_job(config, target, n, p, m, d, lam):
    tau = float(lam*coupling_cap(target, n))
    return {'kind': 'proposal', 'target': target, 'n': int(n),
            'data': DATA_REPEAT, 'algorithm': PROPOSAL_ALGORITHM,
            'setting': [int(p), int(m), int(d), tau],
            'evaluation_samples': config['evaluation']['samples_per_large_factor'],
            'evaluation_exact_arity': config['evaluation']['exact_boundary_arity']}


def random_job(config, target, n, budget, algorithm):
    return {'kind': 'baseline', 'target': target, 'n': int(n),
            'data': DATA_REPEAT, 'algorithm': int(algorithm),
            'family': 'fixed', 'ordering': 'random', 'parameter': int(budget),
            'evaluation_samples': config['evaluation']['samples_per_large_factor'],
            'evaluation_exact_arity': config['evaluation']['exact_boundary_arity']}


def job_origin(job, stage, lam, target_r=None, label=None):
    p, m, d, _ = job['setting']
    return {'stage': stage, 'target': job['target'], 'n': job['n'],
            'p': p, 'M': m, 'd': d, 'lambda': float(lam),
            'target_r': target_r, 'actual_r': actual_r(job['n'], p, m),
            'q0': q0(p, m), 'label': label}


def add_planned(store, job, origin):
    key = controls.job_key(job)
    if key not in store:
        store[key] = {'job': job, 'origins': []}
    if origin not in store[key]['origins']:
        store[key]['origins'].append(origin)


def initial_plan(config):
    plan = {}
    if config['smoke']:
        for target in TARGETS:
            for n in config['n_grid']:
                job = proposal_job(config, target, n, 3, 3, 9, .08)
                add_planned(plan, job, job_origin(job, 'anchor', .08, label='smoke'))
        return plan
    for target in TARGETS:
        for n in config['n_grid']:
            for p, m, d, lam in anchor_settings(target, n):
                job = proposal_job(config, target, n, p, m, d, lam)
                add_planned(plan, job, job_origin(job, 'anchor', lam,
                                                  label='anchor_or_sentinel'))
    return plan


def stage_a_plan(config, failed_cells):
    plan = {}
    for target, n in failed_cells:
        spec = rescue_spec(target)
        facets = spec['facets'][:2] if config['smoke'] else spec['facets']
        rs = (.40, .75) if config['smoke'] else spec['screen_r']
        for p, d in facets:
            for r in rs:
                m = m_for_r(n, p, r)
                if m is None:
                    continue
                job = proposal_job(config, target, n, p, m, d, spec['lambda0'])
                add_planned(plan, job, job_origin(job, 'rescue_A', spec['lambda0'], r))
    return plan


def _manual_auc(xs, ys):
    if not xs:
        return None
    order = np.argsort(xs)
    x = np.asarray(xs)[order]
    y = np.asarray(ys)[order]
    if len(x) == 1 or x[-1] == x[0]:
        return float(y.mean())
    return float(np.sum((x[1:]-x[:-1])*(y[1:]+y[:-1])/2)/(x[-1]-x[0]))


def first_screen_incomplete(row):
    screens = row.get('screen_observations') or []
    return row['status'] == 'censored' and (not screens or not screens[0].get('complete', False))


def facet_ranking(rows, plan, stage='rescue_A'):
    """Rank facets using only complete proposal observations from one stage."""
    grouped = defaultdict(list)
    for row in rows:
        key = controls.job_key(row['study_job'])
        origins = [o for o in plan.get(key, {}).get('origins', []) if o['stage'] == stage]
        for origin in origins:
            grouped[(origin['target'], origin['n'], origin['p'], origin['d'])].append((row, origin))
    result = defaultdict(list)
    for (target, n, p, d), values in grouped.items():
        complete = [(row, origin) for row, origin in values if row['status'] == 'complete']
        xs = [origin['actual_r'] for row, origin in complete]
        logs = [np.log10(max(row['kl_per_token'], 1e-300)) for row, origin in complete]
        item = {'target': target, 'n': n, 'p': p, 'd': d,
                'planned': len(values), 'complete': len(complete),
                'first_screen_incomplete': sum(first_screen_incomplete(row) for row, _ in values),
                'log_auc': _manual_auc(xs, logs),
                'mean_Q_over_N': (float(np.mean([row['total']/n for row, _ in complete]))
                                  if complete else None),
                'best_KL_per_token': min((row['kl_per_token'] for row, _ in complete), default=None),
                'mean_committed_fraction': float(np.mean([row.get('committed_tokens', 0)/n
                                                          for row, _ in values]))}
        result[(target, n)].append(item)
    for cell in result:
        result[cell].sort(key=lambda x: (-x['complete'],
            float('inf') if x['log_auc'] is None else x['log_auc'],
            float('inf') if x['mean_Q_over_N'] is None else x['mean_Q_over_N'], x['p'], x['d']))
    return result


def stage_b_plan(config, rankings):
    plan, selected = {}, {}
    for cell, ranked in sorted(rankings.items()):
        target, n = cell
        top = ranked[:min(2, len(ranked))]
        selected[f'{target}|{n}'] = top
        middle_r = .60 if target != 'stars_original' else .275
        lambdas = ((rescue_spec(target)['lambda0']/2, rescue_spec(target)['lambda0'])
                   if config['smoke'] else lambda_grid(target))
        for facet in top:
            p, d = facet['p'], facet['d']
            m = m_for_r(n, p, middle_r)
            if m is None:
                continue
            for lam in lambdas:
                job = proposal_job(config, target, n, p, m, d, lam)
                add_planned(plan, job, job_origin(job, 'rescue_B', lam, middle_r))
    return plan, selected


def select_stage_c(rows, plan, failed_cells):
    """Choose one facet per cell from Stage B, without consulting random rows."""
    candidates = facet_ranking(rows, plan, stage='rescue_B')
    fallback = facet_ranking(rows, plan, stage='rescue_A')
    selected = {}
    for cell in failed_cells:
        ranked = candidates.get(cell, []) or fallback.get(cell, [])
        if ranked:
            selected[cell] = ranked[0]
    return selected, candidates


def dense_m_values(n, p, interval, count=9):
    values = []
    for r in np.linspace(interval[0], interval[1], count):
        m = m_for_r(n, p, float(r))
        if m is not None and m not in values:
            values.append(m)
    return values


def stage_c_plan(config, selected, current_rescue_jobs):
    candidates = defaultdict(list)
    for (target, n), facet in selected.items():
        p, d = facet['p'], facet['d']
        count = 3 if config['smoke'] else 9
        lambdas = ((rescue_spec(target)['lambda0']/2, rescue_spec(target)['lambda0'])
                   if config['smoke'] else lambda_grid(target))
        for m in dense_m_values(n, p, rescue_spec(target)['dense_r'], count):
            for lam in lambdas:
                job = proposal_job(config, target, n, p, m, d, lam)
                candidates[(target, n)].append(
                    (job, job_origin(job, 'rescue_C', lam, actual_r(n, p, m))))

    cap = config['rescue']['proposal_job_cap']
    remaining = max(0, cap-len(current_rescue_jobs))
    ordered_cells = sorted(selected, key=lambda cell: (
        -selected[cell]['complete'],
        float('inf') if selected[cell]['log_auc'] is None else selected[cell]['log_auc'],
        float('inf') if selected[cell]['mean_Q_over_N'] is None
        else selected[cell]['mean_Q_over_N'], cell))
    plan, omitted = {}, []
    existing = set(current_rescue_jobs)
    for cell in ordered_cells:
        local = sorted(candidates[cell], key=lambda pair: (
            pair[1]['actual_r'], pair[1]['lambda']))
        for job, origin in local:
            key = controls.job_key(job)
            if key in existing or key in plan:
                add_planned(plan, job, origin)
            elif remaining > 0:
                add_planned(plan, job, origin)
                remaining -= 1
            else:
                omitted.append({'job': job, 'origin': origin,
                                'reason': 'proposal_rescue_cap'})
    return plan, omitted


def merge_plans(destination, source):
    for key, entry in source.items():
        if key not in destination:
            destination[key] = {'job': entry['job'], 'origins': []}
        for origin in entry['origins']:
            if origin not in destination[key]['origins']:
                destination[key]['origins'].append(origin)


def run_one(job, output, query_limit='target_n'):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    with prefix_target_context():
        row = standard.run_job(job, output, query_limit=query_limit)
    row.update(sublinear_study=CASE,
               master_field_seed=master_field_seed(job['data']),
               artifact_partition=f'{job["target"]}/N{job["n"]}')
    if job['kind'] == 'proposal':
        p, m, _, tau = job['setting']
        row.update(q0=q0(p, m), q0_over_n=actual_r(job['n'], p, m),
                   lambda_over_X=tau/coupling_cap(job['target'], job['n']))
    return row


def atomic_json(path, value):
    grid.atomic_json(Path(path), value)


def execute_jobs(out, config, jobs, kind, stage, workers, state):
    """Append unique jobs to one resumable stream while preserving manifests."""
    jobs = sorted({controls.job_key(job): job for job in jobs}.values(),
                  key=controls.job_key)
    manifests = out/'manifests'
    manifests.mkdir(parents=True, exist_ok=True)
    freeze_json(manifests/f'{stage}_{kind}_jobs.json', jobs)
    path = out/f'{kind}_runs.jsonl'
    rows = read_runs(path)
    done = {controls.job_key(row['study_job']): row for row in rows}
    if len(done) != len(rows):
        raise ValueError(f'Please remove duplicate records from {path}.')
    pending = [job for job in jobs if controls.job_key(job) not in done]
    state.update(stage=stage, stage_kind=kind, stage_jobs=len(jobs),
                 stage_finished=len(jobs)-len(pending), updated_utc=grid.utc())
    atomic_json(out/'status.json', state)
    started = perf_counter()
    artifacts = out/'artifacts'
    artifacts.mkdir(exist_ok=True)
    if pending:
        with ProcessPoolExecutor(max_workers=workers) as pool, path.open('a') as stream:
            futures = [pool.submit(run_one, job,
                        artifacts/job['target']/f'N{job["n"]}') for job in pending]
            for future in as_completed(futures):
                row = future.result()
                rows.append(row)
                stream.write(json.dumps(row, separators=(',', ':'), allow_nan=False)+'\n')
                stream.flush()
                state['stage_finished'] += 1
                state['updated_utc'] = grid.utc()
                atomic_json(out/'status.json', state)
                if state['stage_finished'] % 10 == 0 or state['stage_finished'] == len(jobs):
                    print(f'{stage}/{kind} {state["stage_finished"]}/{len(jobs)} '
                          f'{row["target"]} N={row["n"]} Q={row["total"]} '
                          f'KL/N={row.get("kl_per_token")} {row["status"]}', flush=True)
    history_path = out/'execution_history.json'
    history = json.loads(history_path.read_text()) if history_path.exists() else []
    history.append({'stage': stage, 'kind': kind, 'requested_jobs': len(jobs),
                    'new_runs': len(pending), 'workers': workers,
                    'seconds': perf_counter()-started, 'finished_utc': grid.utc()})
    atomic_json(history_path, history)
    lookup = {controls.job_key(row['study_job']): row for row in rows}
    return [lookup[controls.job_key(job)] for job in jobs]


def ensure_profiles(out, config):
    profiles = []
    directory = out/'target_profiles'
    directory.mkdir(exist_ok=True)
    prefix_hashes = {}
    for target in TARGETS:
        for n in config['n_grid']:
            repeat = pivot.repeat_id(DATA_REPEAT, PROPOSAL_ALGORITHM)
            oracle, seeds = make_target(target, n, repeat)
            rows, weights, total = initial_edges(oracle)
            path = directory/f'{target}_N{n}_data{DATA_REPEAT}.npz'
            arrays = {'edges': oracle.edges, 'theta': oracle.edge_strengths,
                      'fields': oracle.fields, 'initial_rows': rows,
                      'initial_edge_kl': weights}
            if path.exists():
                with np.load(path) as saved:
                    for name, values in arrays.items():
                        np.testing.assert_array_equal(saved[name], values)
            else:
                np.savez_compressed(path, **arrays)
            # The reused proposal runner loads this profile during its passive
            # diagnostics.  N-partitioned roots avoid the legacy filename's
            # otherwise ambiguous reuse across several N values.
            legacy = (out/'artifacts'/target/f'N{n}'/'target_profiles'/
                      f'{target}_{standard.CASE}_seed{repeat}.npz')
            legacy.parent.mkdir(parents=True, exist_ok=True)
            if legacy.exists():
                with np.load(legacy) as saved:
                    for name, values in arrays.items():
                        np.testing.assert_array_equal(saved[name], values)
            else:
                np.savez_compressed(legacy, **arrays)
            fields_hash = controls.array_hash(oracle.fields, '<f8')
            prefix_hashes.setdefault(n, fields_hash)
            assert prefix_hashes[n] == fields_hash
            profiles.append({'target': target, 'n': n, 'data_repeat': DATA_REPEAT,
                'algorithm_repeat_for_snapshot': PROPOSAL_ALGORITHM, 'seeds': seeds,
                'field_seed': oracle.field_seed, 'fields_sha256': fields_hash,
                'theta': oracle.theta, 'maximum_degree': oracle.max_degree,
                'edge_count': len(oracle.edges), 'L0_total': float(total),
                'L0_per_token': float(total/n),
                'edge_KL': weighted_summary([weights]),
                'snapshot': str(path.relative_to(out)), 'sha256': digest(path)})
    # Please verify true prefix equality, not merely equal seed labels.
    master = np.random.default_rng(master_field_seed(DATA_REPEAT)).uniform(
        -1., 1., max(config['n_grid']))
    for item in profiles:
        with np.load(out/item['snapshot']) as saved:
            np.testing.assert_array_equal(saved['fields'], master[:item['n']])
    freeze_json(out/'target_profiles.json', profiles)
    return profiles


def profile_lookup(profiles):
    return {(row['target'], row['n']): row for row in profiles}


def random_jobs_for_proposals(config, proposal_rows):
    keys = sorted({(row['target'], row['n'], int(row['total'])) for row in proposal_rows
                   if row['status'] == 'complete' and row['target'] != 'matching'})
    return [random_job(config, target, n, budget, algorithm)
            for target, n, budget in keys
            for algorithm in config['random_algorithm_repeats']]


def random_summary(target, n, budget, random_rows, profiles):
    if target == 'matching':
        l0 = profile_lookup(profiles)[(target, n)]['L0_per_token']
        mean = l0*same_batch_probability(n, budget)
        return {'target': target, 'n': n, 'budget': budget, 'count': 'analytic',
                'mean': mean, 'schedule_se': 0., 'measurement_se': 0.,
                'combined_se': 0., 'minimum': mean, 'maximum': mean,
                'individual': [], 'formula': 'exact_matching_schedule_expectation'}
    selected = [row for row in random_rows if row['target'] == target
                and row['n'] == n and int(row['study_job']['parameter']) == budget]
    if not selected:
        return None
    selected.sort(key=lambda row: row['algorithm_repeat'])
    values = np.asarray([row['kl_per_token'] for row in selected], dtype=float)
    k = len(values)
    schedule_se = float(values.std(ddof=1)/np.sqrt(k)) if k > 1 else None
    measurement_se = float(np.sqrt(sum(row.get('kl_mc_se_per_token', 0.)**2
                                       for row in selected))/k)
    combined = (float(np.sqrt(schedule_se**2+measurement_se**2))
                if schedule_se is not None else measurement_se)
    return {'target': target, 'n': n, 'budget': budget, 'count': k,
            'mean': float(values.mean()), 'schedule_se': schedule_se,
            'measurement_se': measurement_se, 'combined_se': combined,
            'minimum': float(values.min()), 'maximum': float(values.max()),
            'individual': values.tolist(),
            'algorithms': [row['algorithm_repeat'] for row in selected],
            'formula': ('eight_balanced_random_schedules' if k == 8
                        else 'balanced_random_schedules')}


def comparisons(proposal_rows, random_rows, profiles):
    records = []
    profiles_by_cell = profile_lookup(profiles)
    for row in proposal_rows:
        profile = profiles_by_cell[(row['target'], row['n'])]
        base = {'proposal_job_key': controls.job_key(row['study_job']),
                'target': row['target'], 'n': row['n'], 'status': row['status'],
                'Q': row['total'], 'Q_over_N': row['total']/row['n'],
                'q0': row['q0'], 'q0_over_N': row['q0_over_n'],
                'p': row['palette'], 'M': row['colorings'], 'd': row['d'],
                'lambda': row['lambda_over_X'], 'tau': row['screen_threshold'],
                'L0_total': profile['L0_total'], 'L0_per_token': profile['L0_per_token'],
                'committed_fraction': row.get('committed_tokens', 0)/row['n'],
                'first_screen_incomplete': first_screen_incomplete(row),
                'abort_stage': (row.get('budget_stop') or {}).get('stage')}
        if row['status'] != 'complete':
            records.append({**base, 'KL_per_token': None, 'KL_total': None,
                'relative_KL': None, 'proposal_mc_se': None, 'random': None,
                'random_over_proposal': None, 'win_factor3': False,
                'win_conservative': False})
            continue
        random = random_summary(row['target'], row['n'], int(row['total']),
                                random_rows, profiles)
        ell = float(row['kl_per_token'])
        mcse = float(row.get('kl_mc_se_per_token', 0.))
        total = float(row['kl_nats'])
        ratio = (random['mean']/max(ell, 1e-300) if random is not None else None)
        raw_win = bool(random is not None and row['total'] < row['n']
                       and ell <= random['mean']/3)
        conservative = False
        if random is not None:
            lower = max(0., random['mean']-2*random['combined_se'])
            conservative = bool(row['total'] < row['n'] and ell+2*mcse <= lower/3)
        records.append({**base, 'KL_per_token': ell, 'KL_total': total,
            'relative_KL': total/profile['L0_total'] if profile['L0_total'] > 0 else None,
            'proposal_mc_se': mcse, 'random': random,
            'random_over_proposal': ratio, 'win_factor3': raw_win,
            'win_conservative': conservative})
    return records


def failed_small_cells(comparison_rows, config, plan):
    initial_keys = {key for key, entry in plan.items()
                    if any(origin['stage'] == 'anchor' for origin in entry['origins'])}
    failed = []
    for target in TARGETS:
        for n in config['small_n']:
            local = [row for row in comparison_rows if row['target'] == target
                     and row['n'] == n and row['proposal_job_key'] in initial_keys]
            if not any(row['win_factor3'] for row in local):
                failed.append((target, n))
    return failed


def allocate_rescue_random(config, proposal_rows, plan, existing_random_rows):
    rescue_keys = {key for key, entry in plan.items()
                   if any(o['stage'].startswith('rescue_') for o in entry['origins'])}
    groups = defaultdict(list)
    for row in proposal_rows:
        key = controls.job_key(row['study_job'])
        if key in rescue_keys and row['status'] == 'complete' and row['target'] != 'matching':
            groups[(row['target'], row['n'], int(row['total']))].append(row)
    existing = {(row['target'], row['n'], int(row['study_job']['parameter']),
                 row['algorithm_repeat']) for row in existing_random_rows}
    algorithms = config['random_algorithm_repeats']
    ranked = sorted(groups, key=lambda group: (
        min(row['kl_per_token'] for row in groups[group]), group))
    jobs, omitted = [], []
    cap = config['rescue']['random_schedule_cap']
    new_count = 0
    for target, n, budget in ranked:
        local = [random_job(config, target, n, budget, algorithm)
                 for algorithm in algorithms
                 if (target, n, budget, algorithm) not in existing]
        if new_count+len(local) <= cap:
            jobs.extend(local)
            new_count += len(local)
        else:
            omitted.append({'target': target, 'n': n, 'budget': budget,
                            'reason': 'random_rescue_cap', 'requested': len(local)})
    return jobs, omitted


def write_plan(out, plan):
    atomic_json(out/'proposal_plan.json', {'jobs': plan})


def write_stage_selection(out, name, value):
    freeze_json(out/'manifests'/name, value)


def audit(out, config, proposal_rows, random_rows, profiles, plan):
    for row in proposal_rows:
        assert row['total'] <= row['n']
        assert row['master_field_seed'] == master_field_seed(DATA_REPEAT)
        assert abs(row['theta_reference']-coupling_cap(row['target'], row['n'])) < 1e-15
        if row['status'] == 'censored':
            assert row['kl_per_token'] is None and row['budget_stop'] is not None
        else:
            assert row['kl_per_token'] is not None and row['all_tokens_committed']
    for row in random_rows:
        assert row['status'] == 'complete'
        assert row['total'] == row['study_job']['parameter'] <= row['n']
    assert len({(p['target'], p['n']) for p in profiles}) == len(TARGETS)*len(config['n_grid'])
    result = {'proposal_runs': len(proposal_rows), 'random_runs': len(random_rows),
              'proposal_jobs_unique': len({controls.job_key(r['study_job'])
                                           for r in proposal_rows}),
              'random_jobs_unique': len({controls.job_key(r['study_job'])
                                         for r in random_rows}),
              'prefix_fields_verified': True, 'query_caps_verified': True,
              'censored_scores_are_null': True,
              'proposal_selection_inputs': 'proposal_runs_only',
              'random_not_used_in_facet_selection': True,
              'phase2_started': False, 'planned_proposal_jobs': len(plan)}
    freeze_json(out/'audit.json', result)
    return result


def minimum_common_n(comparison_rows):
    wins = {(row['target'], row['n']) for row in comparison_rows if row['win_factor3']}
    return next((n for n in sorted({row['n'] for row in comparison_rows})
                 if all((target, n) in wins for target in TARGETS)), None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=8)
    parser.add_argument('--output', type=Path, default=OUTPUT)
    parser.add_argument('--smoke', action='store_true')
    parser.add_argument('--prepare-only', action='store_true')
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
        sources = out/'sources'
        sources.mkdir(exist_ok=True)
        for name, checksum in config['source_sha256'].items():
            destination = sources/name
            if not destination.exists():
                shutil.copyfile(ROOT/name, destination)
            assert digest(destination) == checksum
        if args.prepare_only:
            atomic_json(out/'status.json', {'status': 'prepared', 'stage': 'prepared',
                'output': str(out), 'updated_utc': grid.utc()})
            return

        started = perf_counter()
        state = {'status': 'running', 'stage': 'profiles', 'pid': os.getpid(),
                 'workers': args.workers, 'output': str(out), 'started_utc': grid.utc()}
        atomic_json(out/'status.json', state)
        try:
            load_oracle_backend()
            load_forest_backend()
            profiles = ensure_profiles(out, config)
            plan = initial_plan(config)
            write_plan(out, plan)
            initial_rows = execute_jobs(out, config,
                [entry['job'] for entry in plan.values()], 'proposal',
                'initial_anchor', args.workers, state)
            initial_random_jobs = random_jobs_for_proposals(config, initial_rows)
            initial_random_rows = execute_jobs(out, config, initial_random_jobs,
                'random', 'initial_random', args.workers, state)
            initial_comparisons = comparisons(initial_rows, initial_random_rows, profiles)
            failed = failed_small_cells(initial_comparisons, config, plan)
            write_stage_selection(out, 'rescue_trigger.json', {
                'failed_cells': [list(cell) for cell in failed],
                'rule': config['rescue']['trigger'],
                'random_used_only_for_trigger': True})

            all_proposal_rows = list(initial_rows)
            if failed:
                stage_a = stage_a_plan(config, failed)
                merge_plans(plan, stage_a)
                write_plan(out, plan)
                a_rows = execute_jobs(out, config,
                    [entry['job'] for entry in stage_a.values()], 'proposal',
                    'rescue_A', args.workers, state)
                known = {controls.job_key(r['study_job']) for r in all_proposal_rows}
                all_proposal_rows.extend(r for r in a_rows
                                         if controls.job_key(r['study_job']) not in known)
                rankings_a = facet_ranking(all_proposal_rows, plan, 'rescue_A')
                stage_b, top_two = stage_b_plan(config, rankings_a)
                write_stage_selection(out, 'stage_A_selection.json', {
                    'ranking': {f'{t}|{n}': value for (t, n), value in rankings_a.items()},
                    'selected_top_two': top_two, 'inputs': 'proposal_only'})
                merge_plans(plan, stage_b)
                write_plan(out, plan)
                b_rows = execute_jobs(out, config,
                    [entry['job'] for entry in stage_b.values()], 'proposal',
                    'rescue_B', args.workers, state)
                known = {controls.job_key(r['study_job']) for r in all_proposal_rows}
                all_proposal_rows.extend(r for r in b_rows
                                         if controls.job_key(r['study_job']) not in known)
                selected_c, rankings_b = select_stage_c(all_proposal_rows, plan, failed)
                current_rescue = {key for key, entry in plan.items()
                                  if any(o['stage'].startswith('rescue_')
                                         for o in entry['origins'])}
                stage_c, proposal_omitted = stage_c_plan(
                    config, selected_c, current_rescue)
                write_stage_selection(out, 'stage_B_selection.json', {
                    'ranking': {f'{t}|{n}': value for (t, n), value in rankings_b.items()},
                    'selected_top_one': {f'{t}|{n}': value
                                         for (t, n), value in selected_c.items()},
                    'inputs': 'proposal_only'})
                write_stage_selection(out, 'stage_C_allocation.json', {
                    'selected_cells': {f'{t}|{n}': value
                                       for (t, n), value in selected_c.items()},
                    'new_or_reused_jobs': len(stage_c), 'omitted': proposal_omitted,
                    'cap': config['rescue']['proposal_job_cap']})
                merge_plans(plan, stage_c)
                write_plan(out, plan)
                c_rows = execute_jobs(out, config,
                    [entry['job'] for entry in stage_c.values()], 'proposal',
                    'rescue_C', args.workers, state)
                known = {controls.job_key(r['study_job']) for r in all_proposal_rows}
                all_proposal_rows.extend(r for r in c_rows
                                         if controls.job_key(r['study_job']) not in known)

            all_saved_proposals = read_runs(out/'proposal_runs.jsonl')
            all_saved_random = read_runs(out/'random_runs.jsonl')
            rescue_random_jobs, random_omitted = allocate_rescue_random(
                config, all_saved_proposals, plan, all_saved_random)
            write_stage_selection(out, 'rescue_random_allocation.json', {
                'jobs': rescue_random_jobs, 'omitted': random_omitted,
                'new_schedule_cap': config['rescue']['random_schedule_cap'],
                'proposal_grid_frozen_before_random': True})
            if rescue_random_jobs:
                execute_jobs(out, config, rescue_random_jobs, 'random',
                             'rescue_random', args.workers, state)
            proposal_rows = read_runs(out/'proposal_runs.jsonl')
            random_rows = read_runs(out/'random_runs.jsonl')
            comparison_rows = comparisons(proposal_rows, random_rows, profiles)
            atomic_json(out/'comparisons.json', comparison_rows)
            summary = {'minimum_common_N_factor3': minimum_common_n(comparison_rows),
                       'failed_anchor_cells': [list(cell) for cell in failed],
                       'complete_proposals': sum(r['status'] == 'complete'
                                                 for r in proposal_rows),
                       'censored_proposals': sum(r['status'] == 'censored'
                                                 for r in proposal_rows),
                       'factor3_wins': sum(r['win_factor3'] for r in comparison_rows),
                       'conservative_factor3_wins': sum(r['win_conservative']
                                                        for r in comparison_rows),
                       'phase2_started': False}
            atomic_json(out/'summary.json', summary)
            audit(out, config, proposal_rows, random_rows, profiles, plan)
            from report_sublinear_pilot import report
            report(out)
            for name, checksum in config['source_sha256'].items():
                assert digest(ROOT/name) == checksum
            state.update(status='complete', stage='phase1_complete_stop',
                         finished_utc=grid.utc(), seconds=perf_counter()-started,
                         summary=summary)
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
