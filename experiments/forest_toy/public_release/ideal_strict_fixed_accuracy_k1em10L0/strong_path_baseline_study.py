"""Strengthen the frozen strong-path controls, then confirm on fresh crossed seeds.

Please run with the existing toy virtual environment. This driver uses six
processes by default, saves a frozen design/source snapshot, and resumes only
matching jobs. It leaves the proposal implementation and target law unchanged.
"""
import argparse
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
from time import perf_counter
import traceback

import numpy as np

import explore_minimal as base
import row_cap_grid_study as grid
import strong_path_pivot_study as pivot
import strong_path_study as strong
from minimal_oracle import MinimalRecorder, load_backend
from ordering_baselines import ORDERINGS, sample
from validate import digest, freeze_json, read_runs
from weighted_oracle import weight_metadata


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT/'results'/'strong_path_baseline_study'
SOURCES = tuple(dict.fromkeys((*pivot.SOURCES, 'ordering_baselines.py',
    'strong_path_baseline_study.py', 'report_strong_path_baselines.py',
    'test_ordering_baselines.py')))
REFERENCES = {
    'margin': 'https://proceedings.mlr.press/v267/kim25ah.html',
    'eb': 'https://proceedings.neurips.cc/paper_files/paper/2025/hash/510e22f4a2da5212a64f1591736e2eaf-Abstract-Conference.html',
    'eb_algorithm': 'https://arxiv.org/html/2505.24857v1#S4',
}


def design(smoke=False):
    return {'version': 1, 'smoke': smoke, 'n': 512 if smoke else strong.N,
        'target': 'path', 'target_law': strong.CASE, 'theta': .25,
        'fields': 'iid Uniform[-1,1]', 'oracle': 'exact', 'vocab': 2048,
        'proposal_settings': [(6, 9, 18, .03)] if smoke else
            [(8, 45, 18, .03), (8, 53, 18, .03), (8, 61, 18, .03), (8, 53, 18, .001)],
        'proposal_pivot': (6, 9, 18, .03) if smoke else (8, 53, 18, .03),
        'proposal_variant': 'topd', 'draft': 'first_bank', 'J': 1,
        'proposal_selection': 'Four settings already explored in the previous study; no new proposal tuning.',
        'explore_pairs': [(110, 210)] if smoke else [(110, 210), (111, 211)],
        'confirm_pairs': [(130, 230), (130, 231)] if smoke else
            [(data, algorithm) for data in range(130, 135) for algorithm in (230, 231)],
        'fixed_budgets': [4, 64] if smoke else [1, 256, 1024, 2048, 4096, 6144, 8192, 12288],
        'matched_budget': 'Also include rounded exploratory mean Q of the frozen proposal pivot if all its runs complete.',
        'fixed_orderings': ['random', *ORDERINGS], 'eb_orderings': list(ORDERINGS),
        'eb_gammas': [1.5, 4.] if smoke else [1., 1.25, 1.5, 1.75, 2., 2.5, 3., 4., 8., 16., 64.],
        'eb_rule': 'Largest score-ordered prefix U with sum_i H(p_i)-max_i H(p_i) <= gamma; full-vocabulary entropy in nats.',
        'sampling': 'Temperature one; choose positions before value sampling; one current-history reply per commit; no remasking.',
        'seed_roles': {'data': 'Random path relabeling and unary fields, shared across all methods and parameters.',
            'algorithm': 'Proposal colorings and values; baseline tie priorities and values. Fixed-count streams retain the old budget-dependent seed derivation; EB streams depend on gamma. Ordering names never enter the seed.',
            'pairing': 'Common initial RNG streams do not imply tokenwise common random draws after different batch choices.'},
        'selection_rule': {
            'cost_control': 'Per method, keep the minimum mean KL with mean Q <= N/4, or its cheapest setting if none qualifies.',
            'accuracy_controls': 'Per method and KL/token level 1e-4, 1e-6, 1e-8, keep minimum mean Q attaining the level; if unattained keep its minimum-KL setting.',
            'ties': 'KL floored at 1e-12 for selection only; then Q, then numeric parameter. At most four settings per method.',
            'freeze': 'Use only the two exploration pairs; freeze every method separately before any confirmation result. No best-ordering selection on confirmation seeds.'},
        'metrics': {'main': 'Mean actual total queries Q versus mean conditional reverse KL/token.',
            'secondary': 'Median/p90 Q, sequential depth T, per-target means and individual runs.',
            'KL': 'Exact within each batch on its realized history; expectation over histories estimated across runs. Not the forward-KL bound in the EB paper.',
            'seeds': 'Exploration: two data/algorithm pairs. Confirmation: five new targets crossed with two new algorithm repeats, not ten iid target draws.',
            'censoring': 'Q<=N for proposals; censored runs kept separately with KL=None. Baselines finish within N queries.',
            'plot': 'Average identical x coordinates arithmetically within each method before drawing lines; preserve unmerged setting tables.',
            'claim': 'Sampling-rule comparison on an exact forest oracle, not a reproduction of the original MDM task scores or temperature-zero experiments.'},
        'references': REFERENCES,
        'source_sha256': {name: digest(ROOT/name) for name in SOURCES}}


def array_hash(array, dtype):
    return hashlib.sha256(np.asarray(array, dtype=dtype).tobytes()).hexdigest()


def method_name(job):
    if job['kind'] == 'proposal':
        return 'proposal'
    return job['family']+'_'+job['ordering']


def job_key(job):
    return json.dumps(job, sort_keys=True, separators=(',', ':'))


def job_name(job):
    stem = f'{method_name(job)}_N{job["n"]}_data{job["data"]}_alg{job["algorithm"]}'
    if job['kind'] == 'proposal':
        p, m, d, tau = job['setting']
        return stem+f'_p{p}_M{m}_d{d}_tau{tau:g}'
    return stem+f'_{"B" if job["family"] == "fixed" else "gamma"}{job["parameter"]:g}'


def eb_seeds(n, algorithm, gamma):
    # Please keep data and ordering names out of these two controller streams.
    payload = f'strong-path-eb-v1|{n}|{algorithm}|{float(gamma):.17g}'.encode()
    raw = hashlib.sha256(payload).digest()
    return [int.from_bytes(raw[i:i+8], 'little') for i in (0, 8)]


def run_job(job, output):
    output = Path(output)
    repeat = pivot.repeat_id(job['data'], job['algorithm'])
    if job['kind'] == 'proposal':
        legacy = base.proposal_job('path', job['n'], repeat, tuple(job['setting']))
        row = pivot.run_proposal(legacy, output, 'topd')
        row.update(study_job=job, method='proposal', source_job=row['job'])
        return row
    np.seterr(divide='raise', over='raise', invalid='raise')
    started = perf_counter()
    adaptive = job['family'] == 'eb'
    budget = 0 if adaptive else int(job['parameter'])
    oracle, seeds = pivot.make_target('path', job['n'], repeat, kind='baseline', budget=budget)
    if adaptive:
        seeds = [seeds[0], *eb_seeds(job['n'], job['algorithm'], job['parameter'])]
    metadata = weight_metadata(oracle)
    metadata.pop('true_signal_lower_bound')
    metadata.pop('true_response_upper_bound')
    recorder = MinimalRecorder(oracle.n)
    setup_seconds = perf_counter()-started
    sample_start = perf_counter()
    _, control = sample(oracle, seeds[1], seeds[2], job['ordering'], recorder,
        gamma=float(job['parameter']) if adaptive else None,
        batches=budget if not adaptive else None)
    sample_seconds = perf_counter()-sample_start
    sizes = control['batch_sizes']
    assert oracle.cost.total == oracle.cost.rounds == len(sizes) <= oracle.n
    if not adaptive:
        assert len(sizes) == budget
    expected_rows = oracle.n if job['ordering'] == 'random' else int(
        sum(oracle.n-int(x) for x in np.r_[0, np.cumsum(sizes)[:-1]]))
    assert oracle.cost.returned_rows == expected_rows
    name = job_name(job)
    trace = output/'traces'/(name+'.npz')
    score = recorder.finish(oracle, trace)
    controller_trace = None
    if adaptive:
        controller_trace = output/'traces'/(name+'_controller.npz')
        np.savez_compressed(controller_trace, **control)
    row = {'study_job': job, 'kind': 'baseline', 'method': method_name(job),
        'target': 'path', 'n': oracle.n, 'repeat': repeat, 'seeds': seeds,
        'status': 'complete', 'baseline': job['ordering'], 'family': job['family'],
        'parameter': job['parameter'], 'budget': budget if not adaptive else None,
        'gamma': float(job['parameter']) if adaptive else None,
        'field_seed': oracle.field_seed, 'fields_sha256': array_hash(oracle.fields, '<f8'),
        'target_log_z': oracle.log_z, 'oracle_exact': True, 'all_edge_certificate_claimed': False,
        'sample_seconds': sample_seconds, 'setup_seconds': setup_seconds,
        'seconds': perf_counter()-started, 'trace': str(trace.relative_to(output)),
        'controller_trace': str(controller_trace.relative_to(output)) if adaptive else None,
        'batch_size_histogram': dict(Counter(map(int, sizes))),
        'batch_size_mean': float(sizes.mean()), 'batch_size_max': int(sizes.max()),
        'entropy_budget_max_used': float(control['entropy_bounds'].max()) if adaptive else None,
        'depth': len(sizes), **metadata, **score, **asdict(oracle.cost), 'total': oracle.cost.total}
    return pivot.tag(row)


def proposal_jobs(config, pairs):
    return [{'kind': 'proposal', 'n': config['n'], 'data': d, 'algorithm': a,
             'setting': list(s)} for s in config['proposal_settings'] for d, a in pairs]


def baseline_jobs(config, pairs, settings):
    return [{'kind': 'baseline', 'n': config['n'], 'data': d, 'algorithm': a,
             'family': s['family'], 'ordering': s['ordering'], 'parameter': s['parameter']}
            for s in settings for d, a in pairs]


def initial_settings(config, proposals):
    budgets = set(config['fixed_budgets'])
    pivot_rows = [r for r in proposals if r['study_job']['setting'] == list(config['proposal_pivot'])]
    if pivot_rows and all(r['status'] == 'complete' for r in pivot_rows):
        budgets.add(int(np.floor(np.mean([r['total'] for r in pivot_rows])+.5)))
    return ([{'family': 'fixed', 'ordering': policy, 'parameter': b}
             for policy in config['fixed_orderings'] for b in sorted(budgets)]
            + [{'family': 'eb', 'ordering': policy, 'parameter': gamma}
               for policy in config['eb_orderings'] for gamma in config['eb_gammas']])


def setting_key(row):
    job = row['study_job']
    if job['kind'] == 'proposal':
        return ('proposal', *job['setting'])
    return (method_name(job), job['parameter'])


def aggregate(rows):
    groups = defaultdict(list)
    for row in rows:
        groups[setting_key(row)].append(row)
    result = []
    for key, group in sorted(groups.items()):
        complete = [r for r in group if r['status'] == 'complete']
        item = {'key': list(key), 'method': key[0], 'runs': len(group),
            'complete': len(complete), 'censored': len(group)-len(complete),
            'Q': float(np.mean([r['total'] for r in group])),
            'Q_median': float(np.median([r['total'] for r in group])),
            'Q_p90': float(np.quantile([r['total'] for r in group], .9)),
            'Q_min': min(r['total'] for r in group), 'Q_max': max(r['total'] for r in group),
            'T': float(np.mean([r['depth'] for r in group])),
            'KL': float(np.mean([r['kl_per_token'] for r in complete])) if len(complete) == len(group) else None,
            'KL_max': max((r['kl_per_token'] for r in complete), default=None),
            'below_floor': sum(r['kl_per_token'] <= 1e-12 for r in complete),
            'sample_seconds': float(np.mean([r['sample_seconds'] for r in group])),
            'evaluation_seconds': float(np.mean([r['evaluation_seconds'] for r in group])),
            'pairs': sorted([r['data_repeat'], r['algorithm_repeat']] for r in group)}
        result.append(item)
    return result


def select(config, rows):
    groups = aggregate(rows)
    selected = {}
    for method in sorted({r['method'] for r in groups}):
        local = [r for r in groups if r['method'] == method]
        quality = lambda r: (max(1e-12, r['KL']), r['Q'], r['key'][1])
        cost = lambda r: (r['Q'], max(1e-12, r['KL']), r['key'][1])
        bounded = [r for r in local if r['Q'] <= config['n']/4]
        controls = [(min(bounded, key=quality) if bounded else min(local, key=cost), 'Q<=N/4 control')]
        for epsilon in (1e-4, 1e-6, 1e-8):
            eligible = [r for r in local if r['KL'] <= epsilon]
            controls.append((min(eligible, key=cost) if eligible else min(local, key=quality),
                             f'min Q at KL<={epsilon:g}' if eligible else f'unattained KL<={epsilon:g}; best KL'))
        for row, reason in controls:
            key = tuple(row['key'])
            if key not in selected:
                family, ordering = method.split('_', 1)
                selected[key] = {'family': family, 'ordering': ordering,
                    'parameter': key[1], 'reasons': [], 'explore_Q': row['Q'], 'explore_KL': row['KL']}
            selected[key]['reasons'].append(reason)
    return {'rule': config['selection_rule'], 'settings': [selected[k] for k in sorted(selected)]}


def execute(out, config, phase, kind, jobs, workers, state):
    local = out/phase/kind
    local.mkdir(parents=True, exist_ok=True)
    freeze_json(local/'jobs.json', jobs)
    if kind == 'proposals':
        legacy = [base.proposal_job('path', j['n'], pivot.repeat_id(j['data'], j['algorithm']), tuple(j['setting'])) for j in jobs]
        pivot.ensure_profiles(legacy, local)
    path = local/'runs.jsonl'
    rows = read_runs(path)
    wanted, done = {job_key(j) for j in jobs}, {job_key(r['study_job']) for r in rows}
    assert len(done) == len(rows) and done <= wanted and len(wanted) == len(jobs)
    state.update(stage=phase+'_'+kind, stage_jobs=len(jobs), stage_finished=len(rows), updated_utc=grid.utc())
    grid.atomic_json(out/'status.json', state)
    with ProcessPoolExecutor(max_workers=workers) as pool, path.open('a') as stream:
        futures = {pool.submit(run_job, job, local): job for job in jobs if job_key(job) not in done}
        for future in as_completed(futures):
            row = future.result()
            rows.append(row)
            stream.write(json.dumps(row, allow_nan=False, separators=(',', ':'))+'\n')
            stream.flush()
            state.update(stage_finished=len(rows), updated_utc=grid.utc())
            grid.atomic_json(out/'status.json', state)
            if len(rows) % 10 == 0 or len(rows) == len(jobs):
                print(f'{phase}/{kind} {len(rows)}/{len(jobs)} '
                      f'{row["method"]} Q={row["total"]} KL/N={row["kl_per_token"]}', flush=True)
    return rows


def audit(out, config, records):
    targets, streams, counts = {}, {}, {}
    for phase, by_kind in records.items():
        expected_pairs = {tuple(p) for p in config[phase+'_pairs']}
        for kind, rows in by_kind.items():
            per_setting = defaultdict(set)
            checked = censored = 0
            for row in rows:
                job = row['study_job']
                pair = row['data_repeat'], row['algorithm_repeat']
                assert pair == (job['data'], job['algorithm'])
                per_setting[setting_key(row)].add(pair)
                target_key = row['n'], row['data_repeat']
                hashes = tuple(row[k] for k in ('edges_sha256', 'weights_sha256', 'fields_sha256'))
                assert targets.setdefault(target_key, hashes) == hashes
                stream_key = (job['n'], job['algorithm'], job['kind'],
                              job.get('family'), job.get('parameter'))
                assert streams.setdefault(stream_key, row['seeds'][1:]) == row['seeds'][1:]
                assert row['total'] == row['preprocessing']+row['counterfactual']+row['rounds'] <= row['n']
                if row['status'] != 'complete':
                    assert row['kl_per_token'] is row['trace'] is None
                    assert row['budget_stop']['spent'] == row['total']
                    assert row['total']+row['budget_stop']['next_submission_queries'] > row['n']
                    censored += 1
                    continue
                with np.load(out/phase/kind/row['trace']) as trace:
                    steps, values, costs = (trace[k] for k in ('commit_step', 'values', 'batch_kl'))
                    assert steps.shape == values.shape == (row['n'],)
                    assert set(steps) == set(range(row['rounds']))
                    assert (values >= 0).all() and (values < config['vocab']).all()
                    sizes = np.bincount(steps)
                    assert len(costs) == row['rounds'] and np.isfinite(costs).all() and (costs >= 0).all()
                    assert abs(float(costs.sum())/row['n']-row['kl_per_token']) < 1e-14
                    assert (costs[sizes == 1] == 0).all()
                if job['kind'] == 'baseline':
                    assert row['preprocessing'] == row['counterfactual'] == 0
                    assert row['total'] == row['depth'] == row['rounds']
                    if job['family'] == 'fixed':
                        small, extra = divmod(row['n'], int(job['parameter']))
                        np.testing.assert_array_equal(sizes, [small+(i < extra) for i in range(row['budget'])])
                    else:
                        with np.load(out/phase/kind/row['controller_trace']) as trace:
                            np.testing.assert_array_equal(sizes, trace['batch_sizes'])
                            bounds, following = trace['entropy_bounds'], trace['next_entropy_bounds']
                            assert len(bounds) == len(following) == row['rounds']
                            assert np.isfinite(bounds).all() and (bounds >= 0).all()
                            assert (bounds <= row['gamma']).all()
                            assert (following[np.isfinite(following)] > row['gamma']).all()
                            assert np.isnan(following[-1]) and not np.isnan(following[:-1]).any()
                else:
                    assert row['depth'] == 1+row['screen_calls']+row['rounds']
                checked += 1
            assert all(pairs == expected_pairs for pairs in per_setting.values())
            counts[phase+'/'+kind] = {'completed': checked, 'censored': censored}
    result = {'target_pairing_valid': True, 'algorithm_streams_independent_of_target': True,
              'cost_and_trace_checks_passed': True, 'distinct_targets': len(targets), 'counts': counts}
    freeze_json(out/'audit.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=6)
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
            dest = sources/name
            if not dest.exists():
                shutil.copyfile(ROOT/name, dest)
            assert digest(dest) == checksum
        if args.prepare_only:
            grid.atomic_json(out/'status.json', {'status': 'prepared', 'stage': 'prepared', 'output': str(out), 'updated_utc': grid.utc()})
            return
        started = perf_counter()
        state = {'status': 'running', 'stage': 'preparing', 'pid': os.getpid(),
                 'workers': args.workers, 'started_utc': grid.utc(), 'output': str(out)}
        grid.atomic_json(out/'status.json', state)
        try:
            load_backend()
            records = {'explore': {}, 'confirm': {}}
            records['explore']['proposals'] = execute(out, config, 'explore', 'proposals',
                proposal_jobs(config, config['explore_pairs']), args.workers, state)
            settings = initial_settings(config, records['explore']['proposals'])
            freeze_json(out/'explore_settings.json', settings)
            records['explore']['baselines'] = execute(out, config, 'explore', 'baselines',
                baseline_jobs(config, config['explore_pairs'], settings), args.workers, state)
            selection = select(config, records['explore']['baselines'])
            freeze_json(out/'selection.json', selection)
            from report_strong_path_baselines import report
            report(out, phases=('explore',))
            records['confirm']['proposals'] = execute(out, config, 'confirm', 'proposals',
                proposal_jobs(config, config['confirm_pairs']), args.workers, state)
            records['confirm']['baselines'] = execute(out, config, 'confirm', 'baselines',
                baseline_jobs(config, config['confirm_pairs'], selection['settings']), args.workers, state)
            state.update(stage='audit_and_report', updated_utc=grid.utc())
            grid.atomic_json(out/'status.json', state)
            audit(out, config, records)
            report(out)
            for name, checksum in config['source_sha256'].items():
                assert digest(ROOT/name) == checksum, 'Please avoid changing the running source snapshot.'
            state.update(status='complete', stage='complete', finished_utc=grid.utc(),
                seconds=perf_counter()-started,
                proposal_runs=sum(len(r['proposals']) for r in records.values()),
                baseline_runs=sum(len(r['baselines']) for r in records.values()))
            grid.atomic_json(out/'status.json', state)
            print(json.dumps(state, indent=2), flush=True)
        except BaseException as error:
            state.update(status='failed', error=repr(error), traceback=traceback.format_exc(), updated_utc=grid.utc())
            grid.atomic_json(out/'status.json', state)
            raise


if __name__ == '__main__':
    main()
