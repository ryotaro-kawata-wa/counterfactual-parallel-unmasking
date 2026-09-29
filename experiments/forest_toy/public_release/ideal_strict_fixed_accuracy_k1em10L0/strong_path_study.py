"""Run the agreed strong-path control after an optional preceding background job.

Please keep the original study sources unchanged. Worker-local adapters replace
only the target factory and profile naming; both samplers retain their query meter.
"""
import argparse
from collections import Counter
from contextlib import contextmanager
from dataclasses import asdict
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import time
from time import perf_counter
import traceback

import numpy as np

import explore_minimal as base
import minimal_study
import row_cap_grid_study as grid
from cycle_repair import remove_vertices
from draft_policy import draft_policy, save_capture
from minimal_oracle import MinimalOracle, MinimalRecorder, field_seed, load_backend
from profile_minimal import initial_edges, weighted_summary
from row_cap_variants import row_cap_policy, save_votes
from toy import centroid_batch
from validate import digest, freeze_json, read_runs
from weighted_oracle import make_weighted_target, weight_metadata


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT/'results'/'strong_path_study'
CASE = 'theta025_bias_uniform1'
THRESHOLD = .001
N = 16384
BASE_RUN = base.run_job
ANCHORS = ((4, 25, 36, THRESHOLD), (4, 65, 36, THRESHOLD),
           (6, 49, 18, THRESHOLD), (6, 49, 36, THRESHOLD))
SOURCES = tuple(dict.fromkeys((*grid.SOURCES, 'strong_path_study.py',
                             'report_strong_path.py', 'test_strong_path.py')))
SELECTION = {
    'frontiers': 'For EACH row policy, retain minimum exploratory KL at Q<=1000,2500,5000,N, plus the cheapest complete run.',
    'resolution': 'For EACH row policy, retain minimum Q at KL/token<=1e-4,1e-6,1e-8,1e-12 when attained.',
    'controls': 'Retain four frozen previous p/M/d anchors, using the new fixed TV threshold; retain largest and smallest paired KL ratios.',
    'ties': 'KL floored at 1e-12 for selection only; tie by Q then setting. Raw scores retained.',
    'confirmation': 'Use exploration seed 0 only; freeze candidates before seeds 10/11 and baseline outcomes. Both row policies evaluated for every candidate.',
}


def make_target(target, n, repeat, biased=True, weak_tail=False, sigma=None,
                kind='proposal', budget=0):
    if target != 'path':
        raise ValueError('Please keep this control restricted to paths.')
    prototype, seeds = make_weighted_target(target, n, repeat, 'original_uniform', kind, budget)
    seed = field_seed(target, n, repeat)
    fields = np.random.default_rng(seed).uniform(-1., 1., n)
    oracle = MinimalOracle(n, prototype.edges, np.full(len(prototype.edges), .25), .25,
                           fields, vocab=prototype.vocab)
    oracle.weight_seed = None
    oracle.field_seed = seed
    oracle.tail_shape = None
    oracle.target_law = CASE
    return oracle, seeds


def tag(row):
    """Please replace legacy law labels along with the target factory."""
    row.update(case=CASE, target_law=CASE, biased=True, weak_tail=False, sigma=None,
               field_distribution='Uniform[-1,1]', theta_distribution='constant 0.25',
               tail_shape_b=None)
    return row


@contextmanager
def target_context():
    original_factory, original_case = base.make_target, minimal_study.case_name
    base.make_target = make_target
    minimal_study.case_name = lambda *_: CASE
    try:
        yield
    finally:
        base.make_target, minimal_study.case_name = original_factory, original_case


def ensure_profiles(jobs, output):
    profiles = []
    for target, n, repeat in sorted({(j[1], j[2], j[3]) for j in jobs}):
        oracle, seeds = make_target(target, n, repeat)
        rows, weights, total = initial_edges(oracle)
        path = output/'target_profiles'/f'{target}_{CASE}_seed{repeat}.npz'
        path.parent.mkdir(parents=True, exist_ok=True)
        arrays = dict(edges=oracle.edges, theta=oracle.edge_strengths, fields=oracle.fields,
                      initial_rows=rows, initial_edge_kl=weights)
        if path.exists():
            with np.load(path) as saved:
                for key, values in arrays.items():
                    np.testing.assert_array_equal(saved[key], values)
        else:
            np.savez_compressed(path, **arrays)
        profiles.append({'target': target, 'target_law': CASE, 'n': n, 'repeat': repeat,
            'seeds': seeds, 'field_distribution': 'Uniform[-1,1]', 'theta': .25,
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
    """Please install explicit picklable worker entry points for the reused driver."""
    saved = base.ensure_profiles, grid.run_proposal, base.run_job
    base.ensure_profiles, grid.run_proposal, base.run_job = ensure_profiles, run_proposal, run_baseline
    try:
        yield
    finally:
        base.ensure_profiles, grid.run_proposal, base.run_job = saved


def known_graph_sample(oracle, commit_seed, recorder):
    """This diagnostic alone may inspect true adjacency before generation."""
    graph = {u: set(neighbors) for u, neighbors in enumerate(oracle.adjacency)}
    history = np.full(oracle.n, -1, dtype=np.int64)
    rng = np.random.default_rng(commit_seed)
    while graph:
        batch = np.asarray(sorted(centroid_batch(graph)), dtype=np.int64)
        rows = oracle.submit(history, batch, 'commit')
        values = (rng.random(len(batch))[:, None] > rows[:, :2].cumsum(axis=1)).sum(axis=1)
        tail = values == 2
        values[tail] = rng.integers(2, oracle.vocab, size=int(tail.sum()))
        recorder(batch, rows, values)
        history[batch] = values
        remove_vertices(graph, batch)
    return history


def known_graph_runs(output, n, seeds):
    local = output/'known_graph'
    local.mkdir(exist_ok=True)
    path = local/'runs.jsonl'
    rows = read_runs(path)
    done = {r['repeat'] for r in rows}
    assert len(done) == len(rows) and done <= set(seeds)
    with path.open('a') as stream:
        for repeat in seeds:
            if repeat in done:
                continue
            started = perf_counter()
            oracle, rng_seeds = make_target('path', n, repeat)
            recorder = MinimalRecorder(n)
            sample_start = perf_counter()
            known_graph_sample(oracle, rng_seeds[2], recorder)
            sample_seconds = perf_counter()-sample_start
            trace = local/'traces'/f'known_path_N{n}_seed{repeat}.npz'
            score = recorder.finish(oracle, trace)
            assert score['all_tokens_committed'] and score['unsafe_batches'] == 0
            assert oracle.cost.counterfactual == oracle.cost.preprocessing == 0
            assert oracle.cost.total == n.bit_length()
            assert score['kl_per_token'] < 1e-12
            weights = weight_metadata(oracle)
            weights.pop('true_signal_lower_bound')
            weights.pop('true_response_upper_bound')
            row = tag({'kind': 'known_graph', 'target': 'path', 'n': n, 'repeat': repeat,
                'status': 'complete', 'seeds': rng_seeds, 'information': 'True adjacency given for free to this diagnostic only.',
                'fields_sha256': hashlib.sha256(oracle.fields.astype('<f8').tobytes()).hexdigest(),
                'sample_seconds': sample_seconds, 'seconds': perf_counter()-started,
                'trace': str(trace.relative_to(local)), 'depth': oracle.cost.rounds,
                'batch_size_histogram': dict(Counter(map(len, recorder.batches))),
                **weights, **score, **asdict(oracle.cost), 'total': oracle.cost.total})
            stream.write(json.dumps(row, separators=(',', ':'), allow_nan=False)+'\n')
            stream.flush()
            rows.append(row)
            print(f'known graph seed{repeat} Q={row["total"]} KL={row["kl_per_token"]}', flush=True)
    return rows


def settings(smoke=False):
    if smoke:
        return [('path', 3, 9, 9, THRESHOLD), ('path', 6, 9, 18, THRESHOLD)]
    choices = {('path', p, m, d, THRESHOLD)
               for p in (4, 6, 8, 10, 12)
               for m in {max(9, 2*int(b/(2*p*(2*p-1)))+1) for b in (800, 1600, 3200, 6400)}
               for d in (9, 18, 36)}
    choices.update(('path', *a) for a in ANCHORS)
    return sorted(choices)


def design(smoke=False):
    return {'version': 1, 'n': 1024 if smoke else N, 'smoke': smoke, 'settings': settings(smoke),
        'explore_seeds': [0], 'confirm_seeds': [10, 11], 'selection': SELECTION,
        'target_law': CASE, 'theta': .25, 'fields': 'iid Uniform[-1,1]',
        'vocab': 2048, 'unary': 'proportional to (.4 exp(h), .4 exp(-h), .2); tail mass is uniform over 2046 tokens',
        'draft': 'first_bank', 'J': 1, 'TV_threshold': THRESHOLD, 'variants': grid.POLICIES,
        'topology': 'One path with the existing random relabeling. True adjacency is withheld from all methods except the separately labeled known-graph diagnostic.',
        'budget': 'Only per-run Q<=N. Censored settings separate; Q=3000 is not a cutoff.',
        'known_graph': 'Exact centroid sampling, one current-history oracle query per batch, no preprocessing. Free true adjacency is an information advantage, not a competing discovery method.',
        'baseline_scope': 'Confirmation candidates at rounded mean total Q and separately mean T. Same target seeds, balanced random/confidence, temperature-1 sampling.',
        'source_sha256': {name: digest(ROOT/name) for name in SOURCES}}


def select(records, config):
    chosen = {}
    def add(row, why):
        chosen.setdefault(base.setting_key(row), []).append(why)
    cost = lambda r: (r['total'], max(1e-12, r['kl_per_token']), base.setting_key(r))
    error = lambda r: (max(1e-12, r['kl_per_token']), r['total'], base.setting_key(r))
    for variant, rows in records.items():
        complete = [r for r in rows if r['status'] == 'complete']
        for limit in sorted({min(config['n'], b) for b in (1000, 2500, 5000, config['n'])}):
            eligible = [r for r in complete if r['total'] <= limit]
            if eligible:
                add(min(eligible, key=error), f'{variant}_min_KL_Q_le_{limit}')
        for epsilon in (1e-4, 1e-6, 1e-8, 1e-12):
            eligible = [r for r in complete if r['kl_per_token'] <= epsilon]
            if eligible:
                add(min(eligible, key=cost), f'{variant}_min_Q_KL_le_{epsilon}')
        if complete:
            add(min(complete, key=cost), f'{variant}_cheapest_complete')
    lookup = {base.setting_key(r): r for r in records['reference']}
    pairs = [(lookup[base.setting_key(r)], r) for r in records['topd']
             if r['status'] == 'complete' and lookup[base.setting_key(r)]['status'] == 'complete']
    ratio = lambda pair: (max(1e-12, pair[0]['kl_per_token'])/max(1e-12, pair[1]['kl_per_token']), base.setting_key(pair[0]))
    if pairs:
        add(min(pairs, key=ratio)[0], 'smallest_paired_KL_ratio')
        add(max(pairs, key=ratio)[0], 'largest_paired_KL_ratio')
    for row in records['reference']:
        if config['smoke'] or tuple(base.setting_key(row)[1:]) in ANCHORS:
            add(row, 'fixed_control')
    return {'rule': SELECTION, 'settings': sorted(chosen),
            'reasons': [{'setting': key, 'reasons': reasons} for key, reasons in sorted(chosen.items())]}


def wait_for_predecessor(path, out, state):
    if path is None:
        return
    while True:
        previous = json.loads(path.read_text())
        if previous['status'] in ('complete', 'failed'):
            state.update(predecessor_final_status=previous['status'])
            print(f'predecessor reached {previous["status"]}; starting independent strong-path control', flush=True)
            return
        state.update(status='waiting', stage='waiting_for_previous_job', predecessor=str(path),
                     predecessor_stage=previous.get('stage'), predecessor_finished=previous.get('stage_finished'),
                     updated_utc=grid.utc())
        grid.atomic_json(out/'status.json', state)
        time.sleep(10)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=6)
    parser.add_argument('--output', type=Path, default=OUTPUT)
    parser.add_argument('--after-status', type=Path)
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
        state = {'status': 'starting', 'stage': 'preparing', 'pid': os.getpid(),
                 'workers': args.workers, 'queued_utc': grid.utc(), 'output': str(out)}
        grid.atomic_json(out/'status.json', state)
        try:
            wait_for_predecessor(args.after_status, out, state)
            assert {name: digest(ROOT/name) for name in SOURCES} == config['source_sha256']
            state.update(status='running', started_utc=grid.utc())
            started = perf_counter()
            load_backend()
            known = known_graph_runs(out, config['n'], [*config['explore_seeds'], *config['confirm_seeds']])
            with runner_context():
                exploratory = grid.execute_proposals(out, config, config['settings'], config['explore_seeds'], 'explore', args.workers, state)
                selection = select(exploratory, config)
                freeze_json(out/'selection.json', selection)
                confirmed = grid.execute_proposals(out, config, selection['settings'], config['confirm_seeds'], 'confirm', args.workers, state)
                baselines = grid.baselines(out, config, confirmed, args.workers, state)
            state.update(stage='reporting', updated_utc=grid.utc())
            grid.atomic_json(out/'status.json', state)
            from report_strong_path import report
            report(out)
            assert {name: digest(ROOT/name) for name in SOURCES} == config['source_sha256']
            state.update(status='complete', stage='complete', finished_utc=grid.utc(), seconds=perf_counter()-started,
                         proposal_runs=sum(map(len, exploratory.values()))+sum(map(len, confirmed.values())),
                         baseline_runs=len(baselines), known_graph_runs=len(known))
            freeze_json(out/'execution.json', state)
        except BaseException:
            state.update(status='failed', failed_utc=grid.utc(), traceback=traceback.format_exc())
            raise
        finally:
            grid.atomic_json(out/'status.json', state)
        print(json.dumps(state), flush=True)


if __name__ == '__main__':
    main()
