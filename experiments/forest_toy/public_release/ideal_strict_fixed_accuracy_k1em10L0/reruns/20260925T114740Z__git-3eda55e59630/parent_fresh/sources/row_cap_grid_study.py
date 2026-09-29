"""Run a paired overflow-policy grid, then confirm frozen candidate settings.

Please run this driver in its own process. The original sampler and the previous
result directories remain unchanged; only overflow decoding differs within pairs.
"""
import argparse
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone
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
from draft_policy import draft_policy, save_capture
from minimal_oracle import load_backend
from row_cap_study import SETTINGS as ANCHORS
from row_cap_variants import row_cap_policy, save_votes
from validate import digest, freeze_json, read_runs


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT/'results'/'row_cap_grid_study'
POLICIES = {'reference': 'discard', 'topd': 'top_votes'}
GRID = {
    'matching': {'p': (3, 4, 6), 'screen_budgets': (500, 1000, 1750, 2750, 4250),
                 'd': (9, 18), 'tau': (.0001, .0003, .001, .003)},
    'path': {'p': (4, 6, 8, 10), 'screen_budgets': (700, 1400, 2400, 3800, 5500),
             'd': (9, 18, 36), 'tau': (.0003, .001, .003, .01)},
}
SELECTION = {
    'frontiers': 'For each target AND each policy, retain the minimum exploratory KL at Q<=1000,2500,5000,N. Also retain the cheapest complete run.',
    'paired_extremes': 'For each target, retain both the largest and smallest reference/top-d KL ratio among pairs that both completed. This includes adverse results.',
    'anchors': 'Always retain all seven settings from the previous row-cap study.',
    'ties': 'Compare KL floored at 1e-12, then Q, then the setting tuple. Ratios also use this floor; raw KL is never overwritten.',
    'confirmation': 'Freeze the union using seed 0 only, before new seeds 10/11 or baseline results. Evaluate BOTH policies at every selected setting.',
    'budget': '3000 is not a cutoff. Only the inherited per-run Q<=N cap applies; unfinished runs are reported separately without KL.',
}
SOURCES = tuple(dict.fromkeys((*base.SOURCES, 'draft_policy.py', 'row_cap_variants.py',
                             'row_cap_study.py', 'row_cap_grid_study.py',
                             'report_row_cap_grid.py')))


def utc():
    return datetime.now(timezone.utc).isoformat()


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')
    temporary.replace(path)


def settings(smoke=False):
    if smoke:
        return [('matching', 3, 9, 9, .003), ('path', 3, 9, 9, .003)]
    result = set()
    for target, grid in GRID.items():
        for p in grid['p']:
            # Please vary M with p so the grid spans comparable first-screen costs.
            ms = {max(9, 2*int(b/(2*p*(2*p-1)))+1) for b in grid['screen_budgets']}
            ms.update(s[1] for _, t, s, _ in ANCHORS if t == target and s[0] == p)
            for m in ms:
                for d in grid['d']:
                    for tau in grid['tau']:
                        result.add((target, p, m, d, tau))
    result.update((target, *s) for _, target, s, _ in ANCHORS)
    return sorted(result)


def design(smoke=False):
    grid = settings(smoke)
    return {'version': 1, 'n': 256 if smoke else 16384, 'smoke': smoke,
            'explore_seeds': [0], 'confirm_seeds': [10, 11], 'settings': grid,
            'grid_specification': GRID, 'variants': POLICIES, 'draft': 'first_bank',
            'J': 1, 'selection': SELECTION, 'main_query_limit': None,
            'per_run_query_limit': 256 if smoke else 16384,
            'nominal_screen_cost': 'p(2p-1)M is a grid-design estimate, not the actual total Q or a stopping rule.',
            'baseline_scope': 'Selected confirmation settings only: balanced random/confidence at rounded mean total Q, separately mean depth T.',
            'metric': 'Mean conditional reverse batch KL/token along generated histories; exact per-history evaluation. Raw individual values retained.',
            'seed_role': 'One exploratory seed; two additional repeat IDs for frozen candidates. This is a small PDCA check, not a high-confidence guarantee.',
            'algorithm': 'Strict majority, union, degree-priority repair, peeling and centroid remain fixed. Size<=d rows are unchanged; overflow is discard vs top votes, with public index tie breaking.',
            'capture': 'All runs save graph/trajectory diagnostics and first-screen raw-vote hashes. Full vote arrays are saved for confirmation only; no diagnostic oracle queries.',
            'source_sha256': {name: digest(ROOT/name) for name in SOURCES}}


def first_screen_hash(votes):
    """Fingerprint the raw observations without saving a large array per grid run."""
    h = hashlib.sha256(votes.patterns.astype('<u4').tobytes())
    width = (votes.n+7)//8
    h.update(len(votes.group_masks).to_bytes(8, 'little'))
    for masks in votes.group_masks:
        h.update(len(masks).to_bytes(8, 'little'))
        for mask in masks:
            h.update(mask.to_bytes(width, 'little'))
    return h.hexdigest()


def run_proposal(job, output, variant, full_votes=False, query_limit='target_n'):
    with row_cap_policy(POLICIES[variant]) as votes, draft_policy('first_bank') as capture:
        row = base.run_job(job, output, query_limit=query_limit)
    row.update(study_variant=variant, row_cap_policy=POLICIES[variant],
               draft_policy='first_bank', chunks=1,
               draft_metadata=save_capture(capture, output, base.job_name(job)),
               first_screen_raw_sha256=first_screen_hash(votes[0]) if votes else None,
               vote_metadata=save_votes(votes, output, base.job_name(job)) if full_votes else [],
               full_votes_saved=full_votes)
    return row


def paired_check(records):
    lookup = {v: {tuple(r['job']): r for r in rows} for v, rows in records.items()}
    assert set(lookup['reference']) == set(lookup['topd'])
    unchanged = 0
    for job, a in lookup['reference'].items():
        b = lookup['topd'][job]
        for key in ('seeds', 'edges_sha256', 'weights_sha256', 'fields_sha256', 'first_screen_raw_sha256'):
            assert a[key] == b[key], (job, key)
        assert a['draft_metadata'] == b['draft_metadata'], (job, 'draft')
        no_overflow = all(s.get('complete') and s.get('truncated_rows') == 0
                          for s in a['screen_observations'])
        if a['status'] == 'complete' and no_overflow:
            for key in ('status', 'total', 'counterfactual', 'rounds', 'depth', 'kl_per_token', 'batch_size_histogram'):
                assert json.loads(json.dumps(a[key])) == json.loads(json.dumps(b[key])), (job, key)
            unchanged += 1
    return {'pairs': len(lookup['reference']), 'first_screen_and_target_hashes_match': True,
            'no_overflow_pairs_with_identical_cost_and_score': unchanged}


def execute_proposals(out, config, chosen, seeds, phase, workers, state):
    jobs = [base.proposal_job(t, config['n'], seed, (p, m, d, tau))
            for t, p, m, d, tau in chosen for seed in seeds]
    records, streams, pending = {}, {}, []
    for variant in POLICIES:
        local = out/phase/variant
        local.mkdir(parents=True, exist_ok=True)
        freeze_json(local/'protocol.json', {'phase': phase, 'variant': variant,
            'row_cap_policy': POLICIES[variant], 'jobs': jobs, 'design': config})
        base.ensure_profiles(jobs, local)
        rows = read_runs(local/'proposal_runs.jsonl')
        done = {tuple(r['job']) for r in rows}
        assert len(done) == len(rows) and done <= set(jobs)
        records[variant] = rows
        streams[variant] = (local/'proposal_runs.jsonl').open('a')
        pending.extend((j, local, variant, phase == 'confirm') for j in jobs if j not in done)
    state.update(stage=phase, stage_jobs=2*len(jobs), stage_finished=sum(map(len, records.values())))
    atomic_json(out/'status.json', state)
    try:
        with ProcessPoolExecutor(max_workers=workers) as pool:
            futures = [pool.submit(run_proposal, *task) for task in pending]
            for future in as_completed(futures):
                row = future.result()
                variant = row['study_variant']
                records[variant].append(row)
                streams[variant].write(json.dumps(row, separators=(',', ':'), allow_nan=False)+'\n')
                streams[variant].flush()
                state.update(stage_finished=sum(map(len, records.values())), updated_utc=utc())
                atomic_json(out/'status.json', state)
                print(f'{phase} {state["stage_finished"]}/{state["stage_jobs"]} {variant} '
                      f'{base.job_name(row["job"])} Q={row["total"]} KL={row["kl_per_token"]} '
                      f'screens={row["screen_calls"]} {row["status"]}', flush=True)
    finally:
        for stream in streams.values():
            stream.close()
    freeze_json(out/phase/'paired_audit.json', paired_check(records))
    for variant, rows in records.items():
        summary = base.summarize(rows, seeds)
        freeze_json(out/phase/variant/'summary.json', summary)
        freeze_json(out/phase/variant/'matched_budgets.json', base.match_budgets(summary))
    return records


def select_candidates(records, config):
    reasons = defaultdict(list)
    def add(row, reason):
        reasons[base.setting_key(row)].append(reason)
    def error(row):
        return (max(1e-12, row['kl_per_token']), row['total'], base.setting_key(row))
    def cost(row):
        return (row['total'], max(1e-12, row['kl_per_token']), base.setting_key(row))
    for variant, rows in records.items():
        for target in ('matching', 'path'):
            good = [r for r in rows if r['target'] == target and r['status'] == 'complete']
            for limit in sorted({min(config['n'], q) for q in (1000, 2500, 5000, config['n'])}):
                eligible = [r for r in good if r['total'] <= limit]
                if eligible:
                    add(min(eligible, key=error), f'{variant}_min_KL_Q_le_{limit}')
            if good:
                add(min(good, key=cost), f'{variant}_cheapest_complete')
    lookup = {base.setting_key(r): r for r in records['reference']}
    for target in ('matching', 'path'):
        pairs = [(lookup[base.setting_key(r)], r) for r in records['topd']
                 if r['target'] == target and r['status'] == 'complete'
                 and lookup[base.setting_key(r)]['status'] == 'complete']
        def ratio(pair):
            return (max(1e-12, pair[0]['kl_per_token'])/max(1e-12, pair[1]['kl_per_token']),
                    base.setting_key(pair[0]))
        if pairs:
            add(min(pairs, key=ratio)[0], 'smallest_paired_KL_ratio_including_adverse')
            add(max(pairs, key=ratio)[0], 'largest_paired_KL_ratio')
    for setting in config['settings']:
        if config['smoke'] or tuple(setting) in {(t, *s) for _, t, s, _ in ANCHORS}:
            reasons[tuple(setting)].append('fixed_control')
    return {'rule': config['selection'], 'settings': sorted(reasons),
            'reasons': [{'setting': k, 'reasons': reasons[k]} for k in sorted(reasons)]}


def baselines(out, config, records, workers, state):
    stage = out/'confirm'
    jobs, matches = set(), {}
    for variant in POLICIES:
        matches[variant] = json.loads((stage/variant/'matched_budgets.json').read_text())
        jobs.update(('baseline', r['target'], config['n'], seed, policy, 0, r['baseline_batches'], 0, 0.)
                    for r in matches[variant] for seed in config['confirm_seeds']
                    for policy in ('random', 'confidence'))
    local = stage/'baselines'
    local.mkdir(exist_ok=True)
    freeze_json(local/'jobs.json', sorted(jobs))
    state.update(stage='confirmation_baselines', stage_jobs=len(jobs),
                 stage_finished=len(read_runs(local/'baseline_runs.jsonl')), updated_utc=utc())
    atomic_json(out/'status.json', state)
    rows = base.execute(sorted(jobs), local/'baseline_runs.jsonl', workers, local)
    state.update(stage_finished=len(rows), updated_utc=utc())
    atomic_json(out/'status.json', state)
    for variant in POLICIES:
        freeze_json(stage/variant/'comparisons.json',
                    base.compare(records[variant], rows, matches[variant], config['confirm_seeds']))
    return rows


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
        state = {'status': 'running', 'pid': os.getpid(), 'workers': args.workers,
                 'started_utc': utc(), 'stage': 'preparing', 'output': str(out)}
        started = perf_counter()
        atomic_json(out/'status.json', state)
        try:
            load_backend()
            exploratory = execute_proposals(out, config, config['settings'], config['explore_seeds'],
                                            'explore', args.workers, state)
            selection = select_candidates(exploratory, config)
            freeze_json(out/'selection.json', selection)
            confirmed = execute_proposals(out, config, selection['settings'], config['confirm_seeds'],
                                          'confirm', args.workers, state)
            baseline_rows = baselines(out, config, confirmed, args.workers, state)
            state.update(stage='reporting', updated_utc=utc())
            atomic_json(out/'status.json', state)
            from report_row_cap_grid import report
            report(out)
            assert {name: digest(ROOT/name) for name in SOURCES} == config['source_sha256'], 'Source changed during execution; please inspect before accepting the results.'
            state.update(status='complete', stage='complete',
                         proposal_runs=sum(map(len, exploratory.values()))+sum(map(len, confirmed.values())),
                         baseline_runs=len(baseline_rows), seconds=perf_counter()-started, finished_utc=utc())
            freeze_json(out/'execution.json', state)
        except BaseException:
            state.update(status='failed', failed_utc=utc(), traceback=traceback.format_exc())
            raise
        finally:
            atomic_json(out/'status.json', state)
        print(json.dumps(state), flush=True)


if __name__ == '__main__':
    main()
