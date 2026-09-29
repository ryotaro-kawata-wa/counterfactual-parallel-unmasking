"""Compare frozen previous settings under separate overflow and draft variants."""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
from time import perf_counter

import numpy as np

import explore_minimal as base
from draft_policy import save_capture
from minimal_oracle import load_backend
from row_cap_variants import draft_seed, initial_draft, row_cap_policy, save_votes
from validate import digest, freeze_json, read_runs


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT/'results'/'row_cap_study'
PREVIOUS = ROOT/'results'/'precision_chunk_study'/'confirm'
N, SEEDS = 16384, (8, 9)
VARIANTS = {'reference': ('discard', 'first_bank'),
            'topd': ('top_votes', 'first_bank'),
            'sampled_draft': ('discard', 'initial_sample')}
SETTINGS = (
    ('M1', 'matching', (3, 81, 9, .0001), 'Previous lower-query precision candidate G1'),
    ('M2', 'matching', (4, 61, 9, .0001), 'Previous best precision candidate G6'),
    ('P1', 'path', (4, 25, 36, .01), 'Previous low-query candidate H1'),
    ('P2', 'path', (4, 65, 36, .01), 'Previous best KL with mean Q<=3000, H3'),
    ('P3', 'path', (6, 49, 18, .01), 'Previous higher-precision control H7'),
    ('P4', 'path', (6, 49, 18, .003), 'Previous row-overflow precision control H6'),
    ('P5', 'path', (6, 49, 36, .003), 'Previous best KL and larger-row-cap control H8'),
)
SOURCES = tuple(dict.fromkeys((*base.SOURCES, 'draft_policy.py', 'row_cap_variants.py', 'row_cap_study.py')))


def jobs():
    return sorted(base.proposal_job(target, N, seed, setting)
                  for _, target, setting, _ in SETTINGS for seed in SEEDS)


def identity_id(job):
    return next(label for label, target, setting, _ in SETTINGS if (target, *setting) == (job[1], *job[5:]))


def run_proposal(job, output, variant):
    row_policy, draft = VARIANTS[variant]
    seed = draft_seed(job[1], job[2], job[3])
    with row_cap_policy(row_policy) as votes, initial_draft(draft, seed) as capture:
        row = base.run_job(job, output)
    row.update(study_variant=variant, row_cap_policy=row_policy, draft_policy=draft,
        setting_id=identity_id(job), chunks=1,
        draft_seed=seed if draft == 'initial_sample' else None,
        draft_metadata=save_capture(capture, output, base.job_name(job)),
        vote_metadata=save_votes(votes, output, base.job_name(job)))
    return row


def protocol(variant):
    result = base.protocol(jobs(), variant)
    result.update(study_variant=variant, row_cap_policy=VARIANTS[variant][0],
        draft_policy=VARIANTS[variant][1], frozen_settings=SETTINGS,
        selection='All settings fixed from the previous study before any new result; no reselection.',
        seed_role='Paired PDCA reuse of seeds 8/9; these are not fresh holdout seeds.',
        algorithm='Only overflow decoding OR initial product draft changes. Strict majority, union, peeling, degree repair, centroid and public caps remain.',
        draft_refresh='Initial only, from the existing preprocessing reply; fixed for all screens.',
        source_sha256={name: digest(ROOT/name) for name in SOURCES})
    return result


def proposals(workers):
    pending, records, streams = [], {}, {}
    for variant in VARIANTS:
        output = OUTPUT/variant
        output.mkdir(parents=True, exist_ok=True)
        freeze_json(output/'protocol.json', protocol(variant))
        base.ensure_profiles(jobs(), output)
        records[variant] = read_runs(output/'proposal_runs.jsonl')
        done = {tuple(r['job']) for r in records[variant]}
        assert len(done) == len(records[variant]) and done <= set(jobs())
        pending.extend((job, output, variant) for job in jobs() if job not in done)
        streams[variant] = (output/'proposal_runs.jsonl').open('a')
    load_backend()
    started = perf_counter()
    try:
        with ProcessPoolExecutor(max_workers=workers) as pool:
            futures = [pool.submit(run_proposal, *task) for task in pending]
            for count, future in enumerate(as_completed(futures), 1):
                row = future.result()
                variant = row['study_variant']
                records[variant].append(row)
                streams[variant].write(json.dumps(row, separators=(',', ':'), allow_nan=False)+'\n')
                streams[variant].flush()
                print(f'proposal {count}/{len(pending)} {variant} {row["setting_id"]} seed{row["repeat"]} '
                      f'Q={row["total"]} KL={row["kl_per_token"]} screens={row["screen_calls"]} '
                      f'{row["status"]} elapsed={perf_counter()-started:.1f}s', flush=True)
    finally:
        for stream in streams.values():
            stream.close()
    for variant, rows in records.items():
        summary = base.summarize(rows, SEEDS)
        freeze_json(OUTPUT/variant/'summary.json', summary)
        freeze_json(OUTPUT/variant/'matched_budgets.json', base.match_budgets(summary))
    return records


def reference_check(records):
    old_out = PREVIOUS/'J1'/'first_bank'
    old = {tuple(r['job']): r for r in read_runs(old_out/'proposal_runs.jsonl')}
    checked = []
    for row in records['reference']:
        previous = old[tuple(row['job'])]
        for key in ('status', 'seeds', 'edges_sha256', 'weights_sha256', 'fields_sha256',
                    'total', 'counterfactual', 'rounds', 'depth', 'kl_per_token', 'batch_size_histogram'):
            # Please compare JSON-normalized mappings: histogram keys are ints
            # before serialization and strings in the historical JSONL record.
            assert json.loads(json.dumps(row[key])) == previous[key], (row['setting_id'], key)
        with np.load(OUTPUT/'reference'/row['trace']) as new, np.load(old_out/previous['trace']) as saved:
            assert set(new.files) == set(saved.files)
            for key in new.files:
                np.testing.assert_array_equal(new[key], saved[key])
        checked.append({'job': row['job'], 'previous_source': str((old_out/'proposal_runs.jsonl').relative_to(ROOT)),
                        'previous_source_sha256': digest(old_out/'proposal_runs.jsonl')})
    freeze_json(OUTPUT/'reference_replay.json', checked)


def baselines(records, workers):
    wanted, matches = set(), {}
    for variant in VARIANTS:
        matches[variant] = json.loads((OUTPUT/variant/'matched_budgets.json').read_text())
        subset = sorted({('baseline', r['target'], N, seed, policy, 0, r['baseline_batches'], 0, 0.)
                        for r in matches[variant] for seed in SEEDS for policy in ('random', 'confidence')})
        freeze_json(OUTPUT/variant/'baseline_jobs.json', subset)
        wanted.update(subset)
    output = OUTPUT/'baselines'
    output.mkdir(exist_ok=True)
    freeze_json(output/'jobs.json', sorted(wanted))
    path = output/'baseline_runs.jsonl'
    existing = read_runs(path)
    done = {tuple(r['job']) for r in existing}
    source = PREVIOUS/'baselines'
    reusable = {tuple(r['job']): r for r in read_runs(source/'baseline_runs.jsonl')}
    with path.open('a') as stream:
        for job in sorted(wanted-done):
            if job not in reusable:
                continue
            row = dict(reusable[job])
            destination = output/row['trace']
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source/row['trace'], destination)
            row['reused_from'] = str((source/'baseline_runs.jsonl').relative_to(ROOT))
            row['reused_source_sha256'] = digest(source/'baseline_runs.jsonl')
            stream.write(json.dumps(row, separators=(',', ':'), allow_nan=False)+'\n')
    all_rows = base.execute(sorted(wanted), path, workers, output)
    lookup = {tuple(r['job']): r for r in all_rows}
    for variant in VARIANTS:
        subset = [lookup[tuple(job)] for job in json.loads((OUTPUT/variant/'baseline_jobs.json').read_text())]
        freeze_json(OUTPUT/variant/'comparisons.json', base.compare(records[variant], subset, matches[variant], SEEDS))
    return all_rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=6)
    args = parser.parse_args()
    if args.workers < 1:
        parser.error('Please use at least one process.')
    OUTPUT.mkdir(parents=True, exist_ok=True)
    freeze_json(OUTPUT/'design.json', {'n': N, 'seeds': SEEDS, 'settings': SETTINGS,
        'variants': VARIANTS, 'proposal_jobs': jobs(), 'per_run_query_cap': N,
        'main_budget': 3000, 'seed_role': 'Paired existing-seed PDCA, not independent confirmation.',
        'comparison': 'Mean total Q primary; mean adaptive depth secondary. Censored settings separate.',
        'source_sha256': {name: digest(ROOT/name) for name in SOURCES}})
    started = perf_counter()
    records = proposals(args.workers)
    reference_check(records)
    baseline_rows = baselines(records, args.workers)
    result = {'complete': True, 'proposal_runs': sum(map(len, records.values())),
              'baseline_runs': len(baseline_rows), 'workers': args.workers,
              'seconds': perf_counter()-started, 'finished_utc': datetime.now(timezone.utc).isoformat()}
    (OUTPUT/'execution.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
