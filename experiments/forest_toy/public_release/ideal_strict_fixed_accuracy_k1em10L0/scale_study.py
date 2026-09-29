"""Compare two N values under one logarithmic M rule and a fixed-degree control."""

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict
import hashlib
import json
from math import ceil, log
from pathlib import Path
from time import perf_counter

import numpy as np

from budget_core import BudgetCommitCursor, BudgetObserver, BudgetOracle, CommitTrace, QueryBudgetExceeded
from budget_study import SOURCES as BUDGET_SOURCES, summarize as budget_summary
from explore import FixedColorings
from toy import StarForestOracle, audit, make_forest, sample
from tradeoff import aggregate, seeds_for, write_json
from tradeoff_core import DensityRecorder, random_batch_sample, schedule_audit
from tune import BETA
from validate import EXPLORE_SEED, digest, freeze_json, read_runs


BASE_N, LARGE_N, REPEATS = 4096, 16384, 10
ANCHORS = {"matching": (33, 37, 41, 45, 49, 57, 65, 73),
           "stars_original": (11, 13, 15, 17, 19, 21, 23, 25)}
CONTROL_ANCHORS = (13, 19, 25)
PARAMETERS = {"matching": (4, 9), "stars_original": (6, 17), "stars_fixed64": (6, 17)}
PRIOR_PHASES = ("budget_coarse", "budget_refinement", "budget_degree", "budget_boundary")
SOURCES = (*BUDGET_SOURCES, "scale_study.py")


def scaled_m(anchor, n):
    minimum = ceil(anchor * log(n) / log(BASE_N))
    return minimum + (minimum % 2 == 0)


def agreed_settings():
    settings = [(target, n, PARAMETERS[target][0], scaled_m(anchor, n), PARAMETERS[target][1])
                for target, anchors in ANCHORS.items() for n in (BASE_N, LARGE_N) for anchor in anchors]
    settings += [("stars_fixed64", LARGE_N, 6, scaled_m(anchor, LARGE_N), 17) for anchor in CONTROL_ANCHORS]
    return sorted(settings)


def run_seeds(target, n, repeat, kind, budget=0):
    # Please pair both star rules, including their permutation and commit draws.
    seed_target = "stars_original" if target == "stars_fixed64" else target
    return seeds_for(EXPLORE_SEED, n, seed_target, repeat, kind, budget)


def make_target(n, target, seed, reuse_queries=True):
    if target in ("matching", "stars_original"):
        return make_forest(n, "matching" if target == "matching" else "stars", seed,
                           coupling=.5, reuse_queries=reuse_queries)
    if target != "stars_fixed64":
        raise ValueError("Please use an agreed matching or star target.")
    order = np.random.default_rng(seed).permutation(n)
    root_of = np.arange(n)
    for start in range(0, n, 65):
        group = order[start:start+65]
        root_of[group] = group[0]
    return StarForestOracle(root_of, .5/64, reuse_queries=reuse_queries)


def target_metadata(oracle):
    degrees = np.bincount(oracle.component[oracle.leaf], minlength=len(oracle.roots))
    return {"max_degree": int(degrees.max()), "edge_count": int(oracle.leaf.sum()),
            "component_count": len(oracle.roots),
            "root_of_sha256": hashlib.sha256(oracle.root_of.astype("<i8").tobytes()).hexdigest()}


def row_key(row):
    return (row["target"], row["n"], row["palette"], row["colorings"], row["parameters"]["d"], row["repeat"])


def baseline_key(row):
    return (row["target"], row["n"], row["budget"], row["repeat"])


def run_job(job):
    kind, target, n, p, m, d, repeat = job
    np.seterr(divide="raise", over="raise", invalid="raise")
    seeds = run_seeds(target, n, repeat, kind, m if kind == "baseline" else 0)
    underlying = make_target(n, target, seeds[0], reuse_queries=kind == "proposal")
    started = perf_counter()
    if kind == "baseline":
        result = random_batch_sample(underlying, m, seeds[1], seeds[2])
        score = {k: v for k, v in result.items() if k not in ("sample", "batches")}
        checked = schedule_audit(underlying, result["batches"])
        assert underlying.cost.total == m
        return {"job": list(job), "kind": kind, "phase": "scale_exploration", "target": target,
                "n": n, "repeat": repeat, "budget": m, "depth": m, "screen_calls": 0,
                "seeds": seeds, "theta": underlying.theta, "vocab": underlying.vocab,
                "seconds": perf_counter()-started, **score, **checked, **asdict(underlying.cost),
                "total": underlying.cost.total, **target_metadata(underlying),
                "sample_sha256": hashlib.sha256(result["sample"].astype("<i4").tobytes()).hexdigest(),
                "batch_size_histogram": {str(k): v for k, v in sorted(Counter(map(len, result["batches"])).items())}}
    oracle = BudgetOracle(underlying, n)
    params = FixedColorings(n, oracle.theta, d=d, beta=BETA, palette_override=p, coloring_count=m)
    recorder, observer = DensityRecorder(n), BudgetObserver(params, oracle)
    trace = CommitTrace(recorder, n)
    stopped = None
    try:
        result = sample(oracle, params, seeds[1], seeds[2], observer=observer,
                        commit_session=BudgetCommitCursor(oracle), commit_observer=trace)
    except QueryBudgetExceeded as error:
        stopped = error.details
    sample_seconds = perf_counter()-started
    observer.finish_observation(underlying)
    if stopped is None:
        score = recorder.finish(underlying, result["sample"])
        checked = audit(underlying, params, result)
        structural = (checked["all_tokens_committed"] and checked["fallback"] is None
                      and checked["unsafe_batches"] == 0 and checked["low_degree_row_errors"] == 0
                      and checked["terminal_row_errors"] == 0)
    else:
        score = {"tv_score": None, "log_q_over_p": None}
        checked = {"all_tokens_committed": False, "unsafe_batches": None, "fallback": None}
        structural = None
    elapsed = perf_counter()-started
    return {"job": list(job), "kind": kind, "phase": "scale_exploration", "target": target,
            "n": n, "palette": p, "colorings": m, "parameters": asdict(params), "repeat": repeat,
            "seeds": seeds, "theta": oracle.theta, "vocab": oracle.vocab, **target_metadata(underlying),
            "separation_lhs_over_signal": (4*params.eps+params.tail_tolerance)/params.signal,
            "status": "censored" if stopped else "complete", "budget_stop": stopped, "query_limit": n,
            "screen_calls": len(observer.screens), "completed_screens": sum(s["complete"] for s in observer.screens),
            "screen_cap": params.screen_cap, "screen_cap_reached": len(observer.screens) == params.screen_cap,
            "screen_observations": observer.screens, "depth": 1+len(observer.screens)+oracle.cost.rounds,
            "committed_tokens": int((trace.history >= 0).sum()), "batch_size_histogram": trace.histogram(),
            "sample_sha256": hashlib.sha256(trace.history.astype("<i4").tobytes()).hexdigest() if stopped is None else None,
            "sample_seconds": sample_seconds, "posthoc_seconds": elapsed-sample_seconds, "seconds": elapsed,
            "structural_success": structural, **score, **checked, **asdict(oracle.cost), "total": oracle.cost.total}


def prior_records():
    proposals, baselines, provenance = {}, {}, {}
    for phase in PRIOR_PHASES:
        for filename in ("proposal_runs.jsonl", "baseline_runs.jsonl"):
            path = Path(__file__).with_name("results") / phase / filename
            provenance[str(path.resolve())] = digest(path)
            for row in read_runs(path):
                if row["target"] not in ANCHORS or row["n"] != BASE_N:
                    continue
                if row["kind"] == "proposal":
                    k, destination = row_key(row), proposals
                else:
                    k, destination = baseline_key(row), baselines
                if k in destination:
                    old = destination[k][0]
                    assert (old["total"], old["tv_score"], old["sample_sha256"]) == (
                            row["total"], row["tv_score"], row["sample_sha256"])
                else:
                    destination[k] = (row, str(path.resolve()))
    return proposals, baselines, provenance


def summarize(records):
    output = {"complete_settings": [], "censored_settings": [], "runs": len(records), "settings": 0}
    for n in sorted({r["n"] for r in records}):
        local = budget_summary([r for r in records if r["n"] == n])
        output["settings"] += local["settings"]
        for category in ("complete_settings", "censored_settings"):
            for row in local[category]:
                row["n"] = n
                if category == "complete_settings":
                    row["total_over_n"] = row["total"]/n
                    group = [r for r in records if row_key(r)[:5] ==
                             (row["target"], n, row["palette"], row["colorings"], row["d"])]
                    row["first_missed_high_degree"] = float(np.mean([r["screen_observations"][0]["posthoc_unpeeled_degree_gt_d"] for r in group]))
                output[category].append(row)
    return output


def match_budgets(summary):
    return [{"target": r["target"], "n": r["n"], "palette": r["palette"], "colorings": r["colorings"],
             "d": r["d"], "axis": axis, "proposal_mean": r[axis], "baseline_batches": int(np.floor(r[axis]+.5))}
            for r in summary["complete_settings"] for axis in ("total", "depth")]


def comparisons(proposals, baselines, matches):
    results = []
    for match in matches:
        k = (match["target"], match["n"], match["palette"], match["colorings"], match["d"])
        a = sorted([r for r in proposals if row_key(r)[:5] == k], key=lambda r:r["repeat"])
        b = sorted([r for r in baselines if baseline_key(r)[:3] ==
                    (match["target"], match["n"], match["baseline_batches"])], key=lambda r:r["repeat"])
        assert len(a) == len(b) == REPEATS
        assert [r["repeat"] for r in a] == [r["repeat"] for r in b] == list(range(REPEATS))
        assert all(x["seeds"][0] == y["seeds"][0] for x, y in zip(a, b))
        delta = np.asarray([y["tv_score"]-x["tv_score"] for x, y in zip(a, b)])
        results.append({**match, "proposal": aggregate(a), "baseline": aggregate(b),
                        "baseline_minus_proposal_tv": float(delta.mean()),
                        "paired_difference_se": float(delta.std(ddof=1)/np.sqrt(REPEATS))})
    return results


def execute(jobs, path, workers, reuse):
    records = read_runs(path)
    done = {tuple(r["job"]) for r in records}
    if len(records) != len(done) or not done <= set(jobs):
        raise ValueError("Please preserve every setting and seed when resuming.")
    with path.open("a") as stream:
        for job in jobs:
            if job in done:
                continue
            kind, target, n, p, m, d, repeat = job
            k = tuple(job[1:]) if kind == "proposal" else (target, n, m, repeat)
            if k not in reuse:
                continue
            old, origin = reuse[k]
            row = json.loads(json.dumps(old))
            assert row["seeds"] == run_seeds(target, n, repeat, kind, m if kind == "baseline" else 0)
            row.update({"job": list(job), "phase": "scale_exploration", "reuse_source": origin,
                        **target_metadata(make_target(n, target, row["seeds"][0]))})
            records.append(row)
            stream.write(json.dumps(row, separators=(",", ":"))+"\n")
            done.add(job)
    pending = [job for job in jobs if job not in done]
    if not pending:
        return records
    started = perf_counter()
    with ProcessPoolExecutor(max_workers=workers) as pool, path.open("a") as stream:
        futures = [pool.submit(run_job, job) for job in pending]
        for future in as_completed(futures):
            try:
                row = future.result()
            except BaseException:
                for other in futures:
                    other.cancel()
                raise
            records.append(row)
            stream.write(json.dumps(row, separators=(",", ":"))+"\n")
            stream.flush()
            if len(records) % 10 == 0 or len(records) == len(jobs):
                print(f"{path.stem}: {len(records)}/{len(jobs)} {row['target']} N={row['n']} "
                      f"{row['job'][3:6]} {row.get('status', 'baseline')} Q={row['total']} "
                      f"TVscore={row['tv_score']} elapsed={perf_counter()-started:.1f}s", flush=True)
    execution_path = path.with_name(path.stem+"_execution.json")
    invocations = json.loads(execution_path.read_text()) if execution_path.exists() else []
    invocations.append({"workers": workers, "new_runs": len(pending), "seconds": perf_counter()-started})
    write_json(execution_path, invocations)
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--stage", choices=("all", "proposal", "baseline"), default="all")
    parser.add_argument("--settings", type=Path, help="Optional additional [target,N,p,M,d] settings.")
    parser.add_argument("--design-observation", type=Path, help="Prior frozen summary used to choose an additional round.")
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results") / "scale_study")
    args = parser.parse_args()
    if args.workers < 1:
        raise ValueError("Please use a positive worker count.")
    args.output.mkdir(parents=True, exist_ok=True)
    settings = (sorted(set(tuple(s) for s in json.loads(args.settings.read_text()))) if args.settings else agreed_settings())
    for target, n, p, m, d in settings:
        if target not in PARAMETERS or n not in (BASE_N, LARGE_N) or p < 3 or m < 1 or m % 2 != 1 or d < 9:
            raise ValueError("Please use the agreed N values, a valid target, p>=3, odd M, and d>=9.")
    old_proposals, old_baselines, provenance = prior_records()
    protocol = {"repeats": REPEATS, "settings": settings, "base_n": BASE_N, "large_n": LARGE_N,
                "anchor_M": ANCHORS, "control_anchor_M": CONTROL_ANCHORS, "master_seed": EXPLORE_SEED,
                "M_rule": "Smallest odd integer >= M0*log(N)/log(4096). Initial p,d remain fixed by family.",
                "purpose": "Compare N=4096 and 16384 using matching and the original star rule; "
                           "add three D=64 control settings at N=16384. Adaptive PDCA, not a held-out significance study.",
                "targets": "Matching theta=0.5. Original stars D=max(16,ceil(sqrt(N))), theta=0.5/D. "
                           "Control stars D=64, theta=1/128. All use the same permutation construction. "
                           "At N=4096 the control equals the original target and shares its recorded results.",
                "control_interpretation": "Fixed D changes the N-dependence of hub counts. With fixed d=17, "
                                          "singleton hub peeling leaves an O(N/65) commit term; this is a diagnostic control.",
                "seed_design": "Reuse the prior N4096 seeds, including censored outcomes. N is part of the seed domain. "
                               "At each N, both star rules share graph-permutation/controller/commit seeds. "
                               "Baselines use a separate draw domain; equal budgets share a baseline.",
                "budget": "Hard Q=preprocessing+distinct public-input counterfactual submissions+commit rounds <= N. "
                          "Reject an entire packed family before evaluation if it does not fit; spent Q may be below N. "
                          "Keep any configuration with a censored seed in a separate table. No full TV for stopped runs.",
                "metrics": "Mean total Q versus mean joint-TV density score; retain median,p90,SE,Q/N and sequential "
                           "cost 1+screens+R. TV<=0.05 is a PDCA guide, not a plotting filter or a guarantee.",
                "baseline": "B=round-half-up(proposal mean total Q), separately mean sequential cost. "
                            "B balanced nonempty batches, ten seeds. All finished settings and failed outcomes are retained.",
                "fixed_parameters": {"beta": BETA, "chunks": 1, "vocab": 2048},
                "theory": "M retains logarithmic order but uses empirical constants. Small p,M do not inherit "
                          "the manuscript's uniform success guarantee. Sampler, exact oracle, and signal certificate are preserved.",
                "design_observation": str(args.design_observation.resolve()) if args.design_observation else None,
                "design_observation_sha256": digest(args.design_observation) if args.design_observation else None,
                "prior_sha256": provenance,
                "source_sha256": {name: digest(Path(__file__).with_name(name)) for name in SOURCES}}
    freeze_json(args.output / "protocol.json", protocol)
    jobs = [("proposal", *setting, repeat) for setting in settings for repeat in range(REPEATS)]
    proposals = (execute(jobs, args.output / "proposal_runs.jsonl", args.workers, old_proposals)
                 if args.stage != "baseline" else read_runs(args.output / "proposal_runs.jsonl"))
    assert {tuple(r["job"]) for r in proposals} == set(jobs)
    summary = summarize(proposals)
    freeze_json(args.output / "summary.json", summary)
    matches = match_budgets(summary)
    freeze_json(args.output / "matched_budgets.json", matches)
    if args.stage == "proposal":
        return
    baseline_jobs = sorted({("baseline", item["target"], item["n"], 0, item["baseline_batches"], 0, repeat)
                            for item in matches for repeat in range(REPEATS)})
    baselines = execute(baseline_jobs, args.output / "baseline_runs.jsonl", args.workers, old_baselines)
    freeze_json(args.output / "comparisons.json", comparisons(proposals, baselines, matches))
    print(f"Finished {summary['settings']} settings: {len(summary['complete_settings'])} complete, "
          f"{len(summary['censored_settings'])} in the separate censoring table.", flush=True)


if __name__ == "__main__":
    main()
