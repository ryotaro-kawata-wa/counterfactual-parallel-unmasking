"""Family-specific, ten-seed exploration with a hard total-query limit of N."""

import argparse
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
from time import perf_counter

import numpy as np

from budget_core import BudgetCommitCursor, BudgetObserver, BudgetOracle, CommitTrace, QueryBudgetExceeded
from explore import FixedColorings
from toy import audit, make_forest, sample
from tradeoff import aggregate, run_one as legacy_baseline, seeds_for, write_json
from tradeoff_core import DensityRecorder
from tree_oracle import TreeDensityRecorder, load_backend, make_tree
from tree_study import TREE_IDS, TREE_SEED, audit_tree, run_job as tree_baseline
from tune import BETA, TARGETS
from validate import EXPLORE_SEED, digest, freeze_json, read_runs


N, REPEATS = 4096, 10
FAMILIES = ("matching", "stars_original", "binary", "path")
COARSE = {
    "matching": {3: (17, 49, 81), 4: (17, 49, 73), 5: (11, 35, 61), 6: (9, 25, 45), 8: (7, 17, 33)},
    "stars_original": {3: (9, 45, 89), 4: (9, 35, 65), 5: (5, 21, 39), 6: (3, 15, 27), 8: (5, 9, 13)},
    "binary": {3: (27, 135, 269), 4: (15, 71, 143), 5: (9, 43, 89), 6: (7, 29, 61), 8: (3, 17, 33)},
    "path": {3: (27, 135, 269), 4: (15, 71, 143), 5: (9, 43, 89), 6: (7, 29, 61), 8: (3, 17, 33)},
}
SOURCES = ("toy.py", "tradeoff_core.py", "tradeoff.py", "tune.py", "explore.py", "validate.py",
           "tree_bp.c", "tree_oracle.py", "tree_study.py", "budget_core.py", "budget_study.py")
LEGACY_PATHS = ("exploration/runs.jsonl", "validation/refinement_runs.jsonl",
                "tree_study/new_proposal_runs.jsonl", "tree_extension/proposal_runs.jsonl",
                "degree_exploration/runs.jsonl")


def key(row):
    return (row["target"], row["palette"], row["colorings"], row["parameters"]["d"], row["repeat"])


def proposal_seeds(target, repeat):
    if target in TREE_IDS:
        graph = int(np.random.SeedSequence([TREE_SEED, 0, TREE_IDS[target], N, repeat]).generate_state(1)[0])
        other = np.random.SeedSequence([TREE_SEED, 1, TREE_IDS[target], N, repeat]).generate_state(2).tolist()
        return [graph, *other]
    return seeds_for(EXPLORE_SEED, N, target, repeat, "proposal")


def run_job(job):
    kind, target, p, m, d, repeat = job
    if kind == "baseline":
        row = (tree_baseline((kind, target, 0, m, repeat)) if target in TREE_IDS else
               legacy_baseline((kind, target, N, m, repeat, EXPLORE_SEED)))
        row["job"] = list(job)
        return row
    np.seterr(divide="raise", over="raise", invalid="raise")
    seeds = proposal_seeds(target, repeat)
    underlying = (make_tree(N, target, seeds[0], coupling=.5) if target in TREE_IDS else
                  make_forest(N, TARGETS[target]["family"], seeds[0], coupling=.5, reuse_queries=True))
    oracle = BudgetOracle(underlying, N)
    params = FixedColorings(N, oracle.theta, d=d, beta=BETA, palette_override=p, coloring_count=m)
    recorder = TreeDensityRecorder(N) if target in TREE_IDS else DensityRecorder(N)
    trace, observer = CommitTrace(recorder, N), BudgetObserver(params, oracle)
    session = None if target in TREE_IDS else BudgetCommitCursor(oracle)
    started, result, stopped = perf_counter(), None, None
    try:
        result = sample(oracle, params, seeds[1], seeds[2], observer=observer,
                        commit_session=session, commit_observer=trace)
    except QueryBudgetExceeded as error:
        stopped = error.details
    sample_seconds = perf_counter() - started
    observer.finish_observation(underlying)
    if stopped is None:
        score = recorder.finish(underlying, result["sample"])
        checked = (audit_tree(underlying, params, result, observer) if target in TREE_IDS else
                   audit(underlying, params, result))
        structural = (checked["all_tokens_committed"] and checked["fallback"] is None
                      and checked["unsafe_batches"] == 0 and checked["low_degree_row_errors"] == 0
                      and checked["terminal_row_errors"] == 0)
    else:
        # Please do not assign a full-sample error or a success flag to censoring.
        score = {"tv_score": None, "log_q_over_p": None}
        checked = {"all_tokens_committed": False, "unsafe_batches": None, "fallback": None}
        structural = None
    elapsed = perf_counter() - started
    maximum = (underlying.max_degree if target in TREE_IDS else
               int(np.bincount(underlying.component[underlying.leaf], minlength=len(underlying.roots)).max()))
    return {"job": list(job), "kind": kind, "phase": "budget_exploration", "target": target,
            "n": N, "palette": p, "colorings": m, "parameters": asdict(params), "repeat": repeat,
            "seeds": seeds, "theta": oracle.theta, "vocab": oracle.vocab, "max_degree": maximum,
            "separation_lhs_over_signal": (4*params.eps + params.tail_tolerance)/params.signal,
            "status": "censored" if stopped else "complete", "budget_stop": stopped, "query_limit": N,
            "screen_calls": len(observer.screens), "completed_screens": sum(s["complete"] for s in observer.screens),
            "screen_cap": params.screen_cap, "screen_cap_reached": len(observer.screens) == params.screen_cap,
            "screen_observations": observer.screens, "depth": 1 + len(observer.screens) + oracle.cost.rounds,
            "committed_tokens": int((trace.history >= 0).sum()), "batch_size_histogram": trace.histogram(),
            "sample_sha256": hashlib.sha256(trace.history.astype("<i4").tobytes()).hexdigest() if stopped is None else None,
            "sample_seconds": sample_seconds, "posthoc_seconds": elapsed-sample_seconds, "seconds": elapsed,
            "structural_success": structural, **score, **checked, **asdict(oracle.cost), "total": oracle.cost.total}


def legacy_index():
    indexed, provenance = {}, {}
    for name in LEGACY_PATHS:
        path = Path(__file__).with_name("results") / name
        provenance[name] = digest(path)
        for row in read_runs(path):
            if row["target"] not in FAMILIES or row["n"] != N or row["seeds"] != proposal_seeds(row["target"], row["repeat"]):
                continue
            k = key(row)
            if k in indexed:
                old = indexed[k][0]
                assert (old["sample_sha256"], old["total"], old["tv_score"]) == (row["sample_sha256"], row["total"], row["tv_score"])
            else:
                indexed[k] = (row, name)
    return indexed, provenance


def summarize(rows):
    groups = defaultdict(list)
    for row in rows:
        groups[key(row)[:4]].append(row)
    complete, censored = [], []
    for (target, p, m, d), group in sorted(groups.items()):
        assert len(group) == REPEATS and {r["repeat"] for r in group} == set(range(REPEATS))
        finished = [r for r in group if r["status"] == "complete"]
        stopped = [r for r in group if r["status"] == "censored"]
        combined = {"target": target, "palette": p, "colorings": m, "d": d,
                    "runs": REPEATS, "complete_runs": len(finished), "censored_runs": len(stopped)}
        if stopped:
            scores = sum(r["tv_score"] for r in finished)
            combined.update({"spent_Q_mean": float(np.mean([r["total"] for r in group])),
                             "spent_Q_median": float(np.median([r["total"] for r in group])),
                             "spent_Q_p90": float(np.quantile([r["total"] for r in group], .9)),
                             "stop_stages": dict(Counter(r["budget_stop"]["stage"] for r in stopped)),
                             "empirical_full_score_mean_bounds": [scores/REPEATS, (scores+len(stopped))/REPEATS],
                             "committed_tokens_mean": float(np.mean([r["committed_tokens"] for r in group])),
                             "started_screens_mean": float(np.mean([r["screen_calls"] for r in group]))})
            censored.append(combined)
            continue
        combined.update(aggregate(group))
        for metric in ("total", "counterfactual", "rounds", "depth", "screen_calls"):
            combined[metric+"_median"] = float(np.median([r[metric] for r in group]))
            combined[metric+"_p90"] = float(np.quantile([r[metric] for r in group], .9))
        for metric in ("raw_degree_mean", "truncation_fraction", "peel_size", "incoming_claims_mean",
                       "posthoc_peel_degree_le_half_d", "posthoc_low_degree_row_errors"):
            combined["first_"+metric] = float(np.mean([r["screen_observations"][0][metric] for r in group]))
        combined["posthoc_false_peels"] = float(np.mean([sum(s["posthoc_peel_degree_le_half_d"]
            for s in r["screen_observations"] if s["next_action"] == "peel") for r in group]))
        combined["fallback_reasons"] = dict(Counter(r["fallback"] or "none" for r in group))
        complete.append(combined)
    return {"complete_settings": complete, "censored_settings": censored,
            "settings": len(groups), "runs": len(rows)}


def execute(jobs, path, workers, reuse=None):
    records = read_runs(path)
    done = {tuple(r["job"]) for r in records}
    if len(done) != len(records) or not done <= set(jobs):
        raise ValueError("Please preserve the frozen settings and all seeds when resuming.")
    reuse = {} if reuse is None else reuse
    with path.open("a") as stream:
        for job in jobs:
            if job in done or job[0] != "proposal" or tuple(job[1:]) not in reuse:
                continue
            old, source = reuse[tuple(job[1:])]
            if old["total"] > N:
                continue
            row = json.loads(json.dumps(old))
            row.update({"job": list(job), "phase": "budget_exploration", "status": "complete",
                        "budget_stop": None, "query_limit": N, "committed_tokens": N,
                        "completed_screens": row["screen_calls"], "reused_from": source})
            for screen in row["screen_observations"]:
                screen.update({"complete": True, "completed_colorings": row["colorings"]})
            records.append(row)
            stream.write(json.dumps(row, separators=(",", ":"))+"\n")
            done.add(job)
    pending = [job for job in jobs if job not in done]
    if not pending:
        return records
    load_backend()
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
            if len(records) % 20 == 0 or len(records) == len(jobs):
                print(f"{path.stem}: {len(records)}/{len(jobs)} {row['target']} {row['job'][2:5]} "
                      f"{row.get('status', 'baseline')} Q={row['total']} score={row['tv_score']} "
                      f"elapsed={perf_counter()-started:.1f}s", flush=True)
    execution_path = path.with_name(path.stem+"_execution.json")
    invocations = json.loads(execution_path.read_text()) if execution_path.exists() else []
    invocations.append({"workers": workers, "new_runs": len(pending), "seconds": perf_counter()-started})
    write_json(execution_path, invocations)
    return records


def match_budgets(summary):
    return [{"target": r["target"], "palette": r["palette"], "colorings": r["colorings"], "d": r["d"],
             "axis": axis, "proposal_mean": r[axis], "baseline_batches": int(np.floor(r[axis]+.5))}
            for r in summary["complete_settings"] for axis in ("total", "depth")]


def comparisons(proposals, baselines, matches):
    results = []
    for match in matches:
        wanted = (match["target"], match["palette"], match["colorings"], match["d"])
        a = sorted([r for r in proposals if key(r)[:4] == wanted], key=lambda r:r["repeat"])
        b = sorted([r for r in baselines if r["target"] == match["target"]
                    and r["budget"] == match["baseline_batches"]], key=lambda r:r["repeat"])
        assert len(a) == len(b) == REPEATS
        assert [r["repeat"] for r in a] == [r["repeat"] for r in b] == list(range(REPEATS))
        assert all(x["seeds"][0] == y["seeds"][0] for x, y in zip(a, b))
        delta = np.asarray([y["tv_score"]-x["tv_score"] for x, y in zip(a, b)])
        results.append({**match, "proposal": aggregate(a), "baseline": aggregate(b),
                        "baseline_minus_proposal_tv": float(delta.mean()),
                        "paired_difference_se": float(delta.std(ddof=1)/np.sqrt(REPEATS))})
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--settings", type=Path, help="Frozen JSON list of [target,p,M,d] settings for an additional round.")
    parser.add_argument("--design-observation", type=Path, help="The prior summary used to design this additional round.")
    parser.add_argument("--stage", choices=("all", "proposal", "baseline"), default="all")
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results") / "budget_coarse")
    args = parser.parse_args()
    if args.workers < 1:
        raise ValueError("Please use a positive worker count.")
    args.output.mkdir(parents=True, exist_ok=True)
    old, provenance = legacy_index()
    if args.settings:
        settings = sorted(set(tuple(item) for item in json.loads(args.settings.read_text())))
    else:
        settings = {(target, p, m, 9) for target, palettes in COARSE.items()
                    for p, ms in palettes.items() for m in ms}
        # Please retain historical nearby settings, including those that will
        # hit the cap; only their already-complete, in-budget runs are reused.
        settings |= {(target, p, m, d) for target, p, m, d, repeat in old
                     if d == 9 and p in (3, 4, 5, 6, 8) and m*p*(2*p-1)+2 <= N}
        settings = sorted(settings)
    for target, p, m, d in settings:
        if target not in FAMILIES or p < 3 or m < 1 or m % 2 != 1 or d < 9:
            raise ValueError("Please use an agreed family, p>=3, positive odd M, and d>=9.")
    protocol = {"n": N, "repeats": REPEATS, "settings": settings, "query_limit": N,
                "target_coupling": .5, "beta": BETA, "chunks": 1,
                "legacy_master_seed": EXPLORE_SEED, "tree_master_seed": TREE_SEED,
                "purpose": "Adaptive PDCA exploration, not held-out confirmation. Keep every attempted setting and seed, "
                           "including high-error points and all censored configurations.",
                "target": "Matching and original star forests, connected balanced binary tree and path. "
                          "theta=0.5/max_degree. Coupling per edge and component counts differ across families.",
                "budget": "Q=preprocessing+distinct counterfactual input states+commit rounds. Check before evaluation; "
                          "reject a packed family in full if it does not fit. Actual spent Q may be slightly below N. "
                          "No fallback or sample is manufactured on budget exhaustion.",
                "main_plot": "Only configurations with all ten runs complete within N. Mean total Q versus mean TV score; "
                             "also report median, p90, SE, and the sequential-stage axis.",
                "censoring": "Any censored seed sends the entire configuration to a separate table. No uncensored "
                             "mean-Q or TV estimate from a finished-only subset. Score completion bounds are not confidence intervals.",
                "risk": "E_graph,controller TV(P_graph,Q_graph,controller), estimated from actual commit likelihoods. "
                        "Mean score <=0.05 is a PDCA trigger only, never a plotting filter or an error guarantee.",
                "baseline": "For each complete configuration, fix B=round-half-up(mean Q), or mean sequential cost. "
                            "Use B nonempty balanced batches, paired graph seeds, ten independent baseline draws.",
                "theory": "Keep exact oracle, finite signal separation, and sampler logic. Small palettes/coloring counts "
                          "are empirical overrides, not the original uniform success guarantee.",
                "reused_sources_sha256": provenance,
                "design_observation": str(args.design_observation.resolve()) if args.design_observation else None,
                "design_observation_sha256": digest(args.design_observation) if args.design_observation else None,
                "source_sha256": {name: digest(Path(__file__).with_name(name)) for name in SOURCES}}
    freeze_json(args.output / "protocol.json", protocol)
    jobs = [("proposal", target, p, m, d, repeat) for target, p, m, d in settings for repeat in range(REPEATS)]
    proposals = (execute(jobs, args.output / "proposal_runs.jsonl", args.workers, old) if args.stage != "baseline"
                 else read_runs(args.output / "proposal_runs.jsonl"))
    assert {tuple(r["job"]) for r in proposals} == set(jobs)
    summary = summarize(proposals)
    freeze_json(args.output / "summary.json", summary)
    matches = match_budgets(summary)
    freeze_json(args.output / "matched_budgets.json", matches)
    if args.stage == "proposal":
        return
    baseline_jobs = sorted({("baseline", item["target"], 0, item["baseline_batches"], 0, repeat)
                            for item in matches for repeat in range(REPEATS)})
    baselines = execute(baseline_jobs, args.output / "baseline_runs.jsonl", args.workers)
    freeze_json(args.output / "comparisons.json", comparisons(proposals, baselines, matches))
    print(f"Finished {summary['settings']} settings: {len(summary['complete_settings'])} complete, "
          f"{len(summary['censored_settings'])} in the separate censoring table.", flush=True)


if __name__ == "__main__":
    main()
