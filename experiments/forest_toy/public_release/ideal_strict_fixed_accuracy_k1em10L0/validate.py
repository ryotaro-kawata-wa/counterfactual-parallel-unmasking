"""Refine the small-N grid, freeze candidates, and confirm on independent seeds."""

import argparse
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import platform
from time import perf_counter

import numpy as np

from explore import GRID, SOURCES as EXPLORATION_SOURCES, matching_expectation, run_one as proposal_run
from tradeoff import NUMERICAL_FLOOR, aggregate, run_one as baseline_run, write_json
from tune import BETA, TARGETS


REFINEMENT = {"matching": {4: (57, 65, 73)},
              "stars_easy": {8: (11, 13, 15)},
              "stars_original": {8: (11, 13, 15, 21, 25)}}
N = 4096
EXPLORE_SEED, CONFIRM_SEED = 2026090803, 2026090804
EXPLORE_REPEATS, CONFIRM_REPEATS = 10, 10
SOURCES = (*EXPLORATION_SOURCES, "validate.py")
SELECTION_RULE = {
    "low_cost": "Minimum mean total Q among settings with all 10 observed schedules safe and TV mean <= 1e-10.",
    "larger_M": "At the low_cost palette, the smallest explored larger M satisfying the same eligibility rule.",
    "approximate": "Minimum mean total Q among all settings with exploratory TV mean <= 0.05, without a safety filter.",
    "reference": "Always include p=8, M=33 for each target, as the previously observed common reference.",
    "ties": "Order by mean Q, then palette, then M; merge roles selecting the same setting.",
    "confirmation": "Freeze settings using exploration only, then use 10 independent seeds. Retain every failure; do not reselect.",
}


def read_runs(path):
    return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def freeze_json(path, value):
    """Please keep completed artifacts immutable when resuming an experiment."""
    value = json.loads(json.dumps(value))
    if path.exists() and json.loads(path.read_text()) != value:
        raise ValueError(f"The saved protocol differs: {path}. Please use a new output directory.")
    if not path.exists():
        write_json(path, value)


def summarize(records, repeats):
    groups = defaultdict(list)
    for row in records:
        groups[(row["target"], row["palette"], row["colorings"])].append(row)
    results = []
    for (target, p, m), rows in sorted(groups.items()):
        rows.sort(key=lambda r: r["repeat"])
        if len(rows) != repeats or {r["repeat"] for r in rows} != set(range(repeats)):
            raise ValueError("Please retain every seed of a complete setting before selection or aggregation.")
        combined = aggregate(rows)
        for metric in ("total", "counterfactual", "rounds", "depth", "screen_calls", "seconds"):
            combined[metric+"_median"] = float(np.median([r[metric] for r in rows]))
            combined[metric+"_p90"] = float(np.quantile([r[metric] for r in rows], 0.9))
        for metric in ("raw_degree_mean", "truncation_fraction", "peel_size", "incoming_claims_mean",
                       "posthoc_peel_degree_le_half_d", "posthoc_unpeeled_degree_gt_d"):
            combined["first_"+metric] = float(np.mean([r["screen_observations"][0][metric] for r in rows]))
        combined["screen_cap_runs"] = sum(r["screen_cap_reached"] for r in rows)
        combined["fallback_reasons"] = dict(Counter(r["fallback"] or "none" for r in rows))
        combined["posthoc_false_peels"] = float(np.mean([
            sum(s["posthoc_peel_degree_le_half_d"] for s in r["screen_observations"] if s["next_action"] == "peel")
            for r in rows]))
        results.append({"target": target, "palette": p, "colorings": m, **combined,
                        "matching_first_screen_prediction": matching_expectation(rows[0]["n"], p, m)
                        if target == "matching" else None})
    return results


def select_candidates(summary):
    """Use only complete exploratory summaries, never confirmation outcomes."""
    if any(row["runs"] != EXPLORE_REPEATS for row in summary):
        raise ValueError("Candidate selection requires all 10 exploration seeds per setting.")
    selected = {}

    def add(row, role):
        key = (row["target"], row["palette"], row["colorings"])
        if key not in selected:
            selected[key] = {"target": key[0], "palette": key[1], "colorings": key[2], "roles": [],
                             "exploration_mean_Q": row["total"], "exploration_mean_TV": row["tv_mean"],
                             "exploration_safe_runs": row["safe_schedule_runs"]}
        selected[key]["roles"].append(role)

    cost_order = lambda r: (r["total"], r["palette"], r["colorings"])
    for target in TARGETS:
        rows = [r for r in summary if r["target"] == target]
        eligible = [r for r in rows if r["safe_schedule_runs"] == EXPLORE_REPEATS
                    and r["tv_mean"] <= NUMERICAL_FLOOR]
        if not eligible:
            raise ValueError(f"No eligible low-cost candidate for {target}; please report this before revising the protocol.")
        best = min(eligible, key=cost_order)
        add(best, "low_cost")
        higher = [r for r in eligible if r["palette"] == best["palette"] and r["colorings"] > best["colorings"]]
        if higher:
            add(min(higher, key=lambda r: r["colorings"]), "larger_M")
        approximate = [r for r in rows if r["tv_mean"] <= 0.05]
        if approximate:
            add(min(approximate, key=cost_order), "approximate")
        reference = [r for r in rows if (r["palette"], r["colorings"]) == (8, 33)]
        if len(reference) != 1:
            raise ValueError("The common reference is missing or duplicated.")
        add(reference[0], "reference")
    return [selected[key] for key in sorted(selected)]


def run_job(job):
    if job[0] == "baseline":
        row = baseline_run(job)
        row["phase"] = "confirmation_baseline"
    else:
        row = proposal_run(job)
        row["phase"] = job[0]
    return row


def execute(jobs, path, workers):
    records = read_runs(path)
    wanted, done = set(jobs), {tuple(r["job"]) for r in records}
    if len(done) != len(records) or not done <= wanted:
        raise ValueError("Saved runs do not match the frozen jobs.")
    pending_jobs = [job for job in jobs if job not in done]
    if not pending_jobs:
        return sorted(records, key=lambda r: r["job"])
    started = perf_counter()
    with ProcessPoolExecutor(max_workers=workers) as pool, path.open("a") as stream:
        futures = [pool.submit(run_job, job) for job in pending_jobs]
        for future in as_completed(futures):
            try:
                row = future.result()
            except BaseException:
                for pending in futures:
                    pending.cancel()
                raise
            records.append(row)
            stream.write(json.dumps(row, separators=(",", ":")) + "\n")
            stream.flush()
            if len(records) % 25 == 0 or len(records) == len(jobs):
                print(f"{path.stem}: {len(records)}/{len(jobs)} {row['target']} "
                      f"setting={row['job'][3:5]} Q={row['total']} TVscore={row['tv_score']:.5g} "
                      f"elapsed={perf_counter()-started:.1f}s", flush=True)
    execution_path = path.with_name(path.stem+"_execution.json")
    invocations = json.loads(execution_path.read_text()) if execution_path.exists() else []
    invocations.append({"workers": workers, "new_runs": len(pending_jobs), "seconds": perf_counter()-started,
                        "python": platform.python_version(), "numpy": np.__version__})
    write_json(execution_path, invocations)
    return sorted(records, key=lambda r: r["job"])


def matched_budgets(summary, n):
    matches = []
    for row in summary:
        for axis in ("total", "depth"):
            rounded = int(np.floor(row[axis] + 0.5))
            matches.append({"target": row["target"], "palette": row["palette"], "colorings": row["colorings"],
                            "axis": axis, "proposal_mean": row[axis], "rounded_budget": rounded,
                            "baseline_batches": min(n, rounded), "capped_at_exact_singletons": rounded > n,
                            "rounding_error": rounded-row[axis]})
    return matches


def compare_baselines(proposals, baselines, matches):
    comparisons = []
    for match in matches:
        a = sorted([r for r in proposals if (r["target"], r["palette"], r["colorings"])
                    == (match["target"], match["palette"], match["colorings"])], key=lambda r: r["repeat"])
        b = sorted([r for r in baselines if r["target"] == match["target"]
                    and r["budget"] == match["baseline_batches"]], key=lambda r: r["repeat"])
        if len(a) != CONFIRM_REPEATS or len(b) != CONFIRM_REPEATS:
            raise ValueError("Both comparison arms require all 10 seeds.")
        assert all(x["repeat"] == y["repeat"] and x["seeds"][0] == y["seeds"][0] for x, y in zip(a, b))
        delta = np.array([y["tv_score"]-x["tv_score"] for x, y in zip(a, b)])
        comparisons.append({**match, "proposal": aggregate(a), "baseline": aggregate(b),
                            "baseline_minus_proposal_tv": float(delta.mean()),
                            "paired_difference_se": float(delta.std(ddof=1) / np.sqrt(len(a)))})
    return comparisons


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--stage", choices=("all", "refine", "confirm", "baseline"), default="all")
    parser.add_argument("--initial", type=Path, default=Path(__file__).with_name("results") / "exploration")
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results") / "validation")
    args = parser.parse_args()
    if args.workers < 1:
        raise ValueError("Please use a positive worker count.")
    args.output.mkdir(parents=True, exist_ok=True)
    initial_protocol = json.loads((args.initial / "protocol.json").read_text())
    assert initial_protocol["n"] == N and initial_protocol["repeats"] == EXPLORE_REPEATS
    assert initial_protocol["master_seed"] == EXPLORE_SEED
    for name, expected_hash in initial_protocol["source_sha256"].items():
        assert digest(Path(__file__).with_name(name)) == expected_hash
    initial = read_runs(args.initial / "runs.jsonl")
    expected_initial = {(target, p, m, seed) for target in TARGETS for p, values in GRID.items()
                        for m in values for seed in range(EXPLORE_REPEATS)}
    assert len(initial) == len(expected_initial)
    assert {(r["target"], r["palette"], r["colorings"], r["repeat"]) for r in initial} == expected_initial
    protocol = {"version": 1, "n": N, "d": 9, "chunks": 1, "beta": BETA,
                "targets": TARGETS, "refinement": REFINEMENT, "exploration_repeats": EXPLORE_REPEATS,
                "confirmation_repeats": CONFIRM_REPEATS, "exploration_seed": EXPLORE_SEED,
                "confirmation_seed": CONFIRM_SEED, "selection_rule": SELECTION_RULE,
                "seed_policy": "User requested 10 seeds per setting by default for quick PDCA. No 100-seed run in this study.",
                "seed_design": "Refinement shares the original exploration seeds; confirmation uses a separate master. "
                               "Seeds are paired across settings and star couplings within each phase.",
                "risk": "Mean density score estimates E_{graph,controller} TV(P_graph,Q_graph,controller). "
                        "This is not a per-run TV or the TV of the controller-seed mixture.",
                "cost": "Primary: mean Q_total=1+Q_cf+R. Also median and p90; secondary T_seq=1+screens+R.",
                "baseline": "For each confirmed setting and cost axis use B=round-half-up(mean cost), capped at N. "
                            "Random permutation into B balanced nonempty batches; equal B reuses the same baseline. "
                            "Q>N is marked as exact-singleton baseline saturation, not an advantage.",
                "initial_directory": str(args.initial.resolve()),
                "initial_sha256": {name: digest(args.initial / name) for name in ("protocol.json", "runs.jsonl", "summary.json")},
                "source_sha256": {name: digest(Path(__file__).with_name(name)) for name in SOURCES}}
    freeze_json(args.output / "protocol.json", protocol)
    refinement_jobs = [("refinement", target, N, p, m, repeat, EXPLORE_SEED)
                       for target, palettes in REFINEMENT.items() for p, values in palettes.items()
                       for m in values for repeat in range(EXPLORE_REPEATS)]
    refinement_path = args.output / "refinement_runs.jsonl"
    refinement = (execute(refinement_jobs, refinement_path, args.workers) if args.stage in ("all", "refine")
                  else read_runs(refinement_path))
    if {tuple(r["job"]) for r in refinement} != set(refinement_jobs) or len(refinement) != len(refinement_jobs):
        raise ValueError("Please finish all refinement jobs before candidate selection.")
    exploration_summary = summarize(initial+refinement, EXPLORE_REPEATS)
    freeze_json(args.output / "exploration_summary.json", {"runs": len(initial)+len(refinement), "results": exploration_summary})
    selection = {"rule": SELECTION_RULE, "initial_runs_sha256": digest(args.initial / "runs.jsonl"),
                 "refinement_runs_sha256": digest(refinement_path), "candidates": select_candidates(exploration_summary)}
    freeze_json(args.output / "selection.json", selection)
    print("Frozen candidates: " + json.dumps(selection["candidates"]), flush=True)
    if args.stage == "refine":
        return
    confirmation_jobs = [("confirmation", c["target"], N, c["palette"], c["colorings"], repeat, CONFIRM_SEED)
                         for c in selection["candidates"] for repeat in range(CONFIRM_REPEATS)]
    confirmation_path = args.output / "confirmation_runs.jsonl"
    confirmed = (execute(confirmation_jobs, confirmation_path, args.workers) if args.stage in ("all", "confirm")
                 else read_runs(confirmation_path))
    if {tuple(r["job"]) for r in confirmed} != set(confirmation_jobs) or len(confirmed) != len(confirmation_jobs):
        raise ValueError("Please finish all frozen candidates before matching baseline budgets.")
    confirmed_summary = summarize(confirmed, CONFIRM_REPEATS)
    freeze_json(args.output / "confirmation_summary.json", {"runs": len(confirmed), "results": confirmed_summary})
    matches = matched_budgets(confirmed_summary, N)
    freeze_json(args.output / "matched_budgets.json", matches)
    if args.stage == "confirm":
        return
    baseline_jobs = sorted({("baseline", m["target"], N, m["baseline_batches"], repeat, CONFIRM_SEED)
                            for m in matches for repeat in range(CONFIRM_REPEATS)})
    baselines = execute(baseline_jobs, args.output / "baseline_runs.jsonl", args.workers)
    freeze_json(args.output / "comparisons.json", compare_baselines(confirmed, baselines, matches))
    print(f"Completed {len(refinement)} refinement, {len(confirmed)} independent confirmation, "
          f"and {len(baselines)} balanced-baseline runs. Every setting uses 10 seeds.", flush=True)


if __name__ == "__main__":
    main()
