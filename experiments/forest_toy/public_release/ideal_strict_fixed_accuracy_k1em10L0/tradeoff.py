"""Measure seed-average TV against balanced random sampling at matched mean cost."""

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict
import hashlib
import json
from math import ceil, comb, log, sqrt
from pathlib import Path
import platform
from time import perf_counter

import numpy as np

from toy import Parameters, audit, make_forest, sample
from tradeoff_core import CommitCursor, DensityRecorder, random_batch_sample, schedule_audit
from tune import BETA, TARGETS, RunObserver


COEFFICIENTS = (0.5, 1, 2, 3, 4, 6)
NUMERICAL_FLOOR = 1e-10


def seeds_for(master, n, target, repeat, kind, budget=0):
    family = int(TARGETS[target]["family"] == "stars")
    graph = int(np.random.SeedSequence([master, 0, family, n, repeat]).generate_state(1)[0])
    source = [master, 1 if kind == "proposal" else 2, family, n, repeat]
    if kind != "proposal":
        source.append(budget)
    other = np.random.SeedSequence(source).generate_state(2).tolist()
    return [graph, *other]


def run_one(job):
    np.seterr(divide="raise", over="raise", invalid="raise")
    kind, target, n, setting, repeat, master = job
    seeds = seeds_for(master, n, target, repeat, kind, setting)
    target_config = TARGETS[target]
    oracle = make_forest(n, target_config["family"], seeds[0], coupling=target_config["coupling"],
                         reuse_queries=kind == "proposal")
    started = perf_counter()
    if kind == "proposal":
        params = Parameters(n, oracle.theta, beta=BETA, palette_override=8, coloring_coefficient=setting)
        observer, recorder = RunObserver(params), DensityRecorder(n)
        result = sample(oracle, params, seeds[1], seeds[2], observer=observer,
                        commit_session=CommitCursor(oracle), commit_observer=recorder)
        score = recorder.finish(oracle, result["sample"])
        checked = audit(oracle, params, result)
        auxiliary = {"coefficient": setting, "colorings": params.colorings, "parameters": asdict(params),
                     "screen_calls": len(result["screens"]), "screen_observations": observer.screens,
                     "screen_costs": result["screen_costs"], "peel_sizes": [len(s["peel"]) for s in result["screens"]],
                     "depth": 1 + len(result["screens"]) + oracle.cost.rounds,
                     "structural_success": (checked["all_tokens_committed"] and checked["fallback"] is None
                                            and checked["unsafe_batches"] == 0 and checked["low_degree_row_errors"] == 0
                                            and checked["terminal_row_errors"] == 0), **checked}
    else:
        result = random_batch_sample(oracle, setting, seeds[1], seeds[2])
        score = {key: value for key, value in result.items() if key not in ("sample", "batches")}
        auxiliary = {"budget": setting, "depth": setting, "screen_calls": 0,
                     **schedule_audit(oracle, result["batches"])}
        if oracle.cost.total != setting:
            raise AssertionError("The balanced baseline did not use exactly its allotted nonempty batches.")
    elapsed = perf_counter() - started
    sizes = Counter(map(len, result["batches"]))
    return {"job": list(job), "kind": kind, "target": target, "n": n, "repeat": repeat, "seeds": seeds,
            "theta": oracle.theta, "vocab": oracle.vocab, **score, **asdict(oracle.cost), "total": oracle.cost.total,
            "seconds": elapsed, "batch_size_histogram": {str(k): v for k, v in sorted(sizes.items())},
            "sample_sha256": hashlib.sha256(result["sample"].astype("<i4").tobytes()).hexdigest(), **auxiliary}


def execute(jobs, path, workers):
    records = [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []
    wanted = {tuple(job) for job in jobs}
    done = {tuple(r["job"]) for r in records}
    if len(done) != len(records) or not done <= wanted:
        raise ValueError("Please use a separate output directory for a different set of jobs.")
    started = perf_counter()
    with ProcessPoolExecutor(max_workers=workers) as pool, path.open("a") as stream:
        futures = {pool.submit(run_one, job): job for job in jobs if tuple(job) not in done}
        for future in as_completed(futures):
            try:
                record = future.result()
            except BaseException:
                for pending in futures:
                    pending.cancel()
                raise
            records.append(record)
            stream.write(json.dumps(record, separators=(",", ":")) + "\n")
            stream.flush()
            if len(records) % 20 == 0 or len(records) == len(jobs):
                print(f"{path.stem}: {len(records)}/{len(jobs)}; {record['target']} setting={record['job'][3]} "
                      f"TVscore={record['tv_score']:.5g} Q={record['total']} depth={record['depth']} "
                      f"elapsed={perf_counter()-started:.1f}s", flush=True)
    return sorted(records, key=lambda r: r["job"]), perf_counter() - started


def bernoulli_upper(successes, count, alpha=0.05):
    """One-sided exact bound on the probability of a score exceeding a threshold."""
    if successes == count:
        return 1.0
    low, high = successes / count, 1.0
    for _ in range(65):
        p = (low + high) / 2
        cdf = sum(comb(count, k) * p ** k * (1 - p) ** (count - k) for k in range(successes + 1))
        if cdf > alpha:
            low = p
        else:
            high = p
    return (low + high) / 2


def aggregate(records):
    count = len(records)
    scores = np.array([r["tv_score"] for r in records])
    significant = int((scores > NUMERICAL_FLOOR).sum())
    estimate = float(scores.mean())
    # Please report uncertainty even when all observed scores are numerical zero.
    # E[score] <= P[score > floor] + floor supplies a conservative rare-event bound.
    event_bound = min(1, bernoulli_upper(significant, count) + NUMERICAL_FLOOR)
    hoeffding_bound = min(1, estimate + sqrt(log(1 / 0.05) / (2 * count)))
    result = {"runs": count, "tv_mean": estimate,
              "tv_se": float(scores.std(ddof=1) / sqrt(count)) if count > 1 else None,
              "tv_positive_above_floor": significant, "tv_min": float(scores.min()), "tv_max": float(scores.max()),
              "tv_event_upper_95": event_bound, "tv_hoeffding_upper_95": hoeffding_bound,
              "safe_schedule_runs": sum(r["unsafe_batches"] == 0 for r in records),
              "fallback_runs": sum(r.get("fallback") is not None for r in records),
              "structural_successes": (sum(r["structural_success"] for r in records)
                                       if records[0]["kind"] == "proposal" else None)}
    for metric in ("total", "counterfactual", "nominal_counterfactual", "rounds", "depth", "returned_rows",
                   "screen_calls", "seconds", "log_q_over_p"):
        values = np.array([r[metric] for r in records])
        result[metric] = float(values.mean())
        result[metric + "_min"], result[metric + "_max"] = float(values.min()), float(values.max())
        result[metric + "_se"] = float(values.std(ddof=1) / sqrt(count)) if count > 1 else None
    return result


def match_budgets(proposals, n):
    matches = []
    for target in TARGETS:
        for coefficient in COEFFICIENTS:
            rows = [r for r in proposals if r["target"] == target and r["coefficient"] == coefficient]
            for axis in ("total", "depth"):
                mean = float(np.mean([r[axis] for r in rows]))
                rounded = int(np.floor(mean + 0.5))
                matches.append({"target": target, "coefficient": coefficient, "colorings": rows[0]["colorings"],
                                "axis": axis, "proposal_mean": mean, "rounded_budget": rounded,
                                "baseline_batches": min(n, rounded), "capped_at_exact_singletons": rounded > n,
                                "rounding_error": rounded - mean})
    return matches


def summarize(proposals, baselines, matches):
    results = []
    for match in matches:
        a = sorted([r for r in proposals if r["target"] == match["target"]
                    and r["coefficient"] == match["coefficient"]], key=lambda r: r["repeat"])
        b = sorted([r for r in baselines if r["target"] == match["target"]
                    and r["budget"] == match["baseline_batches"]], key=lambda r: r["repeat"])
        if [r["repeat"] for r in a] != [r["repeat"] for r in b]:
            raise ValueError("Please complete both methods on the same target-label repeats.")
        assert all(x["seeds"][0] == y["seeds"][0] for x, y in zip(a, b))
        difference = np.array([y["tv_score"] - x["tv_score"] for x, y in zip(a, b)])
        results.append({**match, "proposal": aggregate(a), "baseline": aggregate(b),
                        "baseline_minus_proposal_tv": float(difference.mean()),
                        "paired_difference_se": float(difference.std(ddof=1) / sqrt(len(a))) if len(a) > 1 else None})
    return results


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=("all", "proposal", "baseline"), default="all")
    parser.add_argument("--n", type=int, default=16384)
    parser.add_argument("--repeats", type=int, default=100)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--seed", type=int, default=2026090802)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results") / "tradeoff")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    protocol = {"version": 1, "n": args.n, "repeats": args.repeats, "seed": args.seed, "targets": TARGETS,
                "coefficients": COEFFICIENTS, "palette": 8, "beta": BETA, "d": 9, "chunks": 1,
                "main_axis": "total", "secondary_axis": "depth",
                "risk": "E_{graph,controller} TV(P_graph,Q_graph,controller); commit randomness is not conditioned on.",
                "estimator": "For X drawn by Q_w, score=max(0,1-exp(-log(Q_w(X)/P(X)))); retain all runs.",
                "matching": "Fixed B=floor(mean_cost+0.5), capped at N; balanced sizes differ by at most one. "
                            "The first N%B batches get one extra token; random permutation, independent baseline draws.",
                "baseline_reuse": "The same (target,B,repeat) baseline is reused across settings/axes with identical B.",
                "numerical_floor_for_display_and_event_counts": NUMERICAL_FLOOR,
                "uncertainty": "Show sample SE and separate conservative one-sided 95% upper bounds. "
                               "A zero observed score is not proof of exactness.",
                "source_sha256": {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                  for name in ("toy.py", "tradeoff_core.py", "tradeoff.py", "tune.py")}}
    protocol = json.loads(json.dumps(protocol))
    path = args.output / "protocol.json"
    if path.exists() and json.loads(path.read_text()) != protocol:
        raise ValueError("The protocol or source changed. Please use a new output directory.")
    write_json(path, protocol)
    proposal_path = args.output / "proposal_runs.jsonl"
    if args.stage in ("all", "proposal"):
        jobs = [("proposal", target, args.n, coefficient, repeat, args.seed)
                for coefficient in COEFFICIENTS for target in TARGETS for repeat in range(args.repeats)]
        proposals, elapsed = execute(jobs, proposal_path, args.workers)
        write_json(args.output / "proposal_execution.json", {"workers": args.workers, "this_invocation_seconds": elapsed})
    else:
        proposals = [json.loads(line) for line in proposal_path.read_text().splitlines()]
    if len(proposals) != len(TARGETS) * len(COEFFICIENTS) * args.repeats:
        raise ValueError("Please finish all proposal runs before fixing baseline budgets.")
    matches = match_budgets(proposals, args.n)
    budget_path = args.output / "matched_budgets.json"
    if budget_path.exists() and json.loads(budget_path.read_text()) != matches:
        raise ValueError("Previously fixed baseline budgets do not match the proposal records.")
    write_json(budget_path, matches)
    if args.stage in ("all", "baseline"):
        distinct = sorted({(r["target"], r["baseline_batches"]) for r in matches})
        jobs = [("baseline", target, args.n, budget, repeat, args.seed)
                for target, budget in distinct for repeat in range(args.repeats)]
        baselines, elapsed = execute(jobs, args.output / "baseline_runs.jsonl", args.workers)
        write_json(args.output / "baseline_execution.json", {"workers": args.workers, "this_invocation_seconds": elapsed})
        write_json(args.output / "summary.json", {"results": summarize(proposals, baselines, matches),
                   "proposal_runs": len(proposals), "baseline_runs": len(baselines), "workers": args.workers,
                   "python": platform.python_version(), "numpy": np.__version__})
        print("Finished all proposal and matched-budget baseline runs.", flush=True)


if __name__ == "__main__":
    main()
