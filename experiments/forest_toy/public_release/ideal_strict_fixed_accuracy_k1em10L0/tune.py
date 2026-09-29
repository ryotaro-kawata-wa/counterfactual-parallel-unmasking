"""Freeze a small empirical calibration, then evaluate disjoint held-out seeds.

Please retain every completed run, including structural failures and fallbacks.
The primary success event is the conjunction of all post-run structural checks.
"""

import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict
import hashlib
import json
from math import ceil, log, log1p, sqrt
from pathlib import Path
import platform
from time import perf_counter

import numpy as np

from toy import Parameters, audit, make_forest, sample


TARGETS = {
    "matching": {"family": "matching", "coupling": 0.5},
    "stars_easy": {"family": "stars", "coupling": 0.125},
    "stars_original": {"family": "stars", "coupling": 0.5},
}
PRIMARY = ("matching", "stars_easy")
BETA = 0.0009375


class RunObserver:
    """Collect inexpensive observables without access to the hidden forest."""

    def __init__(self, params):
        self.params = params
        self.screens = []

    def start_screen(self, history, draft, columns):
        self.current = {"residual_n": int((history < 0).sum()), "row_source_tests": 0,
                        "positive_row_source_tests": 0, "chunk_source_groups": 0,
                        "responding_chunk_source_groups": 0, "min_positive_diameter": None}
        self.screens.append(self.current)

    def observe_coloring(self, groups, draft, columns):
        pass

    def observe_chunk(self, chunk, sources, diameter):
        positive = diameter > 2 * self.params.eps
        self.current["row_source_tests"] += positive.size
        self.current["positive_row_source_tests"] += int(positive.sum())
        self.current["chunk_source_groups"] += len(sources)
        self.current["responding_chunk_source_groups"] += int(positive.any(axis=0).sum())
        if positive.any():
            minimum = float(diameter[positive].min())
            old = self.current["min_positive_diameter"]
            self.current["min_positive_diameter"] = minimum if old is None else min(old, minimum)

    def observe_prefix(self, completed, total, votes):
        pass

    def finish_screen(self, rows):
        self.current["empty_decoded_rows"] = sum(not neighbors for neighbors in rows.values())
        self.current["claims_after_truncation"] = sum(map(len, rows.values()))

    def observe_controller(self, peel, claims, phase):
        self.current["peel_size"] = len(peel)
        self.current["max_incoming_claims"] = int(claims.max())


def run_one(job):
    stage, target, n, p, coefficient, repeat, master = job
    target_config = TARGETS[target]
    # Please pair the two star targets and all tuning candidates, while keeping
    # calibration and evaluation in different seed domains.
    seeds = np.random.SeedSequence([master, stage, int(target_config["family"] == "stars"),
                                    n, repeat]).generate_state(3).tolist()
    oracle = make_forest(n, target_config["family"], seeds[0], coupling=target_config["coupling"],
                         reuse_queries=True)
    params = Parameters(n, oracle.theta, beta=BETA, palette_override=p,
                        coloring_coefficient=coefficient)
    observer = RunObserver(params)
    started = perf_counter()
    result = sample(oracle, params, seeds[1], seeds[2], observer=observer)
    seconds = perf_counter() - started
    checked = audit(oracle, params, result)
    complete = checked["all_tokens_committed"]
    safe = complete and checked["unsafe_batches"] == 0
    success = (safe and checked["low_degree_row_errors"] == 0
               and checked["terminal_row_errors"] == 0 and checked["fallback"] is None)
    degree = int(np.bincount(oracle.component[oracle.leaf], minlength=len(oracle.roots)).max())
    edges = int(oracle.leaf.sum())
    kl_product = edges * 0.32 * ((1 + params.theta) * log1p(params.theta)
                               + (1 - params.theta) * log1p(-params.theta))
    return {"job": list(job), "stage": "tuning" if stage == 0 else "evaluation", "target": target,
            "n": n, "repeat": repeat, "seeds": seeds, "parameters": asdict(params),
            "palette": p, "coefficient": coefficient, "colorings_per_screen": params.colorings,
            "max_degree": degree, "edges": edges, "bank_size": result["bank_size"],
            "threshold": result["threshold"], "signal": params.signal, "eps": params.eps,
            "separation_lhs_over_signal": (4 * params.eps + params.tail_tolerance) / params.signal,
            "screen_calls": len(result["screens"]), "peel_sizes": [len(s["peel"]) for s in result["screens"]],
            "screen_costs": result["screen_costs"], "screen_observations": observer.screens,
            "commit_batch_sizes": list(map(len, result["batches"])), **asdict(oracle.cost),
            "total": oracle.cost.total, "nominal_total": oracle.cost.nominal_counterfactual + oracle.cost.rounds + 1,
            "seconds": seconds, **checked, "success": bool(success), "safe_schedule": bool(safe),
            "q_cf_below_n": oracle.cost.counterfactual < n, "q_total_below_n": oracle.cost.total < n,
            "product_baseline_kl": kl_product, "product_baseline_tv_upper": min(1, sqrt(kl_product / 2))}


def odd_colorings(n, coefficient):
    count = ceil(coefficient * log(n))
    return count + (count % 2 == 0)


def wilson(successes, count):
    z = 1.959963984540054
    fraction = successes / count
    denominator = 1 + z * z / count
    center = (fraction + z * z / (2 * count)) / denominator
    half = z * sqrt(fraction * (1 - fraction) / count + z * z / (4 * count * count)) / denominator
    return [max(0, center - half), min(1, center + half)]


def aggregate(records):
    count = len(records)
    successes = sum(r["success"] for r in records)
    row = {"runs": count, "successes": successes, "success_fraction": successes / count,
           "success_wilson_95": wilson(successes, count),
           "safe_schedules": sum(r["safe_schedule"] for r in records),
           "q_cf_below_n_runs": sum(r["q_cf_below_n"] for r in records),
           "q_total_below_n_runs": sum(r["q_total_below_n"] for r in records),
           "success_and_q_cf_below_n_runs": sum(r["success"] and r["q_cf_below_n"] for r in records),
           "runs_with_low_degree_errors": sum(r["low_degree_row_errors"] > 0 for r in records),
           "runs_with_terminal_errors": sum(r["terminal_row_errors"] > 0 for r in records),
           "runs_with_unsafe_batches": sum(r["unsafe_batches"] > 0 for r in records),
           "fallback_runs": sum(r["fallback"] is not None for r in records)}
    for metric in ("counterfactual", "nominal_counterfactual", "total", "rounds", "returned_rows",
                   "nominal_returned_rows", "screen_calls", "seconds", "low_degree_row_errors",
                   "terminal_row_errors", "unsafe_batches"):
        values = [r[metric] for r in records]
        row[metric] = float(np.mean(values))
        row[metric + "_min"] = min(values)
        row[metric + "_max"] = max(values)
    return row


def execute(jobs, path, workers):
    records = [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []
    wanted = {tuple(job) for job in jobs}
    if any(tuple(r["job"]) not in wanted for r in records):
        raise ValueError("The output contains a different experiment. Please use a separate directory.")
    done = {tuple(r["job"]) for r in records}
    if len(done) != len(records):
        raise ValueError("Duplicate completed jobs in the output.")
    remaining = [job for job in jobs if tuple(job) not in done]
    started = perf_counter()
    with ProcessPoolExecutor(max_workers=workers) as pool, path.open("a") as stream:
        futures = {pool.submit(run_one, job): job for job in remaining}
        for future in as_completed(futures):
            record = future.result()
            records.append(record)
            stream.write(json.dumps(record, separators=(",", ":")) + "\n")
            stream.flush()
            if len(records) % 8 == 0 or len(records) == len(jobs):
                print(f"{path.stem}: {len(records)}/{len(jobs)} complete; "
                      f"last={record['target']} N={record['n']} p={record['palette']} a={record['coefficient']} "
                      f"success={record['success']} Q_cf={record['counterfactual']} "
                      f"elapsed={perf_counter() - started:.1f}s", flush=True)
    return sorted(records, key=lambda r: r["job"])


def select(records, candidates, repeats, goal_n):
    rows = []
    for candidate in candidates:
        if not candidate["budget_eligible"]:
            rows.append({**candidate, "status": "excluded_by_two_screen_budget"})
            continue
        p, coefficient = candidate["palette"], candidate["coefficient"]
        matching = [r for r in records if r["palette"] == p and r["coefficient"] == coefficient]
        results = {target: aggregate([r for r in matching if r["target"] == target]) for target in PRIMARY}
        if any(r["runs"] != repeats for r in results.values()):
            raise ValueError("Please finish all tuning seeds before choosing settings.")
        rows.append({**candidate, "status": "evaluated", "results": results,
                     "observed_budget_eligible": all(r["counterfactual_max"] < goal_n for r in results.values()),
                     "minimum_successes": min(r["successes"] for r in results.values()),
                     "total_successes": sum(r["successes"] for r in results.values()),
                     "worst_mean_q_cf": max(r["counterfactual"] for r in results.values())})
    eligible = [r for r in rows if r.get("observed_budget_eligible")]
    if not eligible:
        raise RuntimeError("No calibration candidate met the observed query budget; no evaluation was selected.")
    chosen = min(eligible, key=lambda r: (-r["minimum_successes"], -r["total_successes"],
                                        r["worst_mean_q_cf"], r["palette"], r["coefficient"]))
    return {"palette": chosen["palette"], "coefficient": chosen["coefficient"], "beta": BETA,
            "chosen_from_tuning_only": True, "candidates": rows}


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=("all", "tune", "evaluate"), default="all")
    parser.add_argument("--sizes", nargs="+", type=int, default=[256, 1024, 4096, 16384])
    parser.add_argument("--goal-n", type=int, default=16384)
    parser.add_argument("--tuning-repeats", type=int, default=8)
    parser.add_argument("--repeats", type=int, default=100)
    parser.add_argument("--workers", type=int, default=3)
    parser.add_argument("--seed", type=int, default=2026090801)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results") / "tuned")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    candidates = [{"palette": p, "coefficient": a, "colorings_at_goal": odd_colorings(args.goal_n, a),
                   "two_screen_budget": 2 * odd_colorings(args.goal_n, a) * p * (2 * p - 1),
                   "budget_eligible": 2 * odd_colorings(args.goal_n, a) * p * (2 * p - 1) < args.goal_n}
                  for p in (4, 8, 12) for a in (2, 4, 6)]
    protocol = {"version": 1, "seed": args.seed, "sizes": args.sizes, "goal_n": args.goal_n,
                "tuning_repeats_per_target_candidate": args.tuning_repeats,
                "evaluation_repeats_per_target_size": args.repeats, "targets": TARGETS,
                "primary_targets": PRIMARY, "beta": BETA, "degree_cutoff": 9, "chunks": 1,
                "candidates": candidates,
                "selection": "Exclude two-screen full-occupancy budget >= goal N, then any observed tuning "
                             "Q_cf >= N. Maximize the minimum primary-target success count, then their sum, "
                             "then minimize worst-target mean Q_cf; final ties use (p,a).",
                "success": "All tokens committed, no unsafe true-component batch, no low-degree row error, "
                           "no terminal row error, and no fallback. Safe schedules also reported separately.",
                "query_reuse": "Exact public input identity within each fixed chunk and coloring; replies "
                               "are evaluated once and reused for all nominal requests. No global cache.",
                "source_sha256": {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                  for name in ("toy.py", "tune.py")}}
    protocol = json.loads(json.dumps(protocol))
    protocol_path = args.output / "protocol.json"
    if protocol_path.exists() and json.loads(protocol_path.read_text()) != protocol:
        raise ValueError("The frozen protocol or source has changed. Please use a new output directory.")
    write_json(protocol_path, protocol)
    tuning_jobs = [(0, target, args.goal_n, c["palette"], c["coefficient"], repeat, args.seed)
                   for c in candidates if c["budget_eligible"] for target in PRIMARY
                   for repeat in range(args.tuning_repeats)]
    if args.stage in ("all", "tune"):
        records = execute(tuning_jobs, args.output / "tuning_runs.jsonl", args.workers)
        selection = select(records, candidates, args.tuning_repeats, args.goal_n)
        selection_path = args.output / "selection.json"
        if selection_path.exists() and json.loads(selection_path.read_text()) != selection:
            raise ValueError("The existing frozen selection does not match calibration.")
        write_json(selection_path, selection)
        print(f"Frozen selection: p={selection['palette']}, a={selection['coefficient']}, beta={BETA}", flush=True)
    if args.stage in ("all", "evaluate"):
        selection = json.loads((args.output / "selection.json").read_text())
        jobs = [(1, target, n, selection["palette"], selection["coefficient"], repeat, args.seed)
                for target in TARGETS for n in args.sizes for repeat in range(args.repeats)]
        records = execute(jobs, args.output / "evaluation_runs.jsonl", args.workers)
        results = {}
        for target in TARGETS:
            points = [{"n": n, **aggregate([r for r in records if r["target"] == target and r["n"] == n])}
                      for n in args.sizes]
            slopes = ({metric: float(np.polyfit(np.log(args.sizes), np.log([r[metric] for r in points]), 1)[0])
                       for metric in ("counterfactual", "total", "returned_rows")}
                      if len(args.sizes) > 1 else {})
            results[target] = {"points": points, "log_log_slopes": slopes}
        write_json(args.output / "summary.json", {"selection": selection, "results": results,
                   "python": platform.python_version(), "numpy": np.__version__, "workers": args.workers})
        print("Held-out evaluation complete; every seed is retained.", flush=True)


if __name__ == "__main__":
    main()
