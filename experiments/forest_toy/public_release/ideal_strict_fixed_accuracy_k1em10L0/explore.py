"""Explore the agreed small-N palette/coloring grid with passive diagnostics."""

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict, dataclass
import hashlib
import json
from math import comb
from pathlib import Path
import platform
from time import perf_counter

import numpy as np

from toy import Parameters, audit, make_forest, sample
from tradeoff import NUMERICAL_FLOOR, aggregate as risk_summary, seeds_for, write_json
from tradeoff_core import CommitCursor, DensityRecorder
from tune import BETA, TARGETS, RunObserver


GRID = {4: (9, 15, 17, 33, 49), 8: (5, 7, 9, 17, 33), 16: (3, 5, 7, 11, 21)}
SOURCES = ("toy.py", "tune.py", "tradeoff_core.py", "tradeoff.py", "explore.py")


@dataclass(frozen=True)
class FixedColorings(Parameters):
    """Use an exact odd M without changing the existing sampler or defaults."""

    coloring_count: int = 1

    def __post_init__(self):
        super().__post_init__()
        if (not isinstance(self.coloring_count, int) or self.coloring_count < 1
                or self.coloring_count % 2 != 1 or self.coloring_coefficient is not None):
            raise ValueError("Please specify a positive odd M and no logarithmic coefficient.")

    @property
    def colorings(self):
        return self.coloring_count


class ExplorationObserver(RunObserver):
    """Observe public candidate counts, without access to the hidden forest."""

    def start_screen(self, history, draft, columns):
        super().start_screen(history, draft, columns)
        self._residual = np.flatnonzero(history < 0).tolist()
        self._raw_counts = None
        self.current["index"] = len(self.screens)

    def observe_prefix(self, completed, total, votes):
        if completed != total:
            return
        # Please inspect only the final vote counts. Counting bits does not
        # modify the decoder, consume randomness, or add oracle submissions.
        counts = np.array([bin(votes.majority_mask(j)).count("1") for j in self._residual])
        self._raw_counts = dict(zip(self._residual, counts.tolist()))
        histogram = Counter(counts.tolist())
        self.current.update({
            "raw_degree_histogram": {str(k): v for k, v in sorted(histogram.items())},
            "raw_candidates": int(counts.sum()), "raw_degree_mean": float(counts.mean()),
            "raw_degree_median": float(np.median(counts)),
            "raw_degree_p90": float(np.quantile(counts, 0.9)),
            "raw_degree_max": int(counts.max()), "raw_empty_rows": int((counts == 0).sum()),
            "truncated_rows": int((counts > self.params.d).sum()),
            "truncation_fraction": float((counts > self.params.d).mean()),
        })

    def finish_screen(self, rows):
        super().finish_screen(rows)
        if self._raw_counts is None or set(rows) != set(self._raw_counts):
            raise AssertionError("The final candidate snapshot is incomplete.")
        for j, neighbors in rows.items():
            count = self._raw_counts[j]
            expected = count if count <= self.params.d else 0
            if len(neighbors) != expected:
                raise AssertionError("Candidate diagnostics disagree with degree truncation.")
        assert self.current["empty_decoded_rows"] == (self.current["raw_empty_rows"]
                                                       + self.current["truncated_rows"])

    def observe_controller(self, peel, claims, phase):
        super().observe_controller(peel, claims, phase)
        values = claims[self._residual]
        self.current.update({
            "incoming_claims_mean": float(values.mean()),
            "incoming_claims_p90": float(np.quantile(values, 0.9)),
            "incoming_claims_histogram": {str(k): v for k, v in sorted(Counter(values.tolist()).items())},
            "next_action": "terminal" if not peel or phase == self.params.peel_cap else "peel",
        })


def add_posthoc_diagnostics(observer, oracle, result):
    """Please use hidden edges only after all sampling decisions have finished."""
    adjacency = [set() for _ in range(oracle.n)]
    for leaf in np.flatnonzero(oracle.leaf):
        root = int(oracle.root_of[leaf])
        adjacency[int(leaf)].add(root)
        adjacency[root].add(int(leaf))
    for index, (saved, screen, cost) in enumerate(zip(observer.screens, result["screens"], result["screen_costs"])):
        residual = set(screen["rows"])
        truth = {j: adjacency[j] & residual for j in residual}
        peeled = set(screen["peel"])
        saved.update({
            **cost,
            "posthoc_true_edges": sum(map(len, truth.values())) // 2,
            "posthoc_low_degree_row_errors": sum(screen["rows"][j] != neighbors
                                                   for j, neighbors in truth.items() if len(neighbors) <= observer.params.d),
            "posthoc_peel_degree_le_half_d": sum(len(truth[j]) <= observer.params.d / 2 for j in peeled),
            "posthoc_peel_degree_gt_half_d": sum(len(truth[j]) > observer.params.d / 2 for j in peeled),
            "posthoc_unpeeled_degree_gt_d": sum(len(neighbors) > observer.params.d and j not in peeled
                                                  for j, neighbors in truth.items()),
            "residual_reduction_to_next": (len(residual) - len(result["screens"][index+1]["rows"])
                                            if index+1 < len(result["screens"]) else None),
        })


def matching_expectation(n, p, m):
    """Exact first-screen expectations for matching; not a formula for stars."""
    def majority_probability(probability):
        return sum(comb(m, k) * probability**k * (1-probability)**(m-k)
                   for k in range(m//2 + 1, m+1))
    false = (n-2) * majority_probability((p-1) / p**2)
    true = majority_probability(1 - 1/p)
    return {"false_candidates_per_row": false, "true_candidate_per_row": true,
            "raw_candidates_per_row": false + true}


def run_one(job):
    np.seterr(divide="raise", over="raise", invalid="raise")
    _, target, n, p, m, repeat, master = job
    seeds = seeds_for(master, n, target, repeat, "proposal")
    config = TARGETS[target]
    oracle = make_forest(n, config["family"], seeds[0], coupling=config["coupling"], reuse_queries=True)
    params = FixedColorings(n, oracle.theta, beta=BETA, palette_override=p, coloring_count=m)
    observer, recorder = ExplorationObserver(params), DensityRecorder(n)
    started = perf_counter()
    result = sample(oracle, params, seeds[1], seeds[2], observer=observer,
                    commit_session=CommitCursor(oracle), commit_observer=recorder)
    sample_seconds = perf_counter() - started
    score = recorder.finish(oracle, result["sample"])
    checked = audit(oracle, params, result)
    add_posthoc_diagnostics(observer, oracle, result)
    elapsed = perf_counter() - started
    success = (checked["all_tokens_committed"] and checked["fallback"] is None
               and checked["unsafe_batches"] == 0 and checked["low_degree_row_errors"] == 0
               and checked["terminal_row_errors"] == 0)
    return {"job": list(job), "kind": "proposal", "phase": "exploration", "target": target,
            "n": n, "palette": p, "colorings": m, "repeat": repeat, "seeds": seeds,
            "parameters": asdict(params), "theta": oracle.theta, "vocab": oracle.vocab,
            "separation_lhs_over_signal": (4*params.eps + params.tail_tolerance) / params.signal,
            "screen_calls": len(result["screens"]), "screen_cap": params.screen_cap,
            "screen_cap_reached": len(result["screens"]) == params.screen_cap,
            "screen_observations": observer.screens,
            "depth": 1 + len(result["screens"]) + oracle.cost.rounds,
            "batch_size_histogram": {str(k): v for k, v in sorted(Counter(map(len, result["batches"])).items())},
            "sample_sha256": hashlib.sha256(result["sample"].astype("<i4").tobytes()).hexdigest(),
            "sample_seconds": sample_seconds, "posthoc_seconds": elapsed-sample_seconds,
            "seconds": elapsed, "structural_success": success,
            **score, **checked, **asdict(oracle.cost), "total": oracle.cost.total}


def summarize(records):
    results = []
    for target in TARGETS:
        for p, colorings in GRID.items():
            for m in colorings:
                rows = sorted([r for r in records if (r["target"], r["palette"], r["colorings"]) == (target, p, m)],
                              key=lambda r: r["repeat"])
                if not rows:
                    raise ValueError("Please finish the complete exploratory grid before summarizing.")
                combined = risk_summary(rows)
                for metric in ("total", "counterfactual", "rounds", "depth", "screen_calls", "seconds"):
                    combined[metric+"_median"] = float(np.median([r[metric] for r in rows]))
                    combined[metric+"_p90"] = float(np.quantile([r[metric] for r in rows], 0.9))
                for metric in ("raw_degree_mean", "truncation_fraction", "peel_size", "incoming_claims_mean",
                               "posthoc_peel_degree_le_half_d", "posthoc_unpeeled_degree_gt_d"):
                    combined["first_"+metric] = float(np.mean([r["screen_observations"][0][metric] for r in rows]))
                combined["screen_cap_runs"] = sum(r["screen_cap_reached"] for r in rows)
                combined["fallback_reasons"] = dict(Counter(r["fallback"] or "none" for r in rows))
                combined["pooled_truncation_fraction"] = (sum(s["truncated_rows"] for r in rows for s in r["screen_observations"])
                    / sum(s["residual_n"] for r in rows for s in r["screen_observations"]))
                results.append({"target": target, "palette": p, "colorings": m, **combined,
                                "matching_first_screen_prediction": matching_expectation(rows[0]["n"], p, m)
                                if target == "matching" else None})
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=4096)
    parser.add_argument("--repeats", type=int, default=10)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--seed", type=int, default=2026090803)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results") / "exploration")
    args = parser.parse_args()
    if args.repeats < 1 or args.workers < 1:
        raise ValueError("Please use positive repeat and worker counts.")
    args.output.mkdir(parents=True, exist_ok=True)
    protocol = {"version": 1, "phase": "exploration", "n": args.n, "repeats": args.repeats,
                "master_seed": args.seed, "grid": GRID, "targets": TARGETS, "d": 9, "chunks": 1,
                "beta": BETA, "vocab": 2048, "main_cost": "mean total Q_cf + R + 1",
                "supplementary_cost": ["median", "p90 (linear empirical quantile)", "sequential depth"],
                "seed_design": "Pair graph/controller/commit seeds across settings; the two star couplings share seeds. "
                               "This master seed is separate from earlier experiments and future confirmation.",
                "risk": "E_{graph,controller} TV(P_graph,Q_graph,controller), estimated by realized density scores.",
                "selection": "Retain all settings and all seeds. This first pass locates regimes; no 100-seed confirmation yet.",
                "baseline": "Small-N mechanism exploration only; matched-budget baselines are evaluated in the large-N study.",
                "observer": "Public counts before truncation and incoming claims; hidden-graph diagnostics only after sampling.",
                "source_sha256": {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() for name in SOURCES}}
    protocol = json.loads(json.dumps(protocol))
    protocol_path = args.output / "protocol.json"
    if protocol_path.exists() and json.loads(protocol_path.read_text()) != protocol:
        raise ValueError("The protocol or source changed. Please choose a new output directory.")
    write_json(protocol_path, protocol)
    jobs = [("exploration", target, args.n, p, m, repeat, args.seed)
            for p, values in GRID.items() for m in values for target in TARGETS for repeat in range(args.repeats)]
    path = args.output / "runs.jsonl"
    records = [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []
    done = {tuple(row["job"]) for row in records}
    if len(done) != len(records) or not done <= set(jobs):
        raise ValueError("Saved runs do not match the agreed grid.")
    started = perf_counter()
    with ProcessPoolExecutor(max_workers=args.workers) as pool, path.open("a") as stream:
        futures = {pool.submit(run_one, job): job for job in jobs if job not in done}
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
            if len(records) % 10 == 0 or len(records) == len(jobs):
                print(f"{len(records)}/{len(jobs)} {row['target']} p={row['palette']} M={row['colorings']} "
                      f"Q={row['total']} screens={row['screen_calls']} TVscore={row['tv_score']:.5g} "
                      f"elapsed={perf_counter()-started:.1f}s", flush=True)
    write_json(args.output / "execution.json", {"workers": args.workers, "this_invocation_seconds": perf_counter()-started,
               "python": platform.python_version(), "numpy": np.__version__})
    write_json(args.output / "summary.json", {"runs": len(records), "results": summarize(records)})
    print("Completed the exploratory grid, including every failed run.", flush=True)


if __name__ == "__main__":
    main()
