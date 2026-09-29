"""Densify the existing curves and explore standard trees, ten seeds per point."""

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
from time import perf_counter

import numpy as np

from explore import ExplorationObserver, FixedColorings, run_one as legacy_proposal
from toy import sample
from tradeoff import aggregate, run_one as legacy_baseline, write_json
from tree_oracle import (TreeDensityRecorder, load_backend, make_tree,
                         tree_random_batch_sample, tree_schedule_audit)
from tune import BETA
from validate import EXPLORE_SEED, digest, freeze_json, read_runs, summarize


N, REPEATS, TREE_SEED = 4096, 10, 2026090805
TREE_IDS = {"path": 1, "binary": 2, "prufer": 3}
TREE_GRID = {target: {8: (33, 65, 97, 129, 161)} for target in TREE_IDS}
DENSE_GRID = {"matching": {4: (49, 53, 57, 61, 65, 69, 73)},
              "stars_easy": {8: (7, 9, 11, 13, 15, 17, 21, 25, 33)},
              "stars_original": {8: (9, 11, 13, 15, 17, 21, 25, 29, 33)}}
SOURCES = ("toy.py", "tradeoff_core.py", "tradeoff.py", "tune.py", "explore.py", "validate.py",
           "tree_bp.c", "tree_oracle.py", "tree_study.py")


def tree_seeds(target, repeat, kind, budget=0):
    graph = int(np.random.SeedSequence([TREE_SEED, 0, TREE_IDS[target], N, repeat]).generate_state(1)[0])
    source = [TREE_SEED, 1 if kind == "proposal" else 2, TREE_IDS[target], N, repeat]
    if kind != "proposal":
        source.append(budget)
    return [graph, *np.random.SeedSequence(source).generate_state(2).tolist()]


def audit_tree(oracle, params, result, observer):
    """Please inspect hidden edges only after the controller has finished."""
    checked = errors = terminal_errors = 0
    for index, (screen, saved, cost) in enumerate(zip(result["screens"], observer.screens, result["screen_costs"])):
        residual = set(screen["rows"])
        truth = {u: set(oracle.adjacency[u]) & residual for u in residual}
        local_errors = sum(neighbors != screen["rows"][u] for u, neighbors in truth.items() if len(neighbors) <= params.d)
        checked += sum(len(neighbors) <= params.d for neighbors in truth.values())
        errors += local_errors
        terminal_errors = sum(neighbors != screen["rows"][u] for u, neighbors in truth.items())
        saved.update({**cost, "posthoc_true_edges": sum(map(len, truth.values()))//2,
                      "posthoc_low_degree_row_errors": local_errors,
                      "posthoc_peel_degree_le_half_d": sum(len(truth[u]) <= params.d/2 for u in screen["peel"]),
                      "posthoc_peel_degree_gt_half_d": sum(len(truth[u]) > params.d/2 for u in screen["peel"]),
                      "posthoc_unpeeled_degree_gt_d": sum(len(neighbors) > params.d and u not in screen["peel"]
                                                          for u, neighbors in truth.items()),
                      "residual_reduction_to_next": len(residual)-len(result["screens"][index+1]["rows"])
                      if index+1 < len(result["screens"]) else None})
    return {"low_degree_rows_checked": checked, "low_degree_row_errors": int(errors),
            "terminal_row_errors": int(terminal_errors), "fallback": result["fallback"],
            **tree_schedule_audit(oracle, result["batches"])}


def run_job(job):
    kind, target, p, m, repeat = job
    if target not in TREE_IDS:
        row = (legacy_proposal(("curve_exploration", target, N, p, m, repeat, EXPLORE_SEED)) if kind == "proposal"
               else legacy_baseline(("baseline", target, N, m, repeat, EXPLORE_SEED)))
        row.update({"job": list(job), "phase": "curve_exploration"})
        return row
    np.seterr(divide="raise", over="raise", invalid="raise")
    seeds = tree_seeds(target, repeat, kind, m)
    oracle = make_tree(N, target, seeds[0], coupling=.5)
    started = perf_counter()
    if kind == "proposal":
        params = FixedColorings(N, oracle.theta, beta=BETA, palette_override=p, coloring_count=m)
        observer, recorder = ExplorationObserver(params), TreeDensityRecorder(N)
        result = sample(oracle, params, seeds[1], seeds[2], observer=observer, commit_observer=recorder)
        sample_seconds = perf_counter()-started
        score = recorder.finish(oracle, result["sample"])
        checked = audit_tree(oracle, params, result, observer)
        structural = (checked["all_tokens_committed"] and checked["fallback"] is None
                      and checked["unsafe_batches"] == 0 and checked["low_degree_row_errors"] == 0
                      and checked["terminal_row_errors"] == 0)
        auxiliary = {"palette": p, "colorings": m, "parameters": asdict(params),
                     "separation_lhs_over_signal": (4*params.eps+params.tail_tolerance)/params.signal,
                     "screen_calls": len(result["screens"]), "screen_cap": params.screen_cap,
                     "screen_cap_reached": len(result["screens"]) == params.screen_cap,
                     "screen_observations": observer.screens, "depth": 1+len(result["screens"])+oracle.cost.rounds,
                     "structural_success": structural, "sample_seconds": sample_seconds,
                     "posthoc_seconds": perf_counter()-started-sample_seconds, **checked}
    else:
        result = tree_random_batch_sample(oracle, m, seeds[1], seeds[2])
        score = {k: v for k, v in result.items() if k not in ("sample", "batches")}
        auxiliary = {"budget": m, "depth": m, "screen_calls": 0}
        assert oracle.cost.total == m
    return {"job": list(job), "kind": kind, "phase": "curve_exploration", "target": target,
            "n": N, "repeat": repeat, "seeds": seeds, "theta": oracle.theta, "vocab": oracle.vocab,
            "max_degree": oracle.max_degree, "edge_count": len(oracle.edges),
            "edges_sha256": hashlib.sha256(oracle.edges.astype("<i8").tobytes()).hexdigest(),
            "seconds": perf_counter()-started, "batch_size_histogram": {str(k): v for k, v in sorted(Counter(map(len, result["batches"])).items())},
            "sample_sha256": hashlib.sha256(result["sample"].astype("<i4").tobytes()).hexdigest(),
            **score, **asdict(oracle.cost), "total": oracle.cost.total, **auxiliary}


def execute(jobs, path, workers):
    records = read_runs(path)
    done = {tuple(r["job"]) for r in records}
    if len(records) != len(done) or not done <= set(jobs):
        raise ValueError("Please keep the frozen settings and all saved seeds when resuming.")
    pending = [job for job in jobs if job not in done]
    if not pending:
        return sorted(records, key=lambda r:r["job"])
    load_backend()
    started = perf_counter()
    with ProcessPoolExecutor(max_workers=workers) as pool, path.open("a") as stream:
        futures = [pool.submit(run_job, job) for job in pending]
        for future in as_completed(futures):
            try:
                row = future.result()
            except BaseException:
                for remaining in futures:
                    remaining.cancel()
                raise
            records.append(row)
            stream.write(json.dumps(row, separators=(",", ":"))+"\n")
            stream.flush()
            if len(records) % 10 == 0 or len(records) == len(jobs):
                print(f"{path.stem}: {len(records)}/{len(jobs)} {row['target']} setting={row['job'][2:4]} "
                      f"Q={row['total']} screens={row['screen_calls']} TVscore={row['tv_score']:.5g} "
                      f"elapsed={perf_counter()-started:.1f}s", flush=True)
    execution_path = path.with_name(path.stem+"_execution.json")
    invocations = json.loads(execution_path.read_text()) if execution_path.exists() else []
    invocations.append({"workers": workers, "new_runs": len(pending), "seconds": perf_counter()-started})
    write_json(execution_path, invocations)
    return sorted(records, key=lambda r:r["job"])


def legacy_rows():
    paths = [Path(__file__).with_name("results") / name for name in
             ("exploration/runs.jsonl", "validation/refinement_runs.jsonl")]
    sources = {str(path.resolve()): digest(path) for path in paths}
    rows = [r for path in paths for r in read_runs(path)
            if r["target"] in DENSE_GRID and r["palette"] in DENSE_GRID[r["target"]]
            and r["colorings"] in DENSE_GRID[r["target"]][r["palette"]]]
    return rows, sources


def match_budgets(summary):
    return [{"target": r["target"], "palette": r["palette"], "colorings": r["colorings"], "axis": axis,
             "proposal_mean": r[axis], "baseline_batches": min(N, int(np.floor(r[axis]+.5))),
             "capped_at_exact_singletons": int(np.floor(r[axis]+.5)) > N}
            for r in summary for axis in ("total", "depth")]


def compare(proposals, baselines, matches):
    comparisons = []
    for match in matches:
        a = sorted([r for r in proposals if (r["target"], r["palette"], r["colorings"])
                    == (match["target"], match["palette"], match["colorings"])], key=lambda r:r["repeat"])
        b = sorted([r for r in baselines if (r["target"], r["budget"]) == (match["target"], match["baseline_batches"])],
                   key=lambda r:r["repeat"])
        assert len(a) == len(b) == REPEATS
        assert [r["repeat"] for r in a] == [r["repeat"] for r in b] == list(range(REPEATS))
        assert all(x["seeds"][0] == y["seeds"][0] for x, y in zip(a, b))
        delta = np.asarray([y["tv_score"]-x["tv_score"] for x, y in zip(a, b)])
        comparisons.append({**match, "proposal": aggregate(a), "baseline": aggregate(b),
                            "baseline_minus_proposal_tv": float(delta.mean()),
                            "paired_difference_se": float(delta.std(ddof=1)/np.sqrt(REPEATS))})
    return comparisons


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=("all", "proposal", "baseline"), default="all")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results") / "tree_study")
    args = parser.parse_args()
    if args.workers < 1:
        raise ValueError("Please use a positive worker count.")
    args.output.mkdir(parents=True, exist_ok=True)
    reused, provenance = legacy_rows()
    protocol = {"n": N, "repeats": REPEATS, "d": 9, "chunks": 1, "beta": BETA,
                "dense_grid": DENSE_GRID, "tree_grid": TREE_GRID,
                "tree_seed": TREE_SEED, "legacy_seed": EXPLORE_SEED, "tree_coupling": .5,
                "purpose": "Exploration, not a held-out confirmation. Add points near useful settings and broaden tree shapes. "
                           "Retain every setting and seed; superiority to random batches in every regime is not required.",
                "targets": "Path; breadth-first balanced binary tree; uniform labeled tree from a uniform Pruefer sequence. "
                           "These are connected trees. Labels are randomly permuted. theta=0.5/max_degree for each realization; "
                           "this matches the existing certificate, not theta across shapes.",
                "risk": "Mean realized density score estimates E_graph,controller TV(P_graph,Q_graph,controller).",
                "baseline": "Fixed rounded mean total-query or sequential-stage budget, capped at N; balanced nonempty random batches.",
                "oracle": "Exact two-pass sum-product for all submitted states. Native arithmetic changes runtime only; "
                          "state reuse is identified solely from public input assignments. The sampler is unchanged.",
                "reused_sources_sha256": provenance,
                "source_sha256": {name: digest(Path(__file__).with_name(name)) for name in SOURCES}}
    freeze_json(args.output / "protocol.json", protocol)
    wanted = [("proposal", target, p, m, repeat) for target, ps in {**DENSE_GRID, **TREE_GRID}.items()
              for p, ms in ps.items() for m in ms for repeat in range(REPEATS)]
    old_keys = {("proposal", r["target"], r["palette"], r["colorings"], r["repeat"]) for r in reused}
    new_jobs = [job for job in wanted if job not in old_keys]
    proposal_path = args.output / "new_proposal_runs.jsonl"
    new_rows = execute(new_jobs, proposal_path, args.workers) if args.stage != "baseline" else read_runs(proposal_path)
    assert {tuple(r["job"]) for r in new_rows} == set(new_jobs)
    proposals = reused+new_rows
    summary = summarize(proposals, REPEATS)
    freeze_json(args.output / "summary.json", {"runs": len(proposals), "reused_runs": len(reused), "results": summary})
    matches = match_budgets(summary)
    freeze_json(args.output / "matched_budgets.json", matches)
    if args.stage == "proposal":
        return
    baseline_jobs = sorted({("baseline", m["target"], 0, m["baseline_batches"], repeat) for m in matches for repeat in range(REPEATS)})
    baselines = execute(baseline_jobs, args.output / "baseline_runs.jsonl", args.workers)
    freeze_json(args.output / "comparisons.json", compare(proposals, baselines, matches))
    print(f"Finished {len(proposals)} proposal runs ({len(reused)} reused) and {len(baselines)} baseline runs.", flush=True)


if __name__ == "__main__":
    main()
