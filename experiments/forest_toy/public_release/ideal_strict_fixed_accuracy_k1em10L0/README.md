# Ideal-forest fixed-accuracy experiment (`K_star = 10^-10 L0`)

This directory is the public, self-contained bundle for the fixed-accuracy
forest-toy experiment.  It contains the code and frozen parent inputs needed
to rerun the random baseline from an empty output directory, the complete
scalar records from that fresh rerun, the paper-facing figure, and an
independent comparison against the earlier incrementally refined result.

## Reported experiment

- Forests: matching, path, binary tree, and growing stars.
- Sequence lengths: `8192, 10240, 12288, 14336, 16384`.
- Accuracy rule: `K + 2 * MC_SE <= K_star`, with the common rule
  `K_star = 10^-10 L0` and a forest-specific `L0` fixed at `N=2048`.
- Replicates: three target draws crossed with two sampler streams per cell.
- Resource: `Q_tot = Q_pre + Q_cf + R`.
- Points: mean over the six runs; whiskers: their minimum--maximum range.

The proposal cohort is reused because all 120 fresh proposal evaluations have
structural exact-zero discrepancy.  The random baseline is searched
independently on each coupled per-run budget curve.

## Canonical artifacts

The fresh-from-scratch result is the canonical reproducibility run:

- `results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em10L0_fresh/`
- paper figure:
  `ideal_strict_fixed_accuracy_linear_errorbars_1x4.pdf`
- reduced-size paper figure with enlarged type and marks:
  `ideal_strict_fixed_accuracy_linear_errorbars_1x4_large_text.pdf`
- machine audit: `audit.json`
- reproduction comparison: `reproduction_comparison.json`

The sibling `random_per_run_threshold_search_k1em10L0/` directory is the
incrementally refined reference used only for the reproduction comparison.
The fresh run used no seed records, evaluated 1,566 budgets, and completed in
976.5 seconds with eight workers on `newton03`.  It exactly reproduced all 120
selected budgets, all brackets, and all 20 paper-facing random query
summaries.  Shared-record success labels were identical; the maximum absolute
floating-point difference in `K` or `K_upper` was `2.33e-12`.

Presentation-only amendment (2026-09-26): the dotted reference-line legend
was shortened to `$Q_{\mathrm{tot}}=N$`.  No numerical data changed.

Large intermediate NPZ graph, probe, trace, and target-profile files are not
included.  The raw JSONL outcomes, manifests, selections, summaries, source
snapshots, logs, and audits needed to inspect the reported result are included.

## Environment

The checked fresh run used Python 3.12.4, NumPy 1.26.4, and eight worker
processes on Linux.  Matplotlib 3.8.4 generated the included figure.  A C
compiler is required because the exact forest backends are compiled into a
temporary shared library on first use.  BLAS and OpenMP thread counts were
fixed to one per worker.

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
```

## Reproduce from an empty output directory

From this directory:

```bash
./reproduce_fresh.sh 8
```

An optional second argument chooses a different output directory:

```bash
./reproduce_fresh.sh 8 results/ideal_capless_fixed_accuracy_scaling/my_fresh_run
```

The wrapper runs the full coarse search and refinement without
`--seed-records`, renders both the standard and large-text 1-by-4 figures, and
compares the result with the included incrementally refined reference.  On
other hardware, wall-clock time and the last floating-point bits may differ;
selected budgets, success labels, and paper-facing query summaries are the
reproducibility targets.

To regenerate only the reduced-size inclusion variant from a frozen result:

```bash
python -B report_ideal_strict_fixed_accuracy_1x4.py \
  --large-text \
  --results results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em10L0_fresh
```

To verify only the two bundled results:

```bash
./verify_bundled_results.sh
```

For a quick two-worker end-to-end check of the compiled backend and result
pipeline:

```bash
./smoke_test.sh
```

## Layout

- `random_per_run_threshold_search.py`: fresh random-threshold driver.
- `*_bp.c` and `forest_*_kl.c`: exact forest backends compiled at runtime.
- `report_ideal_strict_fixed_accuracy_1x4.py`: paper-figure renderer.
- `verify_random_threshold_reproduction.py`: result-comparison audit.
- `RANDOM_PER_RUN_THRESHOLD_SEARCH_PLAN_2026-09-21.md`: frozen search plan.
- `smoke_test.sh`: small standalone execution check.
- `PAPER_TEXT.md`: manuscript handoff and protocol description.
- `results/ideal_capless_fixed_accuracy_scaling/`: frozen parent inputs and
  the accumulated and fresh `10^-10 L0` results.
- `SOURCE_MANIFEST.json` and `SHA256SUMS`: provenance checksums.

## Licensing note

The original experiment code and its software documentation are distributed
under the MIT License; see the repository-root `LICENSE`. Dependencies retain
their respective licenses.
