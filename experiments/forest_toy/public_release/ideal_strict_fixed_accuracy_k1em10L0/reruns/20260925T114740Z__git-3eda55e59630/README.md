# Four-forest ideal: complete fresh reproduction

- Run ID: `20260925T114740Z__git-3eda55e59630`
- Source commit: `3eda55e596301a179d9a55471032cd28b84c3366`
- Node/workers: `newton03` / `8`
- Parent runtime: `100.3` minutes
- Strict-random runtime: `12.6` minutes
- Existing Proposal/Random observation records reused: none
- Canonical paper result replaced: no

## Comparison with the existing paper figure

The paper-facing result reproduced: all 120 selected random budgets, all 20
random cell summaries, the Proposal figure data, success labels, and numerical
tolerance checks match.  The generic verifier exits nonzero only because the
complete rerun intentionally regenerated `random_confirmation_records.json`,
so that parent-input hash differs from the earlier incremental reference.

This is recorded as a provenance difference, not a plotted-result difference.

Presentation-only amendment (2026-09-26): the dotted reference-line legend
was shortened to `$Q_{\mathrm{tot}}=N$`.  No numerical data changed.

## Files

- `named_figures/`: timestamp-, Git-, and figure-data-hash-named figures.
- `parent_fresh/`: full Proposal/initial-Random summaries and source snapshots.
- `strict_random_fresh/`: per-run strict Random search and figure data.
- `RUN_MANIFEST.json`: full provenance, comparison, and artifact hashes.
- `GIT_SHARE_MANIFEST.json`: Git-package exclusions and JSONL transformations.

Large regenerable target-profile NPZ files and per-job caches remain on
Newton.  Raw JSONL records are retained here as deterministic `.jsonl.gz`
files to keep the Git handoff compact.
