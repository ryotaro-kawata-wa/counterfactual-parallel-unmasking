# Validation of the arxiv-v1 artifact snapshot

Checks completed on 29 September 2026. Machine-readable outcomes are in
[release_checks.json](release_checks.json). This record states the checks
performed for the public export; it does not extend the formalization's scope.

## Lean and manuscript correspondence

The public copy passed `lake build` (8,880 jobs), using an existing cache with
pinned dependencies. All 175 Lean source files and the toolchain/dependency
pins matched the previously checked development byte-for-byte. This was not a
from-scratch dependency rebuild. The following audits were rerun in the public
copy:

- `lake env lean AuditAxioms.lean`: all 4,716 project declarations passed; only
  `propext`, `Classical.choice`, and `Quot.sound` are allowed.
  [Exact output](lean-axioms.log).
- `python3 audit/check_claim_references.py`: all 122 inventory references resolve.
  [Exact output](lean-claims.log).
- `python3 audit/check_manuscript_basis.py`: all 63 compiled TeX fingerprints match.

There are 36 named mathematical proof claims in the inventory. Translation of
manuscript statements and assumptions is audited separately. Lean does not
certify all manuscript prose, references, or scientific experiment conclusions.

## Experiments

All 128 experiment-manifest checksums passed. `verify_bundled_results.sh` passed:
120 selected budgets, 20 summary cells, and the proposal-figure data agree; all
1,566 shared records have identical success labels. The maximum absolute
floating-point KL difference is approximately 2.33e-12.
[Detailed comparison](experiment_comparison.json).

A new two-worker smoke run completed four searches in 16.84 seconds, with no
reused budget records, and passed its audit. The environment used NumPy 1.26.4,
Matplotlib 3.8.4, and a C compiler. Temporary outputs are not release artifacts.
A full experiment was not rerun for this export; the separate full fresh-run
records already included in the experiment bundle provide that evidence.

## Manuscript package

The 72-file submission ZIP built in isolation with TeX Live 2026, an empty user
TeX tree, and disabled shell escape. All 97 pages exactly match the source PDF
in extracted text and rendered pixels at 150%. Pages 10–17, changed by the code
availability paragraph and subsequent text flow, were visually reviewed.
Figure 3 and the remaining pages are unchanged. Internal links and embedded
fonts passed checks; no missing citations/references or overfull boxes were found.

The actual arXiv-generated PDF still needs review after re-upload, particularly
the Definition/Lemma/Assumption reference names. A local LaTeX-kernel rollback
is not a reproduction of arXiv's full TeX Live 2025 environment.

## Artifact integrity

From the repository root, check the exact released files with:

```sh
shasum -a 256 -c SHA256SUMS
```

`SHA256SUMS` covers all released files except itself. It is intended for the
fresh `arxiv-v1` checkout; rebuilding the paper or rerunning experiments may
change generated files. The manuscript ZIP excludes code, caches, and private
reference-review evidence; the code and results are distributed here.
