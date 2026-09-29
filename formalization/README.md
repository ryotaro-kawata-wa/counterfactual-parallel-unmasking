# Forest Sampling formalization

This project verifies mathematical claims in the current arXiv manuscript using
Lean, with the original September 26 mathematical basis preserved. The actual finite randomized TV/KL upper theorems,
full-observation adaptive lower theorem, arbitrary-vocabulary public-class
lower calibration, and uniform upper cutoff curves are proved. Both ordinary
commit probability feedback and sampled values are included in the lower
controller interface. Public row-selector invariance, actual grouped depth,
and the sharper successful-path round count are proved.

The inventory's **36 named proof claims now have checked formal theorem
bundles**, including the actual path TC/DTC/effective-TC comparison. The 25
named definitions/assumptions have a separate translation audit. This does
not certify every unlabelled sentence, experimental conclusion, citation,
or external literature comparison. TeX-to-Lean correspondence remains an
explicit audit boundary; the inventory itself is not proof evidence.

A concise Japanese handoff is [VERIFICATION_REPORT_JA.md](VERIFICATION_REPORT_JA.md).

## Reproduce

Lean is pinned to **4.33.0**, Mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d`, and all dependencies to
`lake-manifest.json`. From this directory:

```sh
source ~/.elan/env  # if lake is not already on PATH
lake exe cache get # only needed for an uncached checkout
lake build
lake env lean AuditAxioms.lean
python3 audit/check_manuscript_basis.py
python3 audit/check_claim_references.py
```

Do not run `lake update` as part of routine verification. The axiom audit scans
every imported project declaration, including generated auxiliaries and
transitive proof dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted; `sorryAx` and new project axioms fail. The number
of audited declarations is not a count of paper theorems.

## Correspondence and scope

The mathematical baseline is arXiv-layout commit
`1507791fd7c1137c77ec139cc0b73b5765f1464b`, unchanged from pushed ICLR commit
`8a8c185375bd4de48c2ef52807da0c3cc00e15ac`.
[`audit/claim_inventory.json`](audit/claim_inventory.json) fingerprints all 62
current compiled TeX inputs and lists 36 named proof claims plus 25 definitions
and assumptions. The original 61-input basis is preserved separately. The
[release-basis audit](audit/ARXIV_RELEASE_BASIS.md) reviews the later author,
acknowledgment, Figure 3, and paragraph-spacing presentation changes; all
mathematical statement and proof files are byte-identical to the original basis. Optional omitted exponent sections are excluded. Coverage means
the listed formal statements under their stated hypotheses; the inventory
itself is not proof evidence. Source changes require deliberate re-auditing.

Lean checks the formal statements and their proofs. Mathematical translation,
algorithm correspondence, unlabelled prose, external comparisons, citations,
experiments, and exposition still require human-facing audits. No mathematical
TeX content has been changed by the formalization work.

## Current theorem interfaces

- `CurrentUpperTheorem` proves the actual packed sampler's finite TV bound
  `rho + eta` and KL bound `N*kappa + N*log|V|*eta`. `GridUpperTheorem` uses the
  manuscript's maximal feasible clipped dyadic threshold and proves robust TV
  over the full frozen-oracle class. `UpperRiskCalibration` instantiates the
  target-error choices. No abstract successful-path or screen-failure
  hypothesis remains.
- `PackedLoopStructure`, `PackedFailure`, and `SafeControllerComparison`
  establish actual adaptive structural safety before first failure, fresh
  reached-screen probability, and an explicit safe replacement. The KL proof
  uses actual joint-reference histories, with graph safety implying zero
  batch total correlation.
- `PackedParameters` proves the public integer choices and exact realized-bank
  query/round counts. `PackedPathDepth` proves a legal grouped-query trace
  with depth at most `1 + actual commit rounds + screen cap`; it does not
  mistake the sequential query-constructor count for parallel depth.
- `CurrentLowerTheorem` proves the full nonlinear finite lower bound and
  target-error alternative for actual family-oracle budgets. Actual dynamic
  posteriors, disclosure, retirement accounting, compensated Laplace moment,
  collision tail, and affinity loss are proved for the constructed family.
- `HardClassMembership`, `LowerAsymptotics`, `LowerVocabularyGrowth`, and
  `PublicClassLower` give actual RT/UEN/RF/oracle inclusion and restrict a
  uniform public-class guarantee to the family. Literal vocabulary growth
  yields the pointwise large-N query/round lower alternative. `ObservedProgram`
  retains the complete commit feedback; vocabulary transport
  preserves actual controller laws, risk, budgets, and full class membership.
  `ArbitraryVocabularyLower` and `ObservedBenchmarkLower` give the final main
  and independent-radius lower statements on any finite vocabulary.
- `UpperRates` gives actual-grid feasibility, RF bank bounds, explicit
  logarithmic resource bounds, the balanced cutoff identity, and formal
  little-o estimates. `UpperFeasibilityGrowth` proves eventual feasibility
  and the actual integer cutoff range from the public growth assumption.
  `MainUpperTheorem`, `MainKLUpperTheorem`, and `GeneralUpperCurve`
  assemble the uniform public samplers with actual TV/KL and resource bounds.

`PaperStatements` and the old universal-reply minimax interface are preserved
legacy definitions. They are not the current paper theorems; the final finite lower
result uses `ObservedLower`/`InstanceFamily.observedMinimax` and budgets on actual family-oracle
paths, including commit-row feedback.

Detailed evidence and remaining work are in
[the current theorem audit](audit/CURRENT_THEOREMS_AUDIT.md),
[the lower audit](audit/LOWER_BOUND_AUDIT.md),
[the upper audit](audit/UPPER_BOUND_AUDIT.md),
[the capped-loop audit](audit/PACKED_LOOP_STRUCTURE_AUDIT.md),
[the rate audit](audit/UPPER_RATES_AUDIT.md), and
[the calibration/comparison audit](audit/CALIBRATION_AND_COMPARISON_AUDIT.md).
Older audit entries describe intermediate states; later completed milestones
supersede their remaining-obligation lists.

The current translation audit is [interface correspondence](audit/INTERFACE_CORRESPONDENCE.md).
The [uniform-curve audit](audit/GENERAL_UPPER_CURVE_AUDIT.md) records the complete
cutoff range and successful-path resources. Later completed milestones in
audits supersede explicitly identified intermediate limitations.

`PathComparisonTheorem`, `PathBenchmarkMembership`, and
`PathEffectiveTCTheorem` give exact TC/DTC formulas, actual eventual benchmark
class membership, and uniform two-sided linear effective-TC bounds. The latter
starts from the full independent mask law and proves its conditional-MI and
integral identities; it does not assume an external TC/DTC comparison lemma.

The completed reproducible validation is recorded in
[FINAL_VALIDATION.md](audit/FINAL_VALIDATION.md): 173 proof modules, 4,716
audited declarations, 61 matching TeX inputs, and 122 resolving inventory
references. Independent final main and path translation reviews are linked
there. Those are the original verification results. The current arXiv branch
integrates the complete proof development with the manuscript and experiments;
its updated presentation fingerprint is described in the release-basis audit.
Publishing this branch does not submit the paper to arXiv.
