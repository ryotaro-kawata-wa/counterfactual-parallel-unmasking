# Actual adaptive collision verification

The concrete midpoint compensation bound is now proved for every sampler and
fixed seed, without assumptions about replay, a survivor invariant, per-step
collision losses, or a compensated supermartingale.

- `SurvivorProcess` identifies whole retirement fibers and actual normalized
  query/commit laws. `SurvivorPosterior` and `MidpointSurvivor` connect their
  posteriors to actual retained-path prefixes.
- `SurvivorLaplace.uniform_fiber_commit_compensated` (in the
  `HardMatching.SurvivorRecord` namespace) handles the concrete single-commit
  matching transform, including zero/one remaining vertices.
- `CompensatedLaplace.laplaceEval_eq_retained_expectation` identifies the
  fixed-instance recursion with the terminal actual ledger moment.
- `AdaptiveSurvivorLaplace.uniformLaplaceEval_le_one` performs real `Program`
  induction, disintegrating each query/commit update by its entire uniform
  compatible fiber. Query replies, commit kernels, and local compensation
  factors are proved constant on the required fibers.
- `CompensatedLaplaceTransport` uses the real common all-mask response to
  identify this recursion with the actual joint instance--midpoint law.
- `AdaptiveCollisionMoment.midpointLedger_compensated_laplace_le_one` proves
  `E exp(-Z+A/64) <= 1`. The module's collision-tail theorem still needs the
  mean query-disclosure bound `E D <= N/8`; its pathwise activity is already
  supplied by the actual retirement ledger.
- `RetirementCollisionBound` proves the exact averaged `1-(1-Hedge²)^Z`
  inequality for this dynamically retired-edge count.
- `OracleLowerReduction` uses the correct family-indexed fixed-oracle
  all-path minimax class. Its only remaining probabilistic hypothesis is the
  same mean query-disclosure estimate.

The full finite lower theorem is not marked proved until that final estimate
is instantiated. Asymptotic calibration and hard-family inclusion are further
manuscript obligations. Source compilation is followed by the integrated
`AuditAxioms.lean` check; no proof placeholders or custom axioms are permitted.

## Final finite-theorem assembly

`SurvivorDisclosure.uniformDisclosureEval_le` proves the actual conditional
Q/K potential from per-instance oracle budgets. `DisclosureTransport` yields
E(query-retired vertices) <= 2*N*Q/K and hence E D <= N/8 when Q <= K/8.
`CurrentLowerTheorem.midpointLedger_collision_tail` and
`CurrentLowerTheorem.lowerValue_le_oracleMinimax` (both in the
`NonlinearMatchingParameters` namespace) discharge every remaining reduction
premise. The finite theorem uses the manuscript's actual-oracle admissible
class, including arbitrary measurable seed spaces. The target-error corollary
is also instantiated; no extra positive-round premise is added, because zero
rounds imply an already complete initial history.

The earlier conditional statements are retained as intermediate lemmas.
Hard-family class inclusion and asymptotic calibration are not certified by
this finite theorem.
