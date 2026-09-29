# Lower bound with free current-history marginal feedback

`ForestSampling/FreeMarginalLower.lean` is built and contains seven public theorems. Their individual axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; no new axiom or proof placeholder is used.

The final lower statements apply directly to arbitrary `RandomizedSamplerData`, its actual probability seed measure, actual TV output risks, family-wise `RiskMeasurableAt`, and `WithinFreeMarginalBudgets`. They do not assume membership in the older `OracleBudgetedSampler` subtype.

The proof re-establishes the concrete collision tail using the actual retained commit count under free-marginal budgets. The unconditional compensated midpoint moment remains valid for all programs. `FreeMarginalDisclosure.midpointLedger_freeMarginal_disclosure_le_eighth` supplies the real adaptive disclosure estimate, including arbitrary uncharged reads at the current commit state. The actual midpoint affinity/penalty reduction then gives the finite-prior TV lower bound for every seed. Finite-prior seed integration and the true worst-case supremum give the randomized lower bound.

The final target-error alternative is unchanged: either `Q > bankSize/8`, or `R > N/16384`, or `R ≥ N*edgeCoupling²/(786432*epsilon)`. Length zero and zero-round executions are handled from completion semantics, not an extra positive-round hypothesis.

This is intentionally a stronger observation model than the old program interface. The separate `ObservedProgram`/`ObservedSimulation` compilation preserves actual output laws and charges while converting commit-row feedback into these free marginal reads; `ObservedLower` consumes the present theorem for the paper's full observation model. This file alone does not identify the old commit continuation with row-observing continuations.

Validation: `lake build ForestSampling.FreeMarginalLower` passed (8749 targets), and all seven `#print axioms` checks passed. Old budget classes and old lower proofs were not modified.
