# Compensated evaluator and actual midpoint transport audit

`ForestSampling/CompensatedLaplace.lean` retains the original `laplaceFactor`
and `laplaceEval` definitions and signatures. Its theorem
`SurvivorRecord.laplaceEval_eq_retained_expectation` now proves that the
recursive compensated midpoint evaluation equals the terminal expectation
of `exp(-ledger.collisions + ledger.activity / 64)` under the actual retained
Program law, for every compatible starting record and hidden instance.
Queries use their actual selected-oracle replies; commits use the actual
instance midpoint kernel. The proof proceeds through the dependent
commit-value/path sum, adds natural collision counts before their real cast,
and multiplies the corresponding exponential factors.

`ForestSampling/CompensatedLaplaceTransport.lean` then supplies the initial
law correspondence. Its five theorems prove nonemptiness of the initial
compatible fiber, the actual all-mask preprocessing branch equality, and
exact expectation transport through the initial-fiber equivalence and the
instance--midpoint joint law. The main endpoint is
`NonlinearMatchingParameters.midpointLedger_expectation_eq_initial_fiber_laplace`.
The shared initial program is explicitly
`A.program seed (fun _ => P.toHardLocal.commonMarginal)`.

Thus averaging `laplaceEval` on the initial uniform compatible fiber is
exactly the actual `P.midpointJoint` expectation of the compensated
`P.midpointLedger`. There is no unidentified surrogate path law, assumed
preprocessing invariance, or change to the sampler's risk.

Both module builds pass without warnings in these modules. The retained
expectation theorem and all five transport theorems were checked with
`#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound` occur.
No axioms, `sorry`, or `admit` were introduced. The uniform-fiber inductive
upper bound on `laplaceEval` belongs to `AdaptiveSurvivorLaplace.lean` and is
not asserted by these equality bridges alone.
