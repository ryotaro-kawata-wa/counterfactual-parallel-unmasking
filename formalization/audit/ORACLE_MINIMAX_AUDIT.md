# Actual-oracle budgeted minimax correspondence audit

`ForestSampling/OracleMinimax.lean` defines the new feasible class
`InstanceFamily.OracleBudgetedSampler F Q R` by

    {A : RandomizedSamplerData N V //
      (∀ i, A.sampler.WithinOracleBudgets (F i).oracle Q R) ∧
      ∀ i, A.RiskMeasurableAt (F i)}.

`oracleMinimax F Q R` takes the infimum of the existing `worstCaseRisk F A`
over this class. The target, frozen oracle, output law, seed probability law,
TV loss, and seed integral are unchanged. The sole interface correction is
that budgets follow each actual family oracle's replies and actual all-mask
preprocessing reply, uniformly over seeds and possible batch values. The
all-mask preprocessing submission stays outside the existing counted-query
convention. `OracleBudgets.withinOracleBudgets_iff_retainedCounts` already
identifies this resource condition with all retained paths for nonempty
vocabularies.

The legacy `BudgetedSampler` instead requires budgets for arbitrary replies,
which is a stronger restriction. The new module retains the old class and
all previous proofs unchanged. Its explicit old-to-new embedding preserves
sampler data identically, and `oracleMinimax_le_minimax` proves the correct
comparison direction. A lower bound for only the old restricted infimum
does not establish the lower bound for the new infimum.

The 14 proved theorems supply explicit feasible-class nonemptiness for
`R ≥ 1` using the existing all-at-once program, the `N=0` version for all
round budgets, actual risk bounds and valid real infimum arguments, and a
finite-prior seedwise TV lower-bound bridge for the new class. The latter
reuses the existing measurable bounded-TV integration theorem, with no
extra Hellinger measurability assumption or substitute risk.

`NonlinearMatchingParameters.le_oracleMinimax_of_midpoint_penalty` is the
corresponding concrete hard-family wrapper: a midpoint penalty bound for
every sampler in the new class yields the lower bound on `oracleMinimax`.
The sampler quantifier in the probabilistic lower proof must therefore use
`OracleBudgetedSampler`, with its budget witness accessed as `A.2.1 i`.

`lake build ForestSampling.OracleMinimax` passes with no warnings in the new
module. All 14 public theorems were checked with `#print axioms`; only
`propext`, `Classical.choice`, and `Quot.sound` occur. No axioms, `sorry`, or
`admit` were introduced. This module provides the corrected correspondence
and reduction, not an unproved final midpoint penalty assertion.
