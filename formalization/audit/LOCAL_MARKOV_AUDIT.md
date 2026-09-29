# Local Markov derivation audit

`ForestSampling/LocalMarkov.lean` derives singleton-row invariance from the
actual `ForestModel.target` factorization. It does not assume a conditional
independence law or replace the model by a surrogate distribution.

The public endpoint is
`ForestModel.exactRow_eq_of_neighbors_observed`: if a position is masked in
two submitted states and every graph neighbor is observed with the same value
in both, their actual `MaskedState.exactRow` laws are equal. All other
observations and masks may differ arbitrarily. The alphabet is finite and
nonempty, and the stored strict positivity guarantees every conditioning
event has positive probability.

The stronger `exactRow_eq_of_neighbors_fixed` identifies that row with the
normalized positive weights `a ↦ M.target (Function.update background j a)`
for any background compatible with the observed neighbors. This follows by
checking a cross-product identity for every root or parent-child factor,
multiplying those identities, summing over the actual masked-state agreement
fibers using a bijective coordinate split, and normalizing by finite-law
mass one. There is no division by an unproved-positive quantity.

`lake build ForestSampling.LocalMarkov` passes. All 11 public theorems were
checked with `#print axioms`; their only dependencies are `propext`,
`Classical.choice`, and `Quot.sound`. The new module has no warnings, axioms,
`sorry`, or `admit`.

The complete-boundary query bridge and its use in the screen contract belong
to the separate screening modules. This module by itself does not assert a
complete screening algorithm or an end-to-end upper minimax result.
