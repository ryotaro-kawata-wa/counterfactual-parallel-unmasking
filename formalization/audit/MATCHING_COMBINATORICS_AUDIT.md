# Matching combinatorics and initial-prior audit

`ForestSampling/MatchingCombinatorics.lean` is complete and stable. It imports `HardMatching` without changing the original `PerfectMatching` representation.

Proved scope:

- Matchings are determined by their mate functions; matching equality is decidable, and the space has `Finite` and `Fintype` instances.
- Each mate map is bijective. Every even `N` admits a perfect matching by transferring endpoint reversal on `Fin k × Fin 2` to `Fin N`; the construction includes `N = 0`.
- Position relabeling induces an equivalence of matching spaces. The uniform matching law is invariant under this equivalence.
- For distinct positions `i,j`, the exact uniform-partner probability is `P(mate(i)=j) = 1 / (N-1)`. The proof uses relabeling symmetry and normalization, with positive denominator derived from the existence of two distinct positions.
- Even `N` and `1 <= K` give an inhabited finite hard-instance index set. Its uniform law factors exactly into an independent uniform matching and independent uniform private triggers at every position.
- A general `FinDist.uniform` and its strict positivity are provided for any inhabited finite type.

Validation:

- `lake build ForestSampling.MatchingCombinatorics`: passed on pinned Lean/mathlib 4.33.0; only inherited modules replay existing linter warnings.
- All 19 public theorems were checked with `#print axioms`. Dependencies are subsets of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms.
- One private two-element endpoint-reversal lemma is used by the proved construction.

This establishes the initial prior and the unconditional uniform-partner law. It does not yet establish the distribution after adaptive transcript conditioning, the fixed-subset matching Laplace bound, or the main lower theorem. Those require restriction/extension and exposure arguments.
