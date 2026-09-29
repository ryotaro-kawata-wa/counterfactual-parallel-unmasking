# Finite path geometry for comparison bounds

`PathGeometricSums.lean` proves the exact finite geometric and counting inputs for the masked path comparison. For q in (0,1], the ordered off-diagonal sum over i,j : Fin N of `(1-q)^(Nat.dist i.val j.val - 1)` is at most `2*N/q`. At a fixed i, each direction maps injectively into the finite exponent range below N, each range sums to at most 1/q, and summing over i gives the bound. The proof includes q = 1 and all short-path cases. Both if-diagonal and filtered-sum APIs are provided.

`InteriorAdjacent i j` requires distance one and both coordinates strictly between zero and N-1. The increasing pairs biject k : Fin(N-3) with (k+1,k+2); reversing the ordered pair gives a disjoint orientation. The exact cardinal is `2*(N-3)` using natural subtraction, with a real double-indicator-sum version for expectation calculations. No asymptotic endpoint correction is assumed.

Validation: `lake build ForestSampling.PathGeometricSums` passed (8707 jobs; 189 lines), with no warnings. Six key axiom checks—finite range bound, both ordered-sum formulations, increasing edge count, ordered adjacent count, and indicator sum—report exactly `[propext, Classical.choice, Quot.sound]`. The module is frozen and importable. These are geometry inputs; the actual masked conditional-information and effective-TC integral bridges are separate modules.
