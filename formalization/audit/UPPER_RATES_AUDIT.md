# Upper resource-rate audit

`ForestSampling/UpperRates.lean` is built and contains 38 public theorems. Every theorem was inspected with `#print axioms`; all depend only on the standard `propext`, `Classical.choice`, and `Quot.sound` axioms. There are no proof placeholders or additional axioms.

## Proved correspondence

- The benchmark floor is the actual public floor `4 max(rowError, 1/vocabularySize)`. The finite margin `16 max(...) ≤ signal ≤ 1/2` proves feasibility of the original clipped dyadic grid and places its maximal feasible selection in `[signal/4, signal/2]`.
- The source-column bound is derived from the actual RF certificate, actual oracle TV accuracy, the actual observed banks, and the selected finite-grid threshold. It is at most `(16/signal)^(1/ζ)+1`; no bank-size rate is assumed.
- The exact query expression is the actual column count times `(J+1) T C (C+L)`. For `L=D`, the proved color contribution is at most `272 D²`.
- The actual public phase, repetition, centroid, and hard-round ceilings are bounded explicitly. With `w(N)=1+log(N+1)`, queries are at most `272 K_S K_T b D² w(N)²` and rounds at most `K_R (N/D) w(N)`. The constants are explicit definitions. The repetition estimate assumes only the concrete failure allocation `η ≥ c/N^a`, with `c>0,a≥0`; fixed TV allocations satisfy this with `c=η,a=0`.
- The actual integer cutoff is `ceil((N signal^(1/ζ))^(1/3))`. If its unrounded value is at least one, ceiling loss is at most two. Query and round bounds then share the scale `N^(2/3) signal^(-1/(3ζ))`, with an explicit query rounding factor four.
- Substitution of the actual benchmark signal proves the exact scale `2^(1/(3ζ)) N^(2/3+1/(9ζ)) / radius^(2/(9ζ))`.
- For every fixed positive radius and `ζ>1`, that scale times the full squared logarithmic envelope is formally `o(N)`. This is a filter-based little-o theorem, not only an algebraic comparison of exponents.
- `selected_program_within_queryCount` connects the exact expression to the concrete manuscript program, all seeds, actual initial frozen-oracle reply, arbitrary later replies, and all commit outcomes.

## Scope

This module supplies finite rate algebra and the actual RF/grid/resource bridges. `UpperFeasibilityGrowth.lean` supplies eventual finite feasibility and eventual cutoff range from literal vocabulary growth. `MainUpperTheorem.lean` separately assembles the public sampler, uniform risk, and common public resource cap. The general multivariate appendix regime with varying accuracy/exponent is not asserted by the fixed-benchmark little-o specialization.

## Validation

`lake build ForestSampling.UpperRates` completed successfully (8787 targets). The dedicated 38-theorem axiom audit completed successfully. The exact dependency pins are those of the isolated verification worktree.
