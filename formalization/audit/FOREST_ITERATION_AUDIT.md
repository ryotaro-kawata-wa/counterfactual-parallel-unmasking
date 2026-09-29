# Actual forest deletion iteration audit

`ForestSampling/ForestIteration.lean` connects the local forest lemmas to
exact finite phase and depth bounds. The module compiles cleanly, and all
24 public theorems were audited with `#print axioms`; only `propext`,
`Classical.choice`, and `Quot.sound` occur. No additional axioms, `sorry`,
or `admit` were introduced.

The public numerical definitions reproduce the manuscript:

- `phaseCap N D = ceil(max(log(2*N/(D+1)),0)/log(D/8))`;
- `centroidDepth N = ceil(log₂(N+1))`;
- `hardRoundCap N D = ceil(4*N*phaseCap N D/D) + centroidDepth N + 2`.

The ceiling is a natural ceiling. On the stated nonnegative expressions
it agrees with the manuscript's ceiling. `phaseCap_geometric` proves the
exact `8/D` reduction factor, and `lt_two_pow_centroidDepth` proves the
strict integer margin `N < 2^centroidDepth N`. `phaseCap_pos` explicitly
records that `D >= 9` and `D+1 < 2*N` imply a positive number of phases.
In particular the manuscript's `N >= 10`, `9 <= D <= N-1` guarantees this.
The strict successful-path estimate has no zero-phase counterexample in
that manuscript domain. The generalized Lean APIs also treat zero phases,
where the total peel count is zero and the nonstrict estimate is appropriate.

`DeletionSequence A` stores actual original-label finite vertex sets and
their successive inclusions. Its graph at time `i` is exactly the induced
graph `G[S_i]`; its `highCount` counts the vertices of that graph whose
actual degree exceeds the threshold. It does not store or assume a count
recurrence. For a successful `ScreenContract` and removal of every member
of the frozen peel set, `peeling_contraction` constructs an embedding into
the genuine post-peeling induced graph and derives the sharp factor `4/D`.
Additional deletions are permitted. The real `8/D` relaxation and the
strict initial forest degree estimate yield
`highCount_zero_at_phaseCap`. `final_rows_exact` applies the final successful
screen to recover all remaining neighbor rows exactly. Screen success is
required only on the specified finite prefix; later entries of the sequence
are irrelevant to those conclusions.

The actual frozen peel sizes satisfy `sum_peel_card_lt_div`: fewer than
`4*N*k/D` singleton commits over every positive successful prefix of length
`k` in a nonempty ambient type. This is the manuscript's factor **with** the
phase count, not a purported total `4*N/D`. `sum_peel_card_le_div` includes
zero phases and an empty ambient type. `peel_plus_centroid_lt_reserved`
combines the actual frozen-set count with a terminal-round bound to show
strict room before the reserved final-round guard.

For centroids, `component_halves_of_embedding` maps a child component into
its actual parent, excludes that parent's chosen centroid, and injects the
child into a component left by deleting it. `centroid_component_bound`
iterates this structural argument on a `DeletionSequence`, proving
`2^k * card(child) <= N` for each actual remaining component. Thus
`remaining_empty_at_centroidDepth` proves the actual remaining vertex set
is empty by the public depth. The choices can be any genuine component
centroids, including the controller's smallest-public-label choices.

These are completed graph and scalar iteration theorems. They do not
assert that the concrete capped sampler has successful screens, or by
themselves identify its histories with a deletion sequence. The separate
controller bridge must establish those actual-path hypotheses and use the
proved reserve inequality to rule out an early guard on successful paths.
No changes were made to `CappedController.lean`, `PackedSampler.lean`,
existing graph modules, or the root import list.
