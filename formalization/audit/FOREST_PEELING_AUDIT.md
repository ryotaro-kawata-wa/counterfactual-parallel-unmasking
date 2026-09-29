# Actual finite-forest peeling audit

`ForestSampling/ForestPeeling.lean` proves the successful-screen combinatorics
in `manuscript_2026-09-17/src/sections/proofs/upper_structure.tex`. Its graph is
an arbitrary actual finite `SimpleGraph`, assumed acyclic. The sole screen
contract is: each returned row has cardinality at most `D`, and every vertex
of true degree at most `D` reports exactly its actual neighbor set. No bound
on false positives from high-degree rows or static outdegree is assumed.

Definitions include incoming claim counts, the observable peel threshold
`D < 2 * claims`, the actual high-degree set, and degrees in an induced
remaining-vertex set. `highVertices_induce_map/card` identify the set-based
representation with the genuine induced graph.

The 28 proven results include:

- Finite-forest degree sum `< 2 n` for nonempty graphs and `≤ 2 n` including
  the empty graph. This uses an acyclic extension to a spanning tree of the
  complete graph and Mathlib's proved tree edge count.
- An unpeeled high-degree vertex has more than `D/2` neighbors in the actual
  high-degree induced forest, because every low-degree neighbor claims it.
- Actual next-phase high counts satisfy the sharp `4/D` contraction; the
  cardinality inequality is strict whenever the old high-degree set is
  nonempty. Both a real-valued version and the public relaxed `8/D` version
  are available, with explicit positive-denominator assumptions.
- Empty observable peeling implies maximum degree at most `D` for `D ≥ 4`,
  and hence every successful row is exact. The manuscript uses `D ≥ 9`.
- Initial high counts satisfy `(D+1) h < 2 n`; directed claims double-count
  exactly to row sizes and total fewer than `2 n`; one peel set has
  `D * |peel| < 4 n` singleton commits.

`lake build ForestSampling.ForestPeeling` passes without warnings in the new
module. All 28 public theorems were inspected with `#print axioms`; only
`propext`, `Classical.choice`, and `Quot.sound` occur. No axioms, `sorry`, or
`admit` were introduced.

This module does not construct the adaptive `Program` controller or identify
its public random seed distribution. Iterating the established contraction
to the exact logarithmic phase cap and charging the controller's total
resource counters remain separate integration steps. Centroid selection is
handled in `ForestCentroid.lean`.
