# Actual finite-tree centroid audit

`ForestSampling/ForestCentroid.lean` proves the centroid facts used in
`manuscript_2026-09-17/src/sections/proofs/upper_structure.tex`. No centroid
existence theorem was available in the pinned Mathlib graph library; the
existence proof here is derived from graph paths and finite minimization.

A vertex minimizing the sum of all graph distances is a centroid. For each
component after deleting that vertex, connectedness supplies an incident
neighbor in the component. Acyclic path uniqueness shows that every vertex
in that component is one step nearer to this neighbor. Every other vertex
is at most one step farther away, by the graph-distance triangle inequality.
Summing and using minimality proves `2 * component_size ≤ original_size`.
All components and cardinalities are those of the actual induced graphs.

The 16 public theorems also establish:

- `exists_centroid` for every finite tree, and a genuine centroid choice in
  each connected component of an acyclic finite graph.
- `componentBatch` for any one-vertex-per-component choice. It has exactly
  one vertex per component, selected vertices are connected only when equal,
  every original vertex is connected to a batch member, and the batch is
  nonempty whenever the graph is nonempty.
- `component_halves_after_deleting_centroids`: after deleting the chosen
  centroids and possibly further vertices, each remaining component has at
  most half the size of its actual parent component. The parent is the
  connected-component image under the induced-graph embedding. The proof
  explicitly embeds the child into a component of the parent's graph after
  deleting its own centroid.
- The specialization to deleting exactly the whole centroid batch supplies
  the actual one-layer halving needed for recursive terminal sampling.

The batch theorems are generic in the vertex selection, so they accommodate
smallest-label centroids once that tie-breaking rule is supplied. The
convenience `componentCentroid` uses classical choice rather than prescribing
this algorithmic tie break.

`lake build ForestSampling.ForestCentroid` passes with no warnings in the new
module. All 16 public theorem axiom sets were checked; only `propext`,
`Classical.choice`, and `Quot.sound` occur. No axioms, `sorry`, or `admit` were
introduced.

The actual adaptive `Program`, transport of selected residual vertices to
its commit positions, logarithmic recursion counter, and complete upper
resource theorem remain separate integration steps. This module proves the
graph inputs needed for those steps rather than assuming halving or
separation as an abstract controller invariant.
