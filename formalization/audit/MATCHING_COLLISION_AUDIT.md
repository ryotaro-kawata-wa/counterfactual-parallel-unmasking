# Exposed-edge conditioning audit

`ForestSampling/MatchingCollision.lean` is complete and stable. It imports the proved initial matching-prior module and preserves the existing hard-family representation.

Proved scope:

- `MatchingOn α` represents fixed-point-free involutions on arbitrary labels. `MatchingOn.finEquiv` gives an exact equivalence with the existing `PerfectMatching N` for `α = Fin N`; no base-model rewrite is required.
- Matchings restrict to mate-closed vertex predicates and their complements. Matchings on the two sides glue uniquely.
- For a fixed exposed matching `L`, `MatchingOn.extensionEquiv` identifies the full-matchings event `Extends L` bijectively with matchings on the unexposed vertex subtype.
- For finite uniform distributions, event masses equal relative cardinalities, conditioning on a nonempty event is uniform on that event, and pushforward event masses equal preimage masses.
- The exposed-edge event has positive probability whenever a survivor matching exists. `uniform_conditionOn_extends` proves exact equality between the conditioned full law and uniform survivor matchings pushed forward by gluing `L`.
- `conditioned_mate_probability` proves the exact conditional partner probability `1/(number of survivors - 1)` for two distinct survivor labels. Positivity/nonemptiness assumptions are explicit, and denominator positivity follows from the two distinct labels.

Validation on the pinned Lean/mathlib 4.33.0 environment:

- `lake env lean ForestSampling/MatchingCollision.lean`: passed without warnings.
- `lake build ForestSampling.MatchingCollision`: passed, with inherited linter warnings only.
- All 19 public theorem axiom dependencies were checked: only subsets of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms.

Limits: this proves conditioning on an explicitly specified fixed exposed-edge event. It does not identify a complete adaptive oracle transcript with that event. The greedy exposure process, fixed-subset internal-edge Laplace estimate with constant `1/32`, adaptive collision tail, and manuscript main lower theorem remain separate obligations.
