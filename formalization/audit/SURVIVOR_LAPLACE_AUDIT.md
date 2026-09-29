# Concrete survivor-fiber Laplace compensation audit

`ForestSampling/SurvivorLaplace.lean` proves the one-commit compensation for
an actual `HardMatching.SurvivorRecord` and an arbitrary batch of original
position labels. Its public endpoints are
`SurvivorRecord.uniform_fiber_commit_compensated` and
`SurvivorRecord.uniform_extensions_commit_compensated`.

For `active = batch \ r.retired`, `k = active.card`, and
`n = N - r.retired.card`, they prove

    E exp(-I.matching.internalEdgeCount(active) + ((k-1 : Nat) : Real)^2 / n / 64) ≤ 1.

The expectation is taken either over the actual uniform compatible-instance
subtype or its full-instance pushforward `r.uniformExtensions`. The only
additional hypothesis is that the compatible fiber is nonempty.

The proof chain is explicit:

1. Restricting a matching to a closed region preserves internal-edge counts
   of subsets within that region.
2. The matching coordinate of the record's actual `fiberEquiv` is precisely
   this restriction. Its internal count on the survivor subtype equals the
   existing integer `PerfectMatching.internalEdgeCount` on active original
   labels. Subtype and original-label cardinalities are also identified.
3. `SurvivorQuery.uniform_fiber_map_matching` identifies the actual survivor
   matching marginal as uniform. Finite expectation change of variables
   transports the matching Laplace theorem to the compatible record fiber.
4. The already proved constant-32 uniform matching estimate at parameter one,
   together with `1 - exp(-1) ≥ 1/2`, pays for the constant-64 compensation.
5. If the survivor cardinality is at most one, `k ≤ n ≤ 1` makes the natural
   subtraction `k-1` zero. Nonnegative internal counts then bound the
   transform by one directly, including `n=0` without dividing by an
   unproved-positive denominator.

`lake build ForestSampling.SurvivorLaplace` passes with no warnings in the
new module. All 8 public theorems were checked with `#print axioms`; only
`propext`, `Classical.choice`, and `Quot.sound` occur. No axioms, `sorry`, or
`admit` were introduced.

This establishes the concrete one-step input. The actual adaptive Program
induction, prefix disintegration, compensated terminal ledger, and final
collision-tail conversion are separate integration modules; no claim of
those full results is made by this module alone.
