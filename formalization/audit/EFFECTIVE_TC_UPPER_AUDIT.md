# Actual effective-TC upper bound and mask-event estimates

`FiniteMaskPatterns.lean` and `PathEffectiveTCUpper.lean` are built and frozen.

The public `MaskedInformation.effectiveTC` is the integral of `min(1,t)` times the actual ordered conditional-mutual-information sum of the independently masked target, with q = exp(-t). The underlying finite law and its posterior identification are established in `FiniteMaskedInformation`; continuity and integral measurability are proved in `MaskedInformationContinuity`, not assumed.

For each distinct ordered pair at distance d, the actual conditional MI is at most q² log(2) (1-q)^(d-1). A visible interior vertex makes the actual posterior pair independent (`PathPairSeparation`); every posterior pair has MI at most log(2) by its genuine binary-type emission factorization (`PathPairConditionals`). The probability that all d-1 interior vertices remain masked is exactly (1-q)^(d-1), regardless of dependence in the original source configuration.

The exact finite geometric sum yields total masked information at most 2N q log(2). Integrating its exponential envelope directly gives `effectiveTC ≤ 2N log(2)` for every constructed path of N=n+1 vertices. This proof does not invoke or assume an external `effectiveTC ≤ min(TC,DTC)` comparison.

The generic lower mask-event theorem is also verified: any c lower bound for actual posterior pair MI when all coordinates in a finite background set S are visible contributes at least q² c q^|S| to actual masked CMI. The concrete positive adjacent-edge coefficient and the final linear lower bound are owned by `PathEffectiveTCLower`; they are not claimed by this upper-bound module.

Validation: Lake builds passed. All 14 public theorems in these two modules passed `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, added axiom, or assumed masking identity is present.
