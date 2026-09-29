# Actual masked-information continuity

`ForestSampling/MaskedInformationContinuity.lean` is built and frozen. The module uses the actual independently masked finite target law from `FiniteMaskedInformation`, not an assumed continuous surrogate.

## Verified declarations

- `FinDist.continuous_maskWeight`: continuity of the finite product of masking factors.
- `FinDist.continuous_maskedLaw_mass`: continuity of every atom of the actual masked law.
- `MaskedInformation.continuous_maskedPairLaw_mass`: continuity after the actual pair-observation equivalence.
- `MaskedInformation.continuous_maskedPair_conditionalMutualInformation`: continuity of actual conditional mutual information for `0 < q < 1`, using strict positivity of the masked pair law and the proved finite CMI continuity theorem.
- `MaskedInformation.maskedPairInformation`: the sum over all ordered distinct position pairs, with diagonal terms zero.
- `MaskedInformation.continuous_maskedPairInformation` and `maskedPairInformation_nonneg`.
- `MaskedInformation.informationCurve`: the same sum at `q = exp (-t)` for `t > 0`, extended by zero outside that domain.
- `informationCurve_continuous_restrict`, `informationCurve_continuousOn`, `informationCurve_aestronglyMeasurable`, and `informationCurve_nonneg`.

The measurable conclusion is with respect to Lebesgue measure restricted to `Set.Ioi 0`, the domain used by the effective-TC integral. No continuity at the artificial endpoint extension is claimed or required. The target is a strictly positive finite law; the vocabulary is finite and nonempty. No uniform positivity margin as `t` approaches either endpoint is assumed.

## Validation and scope

`lake build ForestSampling.MaskedInformationContinuity` passed (8729 jobs). Six representative declarations, including both continuity of actual atom masses and the final measurable/nonnegative curve, were checked with `#print axioms`; all depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry` or added axiom is present.

This module supplies actual-law regularity only. Pairwise information bounds, path-geometry counting, and the weighted integral estimate are proved in their separate path modules; they are not inferred from continuity.
