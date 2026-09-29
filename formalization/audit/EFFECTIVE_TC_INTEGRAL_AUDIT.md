# Effective TC integral and uniform constants

`EffectiveTCIntegral` defines exactly the real integral over positive t of
min(1,t) times the information curve. From the actual curve's nonnegativity,
measurability and A exp(-t) envelope it proves integrability and upper bound A.
A B exp(-4t) lower envelope gives B exp(-4)/4 by restricting to [1/2,1].
No convergence assertion is replaced by Lean's zero default for a
nonintegrable Bochner integral: integrability is proved first.

`FiniteInformationContinuity` proves positive finite-law KL, MI and CMI
continuity on an arbitrary topological parameter domain. The actual
`MaskedInformationContinuity` instantiates this on positive time with
q=exp(-t), derives genuine masked-law continuity and measurability, and
sums the actual ordered pair conditional mutual informations.

`MaskedPairIndependence` derives the exact posterior product law for
endpoints in different residual blocks from `ForestConditionals`; it does
not assume conditional independence as a new target property.
`PathAdjacentInformation` derives a positive minimum over the four binary
outer-neighbor tables. Their strict determinant follows from the original
positive J determinant under positive row and column rescaling. Actual
full-vocabulary emissions cancel in MI. The minimum is unchanged when the
background vocabulary size changes while p is held fixed.

`PathBenchmarkMembership` proves benchmarkSignal(N,rho)->0 for fixed rho,
then derives actual path RT/UEN/RF and both exact-oracle accuracy conditions
eventually, uniformly in every positive background size. This closes the
final benchmark-membership sentence of the path proposition independently
of the masking calculation.

`PathEffectiveTCTheorem` combines the actual integrated bounds into explicit
positive constants fixed before N and vocabulary. For N>=6 the lower
constant is c_pair exp(-4)/4 and the upper constant is 2 log(2). This is the
comparison corollary's Theta(N), with no axiom imported from an external
TC/DTC comparison theorem. See the independent final correspondence audit
for the remaining distinction between checked formal statements and TeX
translation review.
