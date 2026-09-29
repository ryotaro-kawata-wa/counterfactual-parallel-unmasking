# Explicit comparison path: verified class inclusion and total correlation

Basis: `appendix_comparison.tex`, proposition `app:prop:path-in-class` and the subsequent effective-TC corollary, in the canonical 2026-09-17 manuscript tree. This is a partial claim map, not a declaration that the full comparison appendix has been formalized.

## Completed finite construction

The new `PathClass` modules construct the actual vocabulary as two distinguished tokens and `B>0` background tokens. With `p=2^(-exponent)` and `exponent>1`, the marginal masses are `1-p`, `p/2`, and `p/(2B)`. The two-type joint table, interaction weights, token transition kernel, detailed balance, stationarity, and positivity are all derived explicitly.

- `FiniteMarkovChain.lean` constructs normalized retained Markov-chain laws by successive finite draws. It proves the exact product density, strict positivity, and every coordinate's stationary marginal.
- `PathGraph.lean` constructs the actual path rooting and proves acyclicity. The generic `Rooting.isAcyclic` proof rules out cycles using a maximal-depth vertex and unique parents. `PathEdge.lean` proves the exact indexed-edge representation and the at-most-one remaining incident edge fact.
- `PathClass.Parameters.model` is an actual `ForestModel`, including the required rooted factorization and endpoint compatibility. No factorization or stationarity premise is assumed.
- `PathRankFrequency.lean` constructs an explicit first-token/second-token/background ranking, proves its monotonicity, and proves finite RF with constant one.
- `PathConditionals.lean` derives the actual complete-boundary row from the symmetric node/edge density by cancelling all nonincident factors. `PathResponse.lean` proves exact TV preservation by the fixed within-type emissions and the response formula, positivity, and RT scalar bound.
- `PathBoundaryResponse.lean` identifies the actual boundary row with that response formula, independently of the revealed source token, and proves actual RT with constant and exponent one.
- `PathNondegenerate.lean` proves that the remaining-neighbor odds are exactly one of the manuscript's three values, then proves actual two-sided UEN with a positive signal independent of path length and background size.
- The exact conditional oracle supplies A2 for every admissible radius.

## Exact TC

`FiniteMarkovInformation.totalCorrelation_law` proves that any positive stationary finite Markov chain has TC equal to the number of edges times its mean transition KL. `PathInformation.lean` cancels token emission factors in that KL, proves the binary information coefficient strictly positive, and proves it unchanged when only `B` changes.

`PathClass.uniform_path_class_and_totalCorrelation` therefore gives a single positive edge signal and a single positive information coefficient, depending only on the exponent, that work simultaneously for every `B>0`, every nonempty path length, and every admissible oracle radius. Its conclusions are actual RT, UEN, constant-one finite RF, exact-oracle A2, and `TC(P)=n*c` for `N=n+1`.

The aggregate module `PathClassMembership.lean` built successfully (8735 build jobs). The exhaustive axiom audit passed all 309 declarations in the new path/chain namespaces and shared helper lemmas. Only `propext`, `Classical.choice`, and `Quot.sound` occur transitively. All new source modules are free of `sorry`, `admit`, and custom axioms.

## Completed DTC extension

`FiniteEntropy.lean`, `MarkovDeletion.lean`, `MarkovEntropy.lean`, and `MarkovDTC.lean` now derive DTC from the actual complementary-coordinate marginals. Deleting an endpoint preserves the stationary chain; deleting an interior coordinate replaces one transition by the actual composed two-step kernel. The retained entropy chain rule then gives the exact DTC identity. `MarkovConditionalInformation.lean` identifies its second coefficient with an expectation of actual positive row KL and proves strict positivity from distinct transition rows.

`PathDTC.lean` cancels the token emissions in this coefficient, proves its independence of background vocabulary size, and proves `DTC(P_N)=c+(N-2)c'`, with both constants positive. `PathComparisonTheorem.uniform_path_class_and_information` combines the full finite class conditions with both exact information identities. `Parameters.information_linear_bounds` supplies explicit two-sided linear inequalities for all lengths at least three.

The aggregate `PathComparisonTheorem.lean` built successfully (8742 jobs). An exhaustive audit of all 1421 project declarations imported by this aggregate passed with only the three standard axioms. The remaining new-module warnings are unused section variables, not proof obligations. These modules are stable and ready for integration.

## Actual conditional-pair bridges completed

`PairConditionals.lean` defines the actual two-coordinate conditional map and proves its strict positivity at masked endpoints. `PathPairConditionals.lean` proves, by actual target-density cross identities and conditional-event sums, that every such pair retains independent within-type emissions. Together with `PathPairInformation.lean`, this gives the vocabulary-independent bound `MI ≤ log 2` for every outside history.

`PairLocalMarkov.lean` proves the exact adjacent-pair posterior when its two outer neighbors are observed. The proof composes two actual target local cross identities and cancels the shared positive interaction; it assumes neither a pair Markov property nor the desired normalized conditional law. The resulting positive weights are `π(a)π(b)g(left,τa)g(τa,τb)g(τb,right)`.

`PathPairSeparation.lean` instantiates the factorization-derived `MaskedPairIndependence.lean` theorem with the two sides of an observed interior path vertex. It proves that the actual posterior pair MI vanishes. `PathInteriorMask.lean` gives the exact number of potential separators, `distance−1`, and bounds actual pair MI by `log 2` times the event that all these vertices remain masked. These modules have built successfully (8733 jobs for the combined upper bridge).

## Effective-TC: actual masking and integration

The independently developed `FiniteMaskedInformation.lean` proves the endpoint-survival identity for the actual independently erased full target, not an abstract information curve. `FiniteMaskPatterns.lean` proves exact probabilities of prescribed visible or masked outside positions. `PathAdjacentInformation.lean` identifies the normalized adjacent token pair with its two-type table, proves all four determinants and mutual informations positive, and defines a positive minimum depending only on `p`.

`PathEffectiveTCLower.lean` combines these facts with the actual pair posterior. Each ordered interior edge contributes at least `c_pair*q^4`; `PathGeometricSums.lean` counts exactly `2*(N−3)` such ordered pairs. Nonnegativity of the other actual conditional-information terms gives the finite sum lower bound. Substituting `q=exp(-t)` and applying the proved integral inequality yields

`effectiveTC(P_N) ≥ 2*(N−3)*c_pair*exp(-4)/4`.

Its `effectiveTC_ge_adjacent` theorem uses the actual information curve's proved measurability and the direct upper envelope from `PathEffectiveTCUpper.lean`. That upper proof uses separator independence and a finite geometric sum to obtain `effectiveTC(P_N) ≤ 2*N*log 2`. Thus no cited external Lemma 16 is needed as an unproved premise. The combined lower source check passed cleanly, the artifact build succeeded (8746 jobs), and all 1473 imported project declarations passed exhaustive axiom inspection with only `propext`, `Classical.choice`, and `Quot.sound`. The final exponent-uniform linear-bounds aggregate is owned separately by the integrating agent.
