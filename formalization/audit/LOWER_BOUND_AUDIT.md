# Lower-bound audit and proof architecture

Audit date: 2026-09-26. Source baseline: `1507791fd7c1137c77ec139cc0b73b5765f1464b` (the arXiv-format branch). The canonical manuscript root below is `manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/`. This is a source-level mathematical and specification audit, not a certification that the lower bound is formalized. Environment reproduction is tracked separately.

## Finding summary

1. **Confirmed specification drift.** `MatchingLowerParameters.finite_separation`, `lowerValue`, and `FiniteAdaptiveLowerBound` still describe the former linear result: `N λ² ≤ 1`, `N λ²/(768 R)`, and `R ≤ N/8`. The current manuscript instead claims `¼ (1 - exp(-N λ²/(98304 R)))`, without the separation hypothesis, for `Q ≤ K/8` and `1 ≤ R ≤ N/16384`. See [old Lean statement](../ForestSampling/PaperStatements.lean#L89) and [current theorem](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/appendix_results.tex#L120).
2. **Confirmed proof-coverage gap.** The principal lower-bound declarations are propositions (`def ... : Prop`), not proved theorems. The existing hard-family construction, conditioning calculations, and oracle accuracy estimates are useful proof code, but there is no implemented adaptive midpoint process, instance prior, survivor invariant, disclosure theorem, collision Laplace theorem, or minimax lower theorem in the baseline.
3. **No confirmed counterexample found in the inspected compiled mathematical chain.** In particular, the active survivor proof explicitly accounts for the normalization of the midpoint kernel. This audit does not assert the chain is correct: the principal remaining work is to formalize the probabilistic interfaces and the connection to actual sampler executions.
4. **Measurability interface needs care.** Lean currently assumes measurability of seedwise TV only. That does not by itself imply measurability of seedwise Hellinger loss. The manuscript invokes Tonelli while displaying both losses. This can be avoided without strengthening the theorem: derive the prior-averaged TV bound at each fixed seed first, and then integrate the finite weighted sum of measurable TV risks. This is a formalization-interface issue, not a demonstrated false lower bound.
5. **Real infima require nonemptiness and bounds.** Before passing to `InstanceFamily.minimax`, prove that the hard family is nonempty and that budgeted samplers exist for `R ≥ 1`. Lean's `sInf` on `ℝ` does not encode `inf ∅ = +∞`; missing these side conditions could silently change the mathematical convention.

## Evidence-linked dependency map

| Result / role | Manuscript evidence | Existing Lean coverage | Remaining obligation |
| --- | --- | --- | --- |
| Hard marginal, edge law, selected oracle | [definition](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/appendix_results.tex#L19), [local facts](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_family.tex#L48) | `HardLocalParameters.commonMarginal`, `endpointKernel`, `edgeLaw`, `HardMatching.target`, `model`, `selectedOracle`, `exactRowCharacterization`; `selectedOracle_accurate_of_exactRowCharacterization` | Package an unconditional accuracy theorem using the already-proved exact-row characterization. Prove directed response, common edge loss, and full family inclusion. |
| Edge penalty `λ²/12 ≤ d ≤ λ²/2` | [one-edge calculation](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_family.tex#L190) | Feature moments, positivity, generic chi-square upper estimate already exist | Prove ratio bounds `[1/2,2]`, edge chi-square `λ²`, Hellinger lower bound, and independence of private trigger labels. |
| Exact adaptive execution ends in target law | [midpoint proof, steps 1–2](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_midpoint.tex#L191) | `Program.eval` evaluates only the oracle product sampler; history extension and exact conditional distributions exist | Define exact batch execution using the same decision tree. Prove replay uniqueness, terminal partition/exhaustion, and telescoping of exact conditional masses. |
| Adaptive midpoint identity | [statement](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_midpoint.tex#L162), [normalization and affinity calculation](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_midpoint.tex#L233) | `FinDist.affinity`, `bind`, finite product affinity, distance comparisons | Construct normalized geometric-mean kernels, finite dependent execution law, and accumulated local-affinity weight. Preserve histories/paths until the injective output projection has been proved. |
| Product-uniform survivor posterior | [active statement/proof](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_invariant.tex#L202) | `PerfectMatching` as fixed-point-free involution and product target; no random matching or analytic record | Define uniform matching/triggers, whole-edge retirement, failed-candidate sets, augmented analytic history, conditional law on positive atoms, and one-step posterior invariance. |
| Query disclosure `E D ≤ NQ/K` | [statement and proof](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_invariant.tex#L1247) | None specific | Prove conditional hazard at the adaptive kth query, recurrence `p_k-p_(k-1) ≤ (1-p_(k-1))/(K-k+1)`, induction `p_k ≤ k/K`, and edge-to-hit counting. |
| Pathwise ledger | [edge counting](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_collisions.tex#L37) | Involution representation can support counting; no ledger | Every edge retires exactly once. Batch touching count is `k-z`; derive active excess ≥ `N/2-D-R`. |
| Uniform-matching Laplace estimate | [lemma](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_matching_laplace.tex#L22) | None specific | Uniform-mate count via matching-completion equivalence; adaptive exposure law; one-step Bernoulli Laplace factor; iteration; floor inequalities. |
| Collision lower tail | [proposition](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_collision_tail.tex#L25) | Generic real algebra only | Derive `E exp(-Z_t + A_t/64) ≤ 1` conditionally, iterate across finite histories, use ledger/Cauchy–Schwarz and Markov. |
| Collision affinity | [lemma](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_affinity.tex#L27) | `affinity_piProduct`, `sqHellinger_le_tv` already proved | Edge-block equivalence for batch coordinates; exact conditional and oracle-product factorization; local affinity ≤ `(1-d)^z`; midpoint identity. |
| Nonlinear minimax bound and target-error tradeoff | [proof](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/lower_nonlinear.tex#L20) | Only the obsolete linear statement and algebraic linear consequence | Tail-to-penalty expectation; exponential monotonicity; finite prior average ≤ worst case; measurable seed integration; infimum lower bound; nonlinear scalar corollary. |

Dependency spine:

```text
local hard law → edge loss ────────────────────────────────┐
exact adaptive law → normalized midpoint → affinity ──────┤
                         ↓                               │
uniform prior → survivor invariant → query disclosure ─┐  │
                     ↓                                 │  │
uniform matching Laplace → conditional Laplace ────────┤  │
pathwise edge ledger ──────────────────────────────────┤  │
                                                     ↓  ↓
                           collision lower tail → nonlinear seedwise loss
                                                        ↓
                          finite prior + seed integration → minimax
                                                        ↓
                                         target-error / rate corollaries
```

## Specific logical checks and cautions

### Midpoint identity

The identity is exact only because the complete output identifies its adaptive path once the instance and decision-rule seed are fixed. A generic `bind` merges paths, so it does **not** admit an equality between output affinity and the expectation of local-affinity products without an injectivity/separation condition. With an arbitrary output map, data processing gives affinity in the opposite (larger) direction. Therefore prove the identity first on a retained path type, then transfer through a proved equivalence to complete configurations. The manuscript's replay argument at `lower_midpoint.tex:193–211` is precisely the missing bridge.

Strict positivity establishes positive local affinity and equal support, and finite pathwise budgets transfer to the midpoint process. The all-mask preprocessing reply is fixed across hard instances (common marginal), so it does not disturb the initial instance prior. It must still be represented in the sampler-to-process bridge.

### Survivor invariant

Only the blue compiled proof at `lower_invariant.tex:224–732` is the current proof. Lines 737–1225 are within `\iffalse` and must not be counted as a second live theorem.

The crucial pre-observation support assertion is at lines 329–428: fixing the newly retired whole edges and both endpoint triggers reconstructs a unique old survivor configuration from each proposed new survivor. In the query case, all surviving hit bits are zero and failed candidates are removed. In the commit case, surviving vertices are disjoint from the selected batch. Thus the allowed support is a Cartesian product, with no remaining matching-dependent retirement test.

The potentially dangerous global midpoint normalizer is explicitly factorized edgewise at lines 539–605. Every surviving edge contributes the unit factor on an empty coordinate set. All nonunit factors concern edges already in the analytic retirement record, so the observation likelihood does not weight survivor configurations differently. This is the essential fact to mechanize; conditioning under the actual product sampler would not be a substitute.

A practical formalization can use finite conditional masses on atoms rather than general sigma-field conditional expectations: for fixed seed, there are finitely many instances, sampled values, and bounded operations. Oracle rows may be real-valued but only finitely many are reachable under that finite instance family. Arbitrary-seed integration is needed only after the fixed-seed theorem.

### Disclosure

The correct hazard is `1/(K-k+1)` at query index `k`, not `1/K` conditionally after failures. The proof recovers the unconditional `Q/K` bound from the recurrence, which is valid even when a mate hit, commit, or early termination stops future tests. The only independence required is the conditional product-uniform invariant; query events and different vertices need not be independent.

### Matching exposure and tail constants

For `k ≥ 4`, the paper exposes `m=floor(k/4)` edges starting in `A`, with `|A|=floor(k/2)`, `|B|=ceil(k/2)`. At exposure `j`, at least two `A` vertices remain and at least `k/4` `B` vertices remain, so success probability is at least `k/(4n)`. Distinct successful exposures contribute internal edges, and `m ≥ k/8` yields the factor `1/32`. The small cases `k=0,1,2,3` are handled separately. No independent-edge assumption appears in this argument.

At the tail stage, `E D ≤ N/8` gives `P(D ≤ N/4) ≥ 1/2`. The ledger and `R ≤ N/8` give active excess at least `N/8`; Cauchy–Schwarz then gives `Σ A_t ≥ N/(64R)`. Exponential compensation yields threshold `x=N/(8192R)` and tail at least `1/2-exp(-x)`. Finally `R ≤ N/16384` implies `x ≥ 2`, hence a lower bound `1/4`. These constants and inequality directions match in the inspected proof. This is an arithmetic check, not a Lean proof of the process.

### Minimax semantics and quantifier order

The same seed distribution and sampler are chosen before the instance. The prior on matching/triggers is independent of the seed. Prove a lower bound for the prior average **for every seed**, convert Hellinger to TV pointwise, then integrate over seeds. Select a worst-case instance only after seed integration. Choosing an instance separately for each seed would establish a different and insufficient statement.

For the Lean `sSup`/`sInf` definitions establish:

- a nonempty finite type of matchings for even `N` and trigger assignments for `K ≥ 1`;
- risk in `[0,1]`, giving boundedness above and below;
- an all-at-once sampler with `Q=0,R=1` and constant seed, giving budget-class nonemptiness for `R ≥ 1`;
- finite averaging bounded by the nonempty worst-case supremum;
- lower bounds preserved by the nonempty real infimum.

The finite hard-family condition permits `N=0`, but the main implication's budget hypotheses `1 ≤ R ≤ N/16384` exclude it. The finite target-error corollary should separately account for zero rounds/zero length if implemented outside the theorem's positive-budget context.

## Proposed Lean module architecture

1. `CurrentStatements.lean`: current scalar assumptions without `finite_separation`, nonlinear value, explicit family specialization, and clearly labeled unproved principal propositions. Preserve old interfaces until migration is deliberate.
2. `AdaptiveMidpoint.lean`: `FinDist.affinity_pos`, normalized midpoint distribution, dependent sigma-product distribution, two-step affinity chain, and finite-tree path identity. State any sampler reconstruction hypotheses explicitly; a generic algebraic identity alone does not certify the paper theorem.
3. `HardEdgeDistance.lean`: ratio and chi-square identities, Hellinger lower/upper bounds, equality across trigger assignments. This has no adaptive-process dependencies.
4. `MatchingCombinatorics.lean`: finite matching type/cardinality, existence, restriction/extension equivalences, uniform-mate theorem, active-batch edge ledger.
5. `SurvivorProcess.lean`: finite analytic record and one-operation conditional invariant, using retirement-support equivalence plus observation likelihood invariance.
6. `QueryDisclosure.lean`: scalar recurrence first, then connect it to query stopping histories and retired-edge counting.
7. `MatchingCollision.lean`: bounded adaptive Bernoulli exposure transform, matching instantiation, finite conditional Laplace iteration, collision tail.
8. `NonlinearLower.lean`: edge penalty + midpoint + collision tail, followed by the finite-prior/measurable-seed/minimax bridge and target-error corollary.

Priority for the next implementation chunk: normalized finite midpoint and a dependent sigma affinity identity. The result is reusable for both lower and upper arguments, isolates a real mathematical step, and can be compiled without pretending the unimplemented survivor process is an assumption-free theorem.

## Implementation completed after the baseline audit

`ForestSampling/AdaptiveMidpoint.lean` now implements and proves:

- `FinDist.affinity_pos`, `midpoint`, `midpoint_strictlyPositive`, and `midpoint_factorization`;
- `FinDist.sigmaJoint`, its positivity theorem, the exact `affinity_sigmaJoint` chain rule, and `adaptive_midpoint_two_step`;
- invariance of affinity and squared Hellinger distance under a bijective relabeling;
- `MidpointTree`, whose finite branch sizes and subtrees may depend on prior outcomes and whose leaves permit different terminal path lengths;
- `MidpointTree.path_mass_factorization`, `affinity_eq_midpoint_expectation`, and `sqHellinger_eq_midpoint_loss` for the entire adaptive tree;
- `output_sqHellinger_eq_midpoint_loss`, which transfers the identity to an output space when an explicit path/output equivalence is supplied.

Validation: `lake build ForestSampling.AdaptiveMidpoint` succeeds with the pinned Lean 4.33.0/mathlib environment. The module contains no `sorry`, `admit`, or custom `axiom`. This checks the full abstract finite-tree midpoint identity, not only a two-step algebraic special case.

`#print axioms` was run for the two-step identity, pointwise tree factorization, full tree affinity identity, and output-transport loss identity. Each reports exactly `[propext, Classical.choice, Quot.sound]`; none depends on `sorryAx` or a paper-specific axiom.

**Still missing:** conversion of the actual `Program` and hard-family conditional kernels to this tree, the replay equivalence for complete configurations, the instance prior and survivor invariant, query disclosure, matching/collision concentration, and the connection to the nonlinear minimax proposition. The existence of a generic midpoint theorem is not evidence that these remaining obligations have been discharged. The coverage table above describes the original baseline; this section records the subsequent verified extension.

### Actual sampler bridge completed subsequently

`ForestSampling/ProgramMidpoint.lean` now connects the identity to the actual sampler interface. Rather than translating batches to the numbered abstract tree, it retains a dependent finite path type directly from `Program`: queries follow the fixed oracle's unique reply branch, and commits retain the batch assignment together with the child path.

The module proves output agreement with the initial history, output replay, output injectivity, and `Program.retainedOutputEquiv` from empty-history paths to complete configurations. The equivalence is constructed and proved, not assumed. It also proves `retainedPath_withinBudgets`, transferring both original counters to every retained path, including those sampled by the analytic midpoint law.

`retainedOutputLaw_ofOracle` recovers the original `Program.eval`. `retainedOutputLaw_ofTarget` recovers `Program.evalJointReference` from `ExactReference.lean`; the latter's independently proved exact-target theorem identifies the comparison output with the target. Thus `Sampler.adaptive_midpoint_identity` now states the actual paper-level fixed-seed identity:

```text
1 - sqHellinger M.target (A.outputLaw w O)
  = sum path, A.midpointPathLaw M w O path * A.midpointPathWeight M w O path.
```

The midpoint law uses the true joint conditional and the oracle-product law at each selected batch; preprocessing and all later queries use the same frozen oracle. This holds for any positive target and any actual `Sampler`, without hard-family, accuracy, safety, or budget hypotheses; budgets are available through the separate pathwise transfer lemma.

Validation: `lake build ForestSampling.ProgramMidpoint` succeeds (8713 jobs), with no warnings introduced by this module. It contains no `sorry`, `admit`, or custom axiom. The remaining lower-bound obligations are now the instance prior/survivor law, disclosure and matching concentration instantiated to those paths, edgewise collision penalties, and the final nonlinear/minimax assembly. The earlier paragraph's missing Program/replay bridge has been discharged by this subsequent module.

The checked axioms of `Program.retainedOutputEquiv`, `Program.retainedPath_withinBudgets`, `Program.target_output_sqHellinger_eq_midpoint_loss`, and `Sampler.adaptive_midpoint_identity` are exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or custom assumption.
## Actual collision-affinity bridge added

`ForestSampling/HardCollisionAffinity.lean` proves the local and pathwise penalty for the actual laws, without assuming a survivor invariant or a batch-factorization conclusion. `PerfectMatching.BatchEdge M batch` consists exactly of matching edges whose two endpoints belong to the chosen batch. A deterministic projection retains just those endpoint pairs. `jointBatchLaw_map_batchPairs` proves that the conditioned hard target projects to the independent product of their correlated edge laws; freshness ensures that the old history imposes no constraint on these edges. `commitDistribution_map_batchPairs` proves that the selected oracle projects to independent common-marginal pairs, since both endpoints and their mates are masked. The needed product-restriction, coordinatewise-conditioning, regrouping, and affinity data-processing facts are also proved in this module.

`jointBatch_affinity_le_one_sub_loss_pow` bounds the actual batch affinity by `(1−d)^card(BatchEdge)`, where `d` is the actual one-edge squared Hellinger loss. `Program.retainedMatchingCollisionCount` counts the actual internal edges along the program's chosen batches, and `retainedAffinityWeight_le_edgeAffinity_pow` multiplies the local bound through every query and commit branch. Finally `midpointPathWeight_le_exp_collisions` instantiates the result to the existing sampler midpoint weight and gives `weight ≤ exp(−λ² C/12)`, using the already-checked hard-edge lower loss. This completes the pointwise penalty input for the nonlinear lower bound. The remaining probabilistic task is to prove that sufficiently many such collisions occur under the actual instance–midpoint joint law; this module does not assert that tail or the adaptive survivor invariant.

Validation: `lake build ForestSampling.HardCollisionAffinity` passed (8717 jobs; imported baseline warnings only). The file has 472 lines and no `sorry`, `admit`, or custom `axiom`. `#print axioms` for both projection identities, the local loss-power inequality, the retained-path inequality, and the sampler exponential corollary returns only `propext`, `Classical.choice`, and `Quot.sound`.

## Concrete survivor-record and one-step posterior work

`HardRestriction.lean` proves locality for the actual hard target, selected oracle, and normalized midpoint kernel. For two instances agreeing on a mate-closed retired region, exact observation likelihoods supported in that region coincide. Taking ratios for the old and batch-appended history proves equality of the full joint batch laws; selected product rows and their normalized geometric midpoint then also coincide. The complete counterfactual reply coincides whenever all endpoints outside the region miss their tested triggers, and the all-mask preprocessing reply is the common marginal for every hard instance. These are proved equalities, not assumed factorization properties.

`SurvivorProcess.lean` defines a finite record containing only the retired matching, both retired triggers, and candidate sets. `fiberEquiv` constructs the exact bijection between compatible full instances and survivor matching × remaining candidate assignments. Actual query/commit updates retire entire touched edges and record their real triggers. `queryUpdate_eq_iff` and `commitUpdate_eq_iff` prove that the preimage of an actual retirement record is its entire compatible fiber; compatibility with the old record is preserved backward. `uniform_queryRetirementPosterior` and `uniform_commitRetirementPosterior` then normalize the real retirement event under the old uniform fiber. Finally `commitObservation_posterior` proves that actual midpoint commit values do not alter the newly uniform fiber: all the actual normalized kernels on that fiber are equal, their observation likelihoods are positive, and Bayes normalization is checked explicitly.

Scope boundary: these results establish the concrete record support and the normalized one-step survivor mechanism. The theorem identifying the posterior at every actual adaptive prefix under `HardMidpoint.midpointJoint` is still missing, as are its query-ordinal hazard integration and the resulting `E D ≤ NQ/K`. A uniform starting fiber in a one-step lemma is not being counted as a proof that arbitrary adaptive prefixes have that law. Builds: `HardRestriction` (8720 jobs) and `SurvivorProcess` (8721 jobs) passed with no new warnings; source sizes are 250 and 651 lines respectively.

## Actual adaptive survivor invariant and exact disclosure integration completed

The previous section's one-step scope boundary has now been discharged. `SurvivorQuery.lean` proves the uniform surviving-matching marginal, independent uniform candidate marginals, and the exact reciprocal-candidate query hazard from the explicit `fiberEquiv`. `SurvivorPosterior.lean` then defines coherent finite prefixes using the actual `Program` constructors and the already defined `Program.retirementTrace`. Its `eventMass_eq_likelihood` proves that the actual retained midpoint probability of every such prefix is a common strictly positive scalar on the final compatible fiber and is zero outside it. This is an induction over actual queries and commit values, using proved full-reply equality and equality of the actual normalized midpoint kernels. `ofPath`, `observations_ofPath`, and `queryCount_ofPath_le` show that every finite prefix of every actual retained execution is covered; no reachability or replay hypothesis is assumed.

`MidpointSurvivor.lean` transports this result to the actual `NonlinearMatchingParameters.midpointJoint`, including the proved common all-mask preprocessing reply. `midpointPrefix_posterior` identifies the exact conditional hidden-instance law with the uniform full compatible fiber. `midpointPrefix_hit_probability_le` proves the actual conditional trigger-hit hazard `1/(K−q)` after `q` preceding extra queries, with `midpointPrefix_candidate_card` deriving the candidate lower bound from the actual prefix. These are distribution identities and actual conditioned-event probabilities, not an abstract invariant supplied as an assumption. Builds of `SurvivorPosterior` (8729 jobs) and `MidpointSurvivor` (8733 jobs) passed. Axiom checks for the prefix likelihood, actual-path coverage, actual joint posterior, and conditional hit hazard return only `propext`, `Classical.choice`, and `Quot.sound`.

`SurvivorDisclosure.lean` proves the integrated exact `Q/K` estimate by a finite potential argument on the actual execution. `uniform_expected_queryHits_le` bounds the number of hit sources by the surviving count divided by the tracked candidate minimum. `queryUpdate_card_bounds` proves that the real retirement increment lies between the hit count and twice that count. The potential is `2·n·q/m`, with `n` surviving vertices, `q` remaining queries, and candidate minimum `m`. At a query it uses the reduction of the surviving count, not the coarser sum of reciprocal hazards, so the final constant is exactly `2NQ/K` for query-retired vertices. The query and commit induction steps disintegrate the complete finite fibers using their proved equivalences and actual reply/kernel locality. `disclosureEval_eq_retained_expectation` connects the recursion to the existing actual retirement ledger; `uniformDisclosureEval_le` is proved, not a postulated supermartingale condition. This module built successfully (8736 jobs).

The global budget hypothesis in this integration is `Program.WithinOracleBudgets` for each compatible instance's actual frozen oracle. It does **not** require the older, stronger universal-arbitrary-reply `WithinBudgets`. `DisclosureTransport.lean` uses the existing common-initial-program and initial-fiber equivalences to state the actual joint mean bound `midpointLedger_queryVertices_expectation_le`; its `midpointLedger_disclosure_le_eighth` gives `E(queryVertices/2)≤N/8` under `Q≤K/8`, exactly the input requested by `OracleLowerReduction.lowerValue_le_oracleMinimax_of_disclosure`. Thus the remaining final lower-theorem assembly can use the manuscript's actual family-oracle minimax class rather than silently retaining the narrower legacy class. Final aggregate theorem/build status should be read from the root-owned current coverage report; this audit does not relabel other unformalized paper claims as proved.

Final validation of this extension: `lake build ForestSampling.DisclosureTransport` passed (8743 jobs; imported and minor linter warnings only). `#print axioms` for `uniform_query_potential_le`, `uniformDisclosureEval_le`, `midpointLedger_queryVertices_expectation_le`, and `midpointLedger_disclosure_le_eighth` each returns exactly `[propext, Classical.choice, Quot.sound]`. No custom axiom or `sorryAx` occurs. These checks supplement the separately checked posterior identities above.

## Concrete finite class inclusion and signal calibration completed

`HardFamilyInclusion.lean` now proves the actual complete-boundary row formula on matching edges, independence from a nonmatched source, `directedResponse_eq_coupling`, `model_edgeNondegenerate`, and `model_tailResponseRegular`. It uses the already proved exact conditional characterization and local endpoint TV response, not an assumed conditional Markov or response property. The explicit positivity/factorization/forest structure was already contained in the constructed `HardMatching.model`. The signal positivity and radius-domain hypotheses required by the typed RT/UEN/A2 interfaces are exactly the public domains stated in `appendix_setup.tex:225,357`; they are not new restrictions. Precision: `λ²θ` bounds squared Hellinger row error, while the actual TV error in the nontrigger branch is `λθ`.

Combining these theorems with the root-owned actual bank-first marginal ordering and RF proof in `HardRankFrequency.lean`, `HardClassMembership.lean` proves the existing full `FiniteHardFamilyIncluded` specification. The current parameter-object theorem is `NonlinearMatchingParameters.hardFamily_finiteIncluded`; its ranking is constructed by `hardFamilyRanking`. This is finite class membership and deliberately does not absorb the separate public vocabulary-growth assumption.

`HardFiniteCalibration.lean` constructs `K=⌊signal^(−1/exponent)⌋₊` and proves its nonemptiness, strict vocabulary inclusion, `K·signal<1`, and the RF parameter inequality `signal≤K^(−exponent)` at actual finite public values. `signalCalibratedParameters` sets both trigger mass and coupling to the public signal and fills every validity field from these proofs. `signalCalibratedParameters_finiteIncluded` then certifies all RT/UEN/RF/A2 requirements under the manuscript's finite spread and cubic oracle-budget conditions.

`CalibratedLowerBound.lean` applies the actual admissible-algorithm lower theorem to this witness. `signalCalibrated_target_error_alternative` proves the printed real thresholds `Q>K/8` or `R≥min{N/16384,N·signal²/(786432ε)}`, explicitly converting the earlier natural floor-division branches. `benchmarkSignal_cube` proves the exact benchmark cube `radius²/(8N)`, and `benchmarkSignal_bounds` verifies the positive/half-signal domain and cubic A2 allowance.

Validation: `HardFamilyInclusion` built (8724 jobs), `HardFiniteCalibration` built (8725), `CalibratedLowerBound` built (8758), and `HardClassMembership` built (8727). None contains `sorry`, `admit`, or a custom axiom. These finite consequences currently quantify over the explicitly constructed witness's actual-oracle budget class. A fully packaged public-class corollary additionally restricts the public uniform guarantees to this proved contained family, and transports vocabulary labels if the public type is represented differently. Fixed-accuracy growth limits and the optional independent-signal asymptotics remain separate obligations.

## Main and fixed-accuracy lower calibration completed

`LowerAsymptotics.lean` constructs the actual benchmark parameter object with signal `σ = (1/2)(radius²/N)^(1/3)`, rather than assuming the bank or power scales. It proves the exact query and round power identities, removes `K = floor(σ^(-1/α))` at a factor-two cost, and certifies all RT/UEN/RF/A2 clauses via `benchmarkParameters_finiteIncluded`. `benchmark_target_error_power_alternative` gives the actual finite independent-radius alternative with query threshold `2^(1/α)(N/radius²)^(1/(3α))/16` and round threshold `min{N/16384, N^(1/3) radius^(4/3)/(3145728 ε)}`. After `radius=ε/2`, `main_target_error_power_alternative` proves `Q > (N/ε²)^(1/(3α))/16` or `R ≥ N^(1/3) ε^(1/3)/12582912` for every even `N≥1`, `α>1`, `0<ε≤1/8`, and strict public spread `Vσ>1`. The finite minimum can be removed already at every such `N` in this single-accuracy specialization.

`LowerVocabularyGrowth.lean` proves the remaining vocabulary condition from the literal sequence representation `V_N = N^(ν + error_N)` eventually, with `error_N → 0` and `ν>1/3`. It derives an eventual lower power bound using the positive gap above one third and then proves `V_N σ_N>1`. It also removes the independent-radius round minimum by a genuine `atTop` argument at fixed positive budgets. The theorems `main_target_error_power_alternative_eventually` and `benchmark_target_error_power_alternative_eventually` cover every even length in the resulting tail and every actual-family oracle-budgeted sampler at that length, with the displayed constants. These are explicit uniform per-length alternatives; no assertion is made that an arbitrary sequence cannot alternate which resource branch is large.

Validation: `LowerAsymptotics` built successfully (8761 jobs; 195 lines) and `LowerVocabularyGrowth` built successfully (8762 jobs; 160 lines), with no new warnings. Axiom checks for benchmark inclusion, both finite alternatives, actual vocabulary-growth implication, and both eventual alternatives return only `[propext, Classical.choice, Quot.sound]`. The previously checked finite inclusion/calibration key theorems also have exactly these standard dependencies. Both modules are frozen after these checks. The remaining packaging obligation is restriction of a uniform public-class sampler to this now-proved contained family; that is being isolated in `PublicClassLower.lean`. Optional independent-signal exponent tradeoffs are not claimed by these benchmark-specialization results.

## Public-class restriction and final calibrated lower wrappers completed

`PublicClassLower.lean` now closes the restriction obligation above on the same public vocabulary labeling. `HellingerPublicClass` quantifies over arbitrary typed forest targets and arbitrary frozen oracles satisfying actual RT(1,1), UEN at the public signal, RF with an existential marginal ranking and constant 1, and A2 at the public radius. `hellingerPublicFamily` is the entire subtype of such target/oracle pairs, not the matching family. `RandomizedSamplerData.HellingerPublicAdmissible` uses each instance's actual frozen-oracle path budgets and seed-risk measurability. `hellingerPublicRisk` is the existing supremum of the unchanged seed-averaged TV risk over this whole public subtype.

`uniformHellingerGuarantee_of_publicRisk` converts the public supremum bound to per-instance guarantees using proved risk boundedness. The actual `UniformHellingerGuarantee.restrict` preserves the sampler and seed law and constructs its finite actual-oracle budgeted subtype using `benchmarkParameters_finiteIncluded`; membership is therefore proved, rather than a new hypothesis. `restrictedRisk_le` supplies the finite family's risk bound. `main_public_class_lower` and `main_public_class_lower_eventually` then give the main explicit Q/R powers for public-class guarantees; `benchmark_public_class_lower` and `benchmark_public_class_lower_eventually` give the corresponding independent-radius finite and fixed-accuracy statements.

Validation: `lake build ForestSampling.PublicClassLower` passed (8763 jobs; 211 lines), with no new warnings. All six key axiom checks, including both public supremum restriction results and all four public lower wrappers, return only `[propext, Classical.choice, Quot.sound]`. The file is frozen after these checks. The vocabulary is explicitly `HardVocabulary K (V−K)`, whose cardinality is proved to equal the public `V`; transporting the whole sampler/oracle interface to an arbitrary separately supplied token type of that cardinality is not included. The calibrated rates are uniform per-length resource alternatives, as recorded above. No manuscript changes were made.

## Commit-row observation correspondence corrected

A subsequent source audit found a real formal-interface mismatch: the manuscript's ordinary commit observation (`appendix_setup.tex`, around line 548) contains the selected probability rows as well as the sampled values. The original `Program.commit` continuation only received the values. Consequently, the earlier lower wrappers alone quantified over a narrower controller class; proving actual-oracle budgets did not repair this separate issue. This is a formalization correspondence gap, not an identified error in the manuscript's mathematical lower-bound argument.

`ObservedProgram.lean` now represents the full observation explicitly: the batch is chosen before a continuation receives its probability rows and sampled values. Its compiler inserts a read-only query at exactly the current commit state, followed immediately by that already chosen batch. It forwards only the batch rows to the observed controller. `ObservedProgram.eval_compile` and `RandomizedObservedSamplerData.risk_compile` prove exact output-law and seed-risk preservation for every frozen oracle.

The inserted readout is **not charged as an additional probe**. The independently checked `FreeMarginalBudgets.lean`, `FreeMarginalDisclosure.lean`, and `FreeMarginalLower.lean` establish the lower bound in a stronger model allowing every current-commit-state row query for free. In the actual survivor process such a query has no new trigger hits; the revised disclosure proof tracks unchanged survivor candidates and retired support without incorrectly requiring equality of candidate sets on already retired vertices. `ObservedSimulation.lean` proves that every observed controller with ordinary Q/R budgets compiles to this stronger model with exactly the same Q/R budgets. `ObservedEmbedding.lean` also proves observed feasible-class nonemptiness whenever R is positive.

`ObservedLower.lean` supplies `NonlinearMatchingParameters.lowerValue_le_observedMinimax`, `observed_target_error_alternative`, and `main_observed_target_error_power_alternative`. These cover arbitrary randomized full-observation controllers with each actual oracle's pathwise budgets and measurable seed risk. `ObservedPublicClassLower.lean` proves `main_observed_public_class_lower` and `main_observed_public_class_lower_eventually`: a uniform guarantee over the entire public RT/UEN/RF/A2 class restricts to the actually constructed contained hard family and gives the explicit main resource alternative. The final main-lower correspondence claim should use these observed-controller wrappers, rather than the narrower earlier `Program` wrappers.

Validation: `ObservedProgram` built (8716 jobs), `ObservedSimulation` (8718), `ObservedEmbedding`, `ObservedLower` (8768), and `ObservedPublicClassLower` (8771). All nine key axiom checks—including the simulation, exact risk preservation, preserved budgets, nonemptiness, observed minimax theorem, calibrated power bound, and both public wrappers—report exactly `[propext, Classical.choice, Quot.sound]`. No custom axiom or unfinished proof is used. These five modules are frozen after these checks. They currently retain the canonical `HardVocabulary K (V−K)` labeling; explicit transport of the entire model/oracle/controller interface to an arbitrary token type of the same cardinality remains a separate representation obligation.

## Arbitrary public vocabulary transport completed

The canonical-label scope boundary in the preceding sections is now discharged for arbitrary finite nonempty public token types. `VocabularyEquivalence.lean` constructs pointwise configuration, history, masked-state, and frozen-oracle transport under a public token bijection. It proves that committed and masked coordinate sets are unchanged, that actual commit feedback and independent commit distributions transport exactly, and that TV is invariant. The actual batch laws are proved product pushforwards, not replaced by assumed equivalent laws.

`ObservedVocabularyTransport.lean` recursively relabels the full observed program. It translates every query response and every commit-row feedback/value pair back into the original controller's labels before invoking its continuation, without adding operations or changing a chosen batch. `ObservedProgram.eval_relabel` and `withinOracleBudgets_relabel` prove exact output-law transport and unchanged actual-oracle Q/R budgets. `ObservedSampler.outputLaw_relabel_symm` includes the free initial all-mask reply. The randomized transport retains the identical seed probability space; `risk_relabel_symm` and `riskMeasurableAt_relabel_symm_iff` derive risk equality and unchanged measurability from pointwise TV equality.

The independently implemented `VocabularyModelTransport.lean` constructs the transported forest model and proves actual RT, UEN, RF, Hellinger accuracy, and forward-KL accuracy invariance. Its `samplingInstance` changes the model and oracle together, and `publicClass` proves that the corresponding arbitrary-label instance belongs to the same public class. `ArbitraryVocabularyLower.lean` then constructs the token equivalence from the proved hard-witness cardinality and applies these results to an arbitrary observed controller on the user's public vocabulary. The final finite theorem is `main_observed_public_class_lower_any_vocabulary`; the literal-growth tail theorem is `main_observed_public_class_lower_any_vocabulary_eventually`. Their conclusion remains the explicit uniform per-length alternative `Q > (N/ε²)^(1/(3α))/16` or `R ≥ N^(1/3) ε^(1/3)/12582912`, with the same finite spread, even-length, exponent, and small-accuracy hypotheses already stated above.

Validation: `VocabularyEquivalence` built (8717 jobs), `ObservedVocabularyTransport` (8718), and the aggregate `ArbitraryVocabularyLower` built (8776). These owned modules are frozen. The statements use arbitrary `V : Type` (and arbitrary probability spaces `Seed : Type`), matching the existing randomized-data universe convention; they do not assume any ordering, numeric encoding, or structure on the token alphabet beyond its finite cardinality. This concludes the previously recorded canonical-vocabulary representation obligation. The manuscript was not edited.

All nine vocabulary-transport axiom checks, including both final arbitrary-vocabulary public lower statements, return exactly `[propext, Classical.choice, Quot.sound]`. In particular, the final theorem's dependency closure contains neither `sorryAx` nor a custom paper-specific axiom; this also audits the imported model/class transport through the final wrapper.

## Independent-radius lower wrappers corrected as well

`ObservedBenchmarkLower.lean` extends the same final protocol and vocabulary correspondence to the fixed-accuracy appendix, where the oracle radius and final TV tolerance are separate positive parameters. `benchmark_observed_target_error_power_alternative` derives the actual-witness query power and finite round minimum from `observed_signalCalibrated_alternative`. `benchmark_observed_public_class_lower_any_vocabulary` proves the public-class result for an arbitrary finite token alphabet with full commit-row feedback. Its `_eventually` companion uses the already proved literal vocabulary-growth implication and `benchmark_round_min_eventually` to remove the minimum on an actual tail at fixed positive radius and tolerance.

The query threshold is `2^(1/α)·(N/radius²)^(1/(3α))/16`; the eventual round threshold is `N^(1/3)·radius^(4/3)/(3145728·ε)`. The finite theorem retains the minimum with `N/16384`. Public RT/UEN/RF/A2 membership, the chosen benchmark signal, actual-oracle Q/R budgets, and measurable seed risk are all preserved by the same proved witness and controller transport. The old independent-radius `RandomizedSamplerData` wrappers remain valid for their narrower interface, but these observed wrappers should be used for manuscript correspondence.

Validation: `lake build ForestSampling.ObservedBenchmarkLower` passed (8777 jobs; 110 lines), and all three exported theorem axiom checks report exactly `[propext, Classical.choice, Quot.sound]`. The file is frozen, with no `sorry`, `admit`, or custom axiom.
