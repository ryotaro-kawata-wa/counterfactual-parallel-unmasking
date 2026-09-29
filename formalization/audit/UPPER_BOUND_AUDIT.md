# Latest randomized upper bounds: specification and proof audit

Audit date: 2026-09-26. Canonical source: `manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/` at the starting arXiv worktree snapshot. This document records a mathematical reading and a source-code inventory, not a claim that the upper theorems have been checked by Lean.

## Scope and outcome

Read `appendix_upper_proofs.tex`, `proofs/upper_screen.tex`, `proofs/upper_structure.tex`, `proofs/upper_error.tex`, `appendix_kl_extension.tex`, `appendix_algorithm.tex`, and `main_setup.tex`; inspected the existing finite probability, forest, oracle, algorithm, and paper-statement interfaces.

The latest Hellinger and forward-KL arguments contain the important adaptive probability distinctions: common stored nodes rather than independently realized paths, a safe comparison rule rather than conditioning the output on success, and averaging the screen failure over the joint seed/reference law rather than conditioning on the full seed. No fatal mathematical gap was identified in this bounded reading. The finite upper bounds themselves are not currently proved in Lean; several major construction and probability components remain absent.

## Correct finite specifications

Write `rho` for the public Hellinger radius, `eta` for the screen failure budget, `Delta` for the degree cutoff, `J` for the peel-phase cap, `S = J + 1`, `c = 8(Delta + 1)`, and `T = ceil(8 log(S N^2 / eta))`. The source-column count is `K + 1` when the realized maximum bank size `K` is positive, and zero when `K = 0`.

- Degree range: `9 <= Delta <= N - 1`; `N >= 10`; chunk parameter lies in `1..N`; `0 < eta < 1`.
- Preprocessing uses the standard floor and must be feasible. Strict separation is `4 rho / sqrt(N) + tailTolerance < edgeSignal`.
- Every path: `Q <= columns * S * T * c * (c + chunkCount)` and `R <= ceil(4 N J / Delta) + ceil(log_2(N+1)) + 2`.
- Oracle depth: `D <= 1 + R + S`. The initial all-mask readout is outside `Q`; charging it adds one.
- Hellinger case: every exact/oracle row pair has `H^2 <= rho^2/(2N)`, and the seed-averaged output TV is at most `rho + eta` for each fixed admissible oracle.
- Forward-KL case: row KL is at most `kappa <= rho^2/N`; the seed-averaged output forward KL is at most `N kappa + N log(|V|) eta`.
- The successful-path round estimate is strict and sharper; it must not replace the unconditional cap on failed-screen paths.

`PaperStatements.FiniteExactCertificationUpperBound` is an obsolete `Prop` definition: it uses a deterministic-style color factor, omits the tail column and failure budget, uses `8NJ/Delta` for rounds, and asks for risk at most `rho`. It is neither the current specification nor a proved theorem.

## Dependency map and status at audit start

| Manuscript result | Necessary input | Current Lean coverage / missing bridge |
|---|---|---|
| Residual Markov property (`app:lem:residual-markov`) | Positive forest factorization; grouping factors by residual component; cancellation of factors away from a readout | Typed forest factorization, histories, and exact conditional rows exist. General residual component independence and fixed-neighbor cancellation are not proved. |
| Preprocessing certificates (`app:lem:preprocessing-certificates`) | Row TV from Hellinger; threshold floor; finite ranking | Row TV implication is proved in `FrozenOracle.Accurate.tv_bound`. Banks, threshold grid, tail representative, and bank cardinality proofs are not implemented. |
| Fresh randomized screens (`app:lem:random-screen-success`) | Independent uniform color block at each reached call; at most `2 Delta` forbidden equalities; Hoeffding; finite union bounds; conditional expectation | No screen random-source implementation or reached-call probability theorem. Need only fixed-call conditional bounds, not a union over histories or drafts. |
| Fixed-draft rows and low-degree contract (`app:lem:fixed-draft-rows`, `app:lem:low-degree-screen`) | Residual Markov; separating colors; RT at one common complete boundary; UEN; strict majority; selector identity on nonoverflow | RT/UEN have typed definitions. Actual probes, votes, banks, selectors, and their certificates are absent. |
| Peeling contraction (`app:lem:successful-path-structure`) | Exact low-degree rows; size cap on high-degree rows; forest degree sum; nonincreasing degree under deletion | No packed sampler or peeling implementation/proof. High-degree rows need not be subsets of true neighbors. |
| All-path resources (`app:lem:upper-resources`) | Chunk counting; at most `J+1` screens; singleton peels; centroid halving; reserved fallback round | Generic `Program.WithinBudgets` exists. Concrete capped loop and all-path invariants are absent. |
| Exact hybrid (`app:lem:exact-hybrid`) | Residual component independence; safe batches; telescoping adaptive conditional probabilities | `Program.eval` exists only for oracle commits. Exact-row hybrid preserving frozen query replies, safe-batch predicate, and target-law theorem are absent. |
| Adaptive Hellinger (`app:lem:adaptive-hellinger-upper`) | Product Hellinger calculus; continuation recursion; one charge per coordinate | Finite product affinity and product Hellinger bound are proved. Adaptive bind inequality and program induction remain to be implemented. |
| Safe comparison (`app:lem:safe-controller-comparison`) | Success implies safe structure/no fallback; switch on first failed screen; common-prefix coupling; joint failure bound | No comparison program or coupling proof. TV triangle/coupling lemmas are not present in this project's finite API. |
| Forward-KL decomposition (`app:lem:adaptive-joint-kl`) | Joint batch conditionals; unique fixed-seed output path; exact reference target law; KL chain rule; product-marginal decomposition | Existing finite API has no KL definition or KL calculus. A full joint-reference execution proof is absent. |
| Finite KL bound (`app:thm:finite-kl-upper`) | Previous row/TC identity; `TC <= batchSize * log(|V|)`; safe-path TC = 0; fresh-color bound under joint reference | Entire connection remains open. TV coupling alone cannot supply it. |

## Checks and formalization hazards

1. **Keep frozen replies fixed in the exact hybrid.** Evaluating `Program.eval (FrozenOracle.exact M)` is not the required hybrid: it changes query replies and therefore future batches. Introduce a second evaluator whose query branch uses the given frozen oracle and whose commit branch alone uses exact rows.
2. **Keep the realized-bank query bound distinct from uniform program budgets.** `Sampler.WithinBudgets` quantifies all preprocessing replies and all later replies, while the finite query bound uses the banks realized for the particular admissible oracle. The sharp statement needs an oracle-specific resource semantics, or a public uniform bank upper bound must replace the realized bank size before using the current uniform budget predicate.
3. **Requested rows and returned rows are different interfaces.** Existing `Program.query` exposes all masked rows. This is allowed by the manuscript by requesting all of them, and does not change submission counts. To verify the sharper returned-row count, formalize the requested readout subset and prevent the controller from reading outside it.
4. **The joint-reference KL identity is an equality because the path is determined by the final assignment after fixing the seed and frozen map.** Generic data processing gives only an inequality. Prove the cylinder/unique-path fact before claiming the displayed equality.
5. **Do not require screen failure at most `eta` for each seed.** The full seed fixes all colors. The correct per-seed comparison involves the conditional failure probability; its seed expectation is at most `eta`.
6. **KL uses the reference law's failed-screen probability.** A bound under the implemented oracle execution is insufficient. Fresh independent colors after each reference history prove the needed reference estimate directly; no change-of-measure estimate is required.
7. **High-degree row correctness must not enter the peeling proof.** Only cardinality at most `Delta` is available. Low-degree neighbors give a lower bound on incoming claims, and high-degree claims can only increase it.
8. **Phase-cap positivity is available from the actual parameter range.** Since `Delta <= N-1`, `2N/(Delta+1) >= 2`, so `J >= 1`. This closes the apparent zero-phase issue in the strict successful-path round estimate; a relaxed parameter structure lacking the upper degree bound would not support the same proof without an extra case.
9. **Termination should be explicit.** A complete program has finitely many queries between commits and at most `N` nonempty commits. The manuscript's standard zero-query draft and finite screen loops give this; arbitrary callbacks require the corresponding termination evidence.

## Small reusable Lean architecture

### First: adaptive Hellinger without graph machinery

The existing typed `Program` already supports the central composition theorem. Add a standalone module importing `Algorithm` and prove:

1. `FinDist.affinity_bind_ge`: for finite kernels `k,l`,
   `sum a, sqrt(p a * q a) * affinity (k a) (l a) <= affinity (p.bind k) (q.bind l)`.
   Finite Cauchy--Schwarz at each output followed by exchanging sums proves this. Equality is unnecessary for the upper bound, avoiding support bookkeeping.
2. `FinDist.sqHellinger_bind_le_add`: if every child Hellinger cost is at most a nonnegative common remaining budget `b`, the parent cost is at most `H^2(p,q) + b`. Use the previous inequality and `affinity p q <= 1`.
3. `Program.evalWithCommitOracle`: retain query oracle `O`; use a separate commit oracle `C`. The existing `eval O` is the diagonal case `C = O`.
4. Induct on the program and bound `H^2(evalWithCommitOracle O C program, eval O program)` by `uncommitted.card * rowBudget`, under uniform row distance `<= rowBudget`. Query branches cost zero; commit branches use the existing product bound and `card(uncommitted after append) = card(uncommitted) - card(batch)`.
5. Instantiate `C = FrozenOracle.exact M` and `rowBudget = rho^2/(2N)` to obtain the manuscript's adaptive Hellinger lemma, without structural safety. This is a substantive proof over the actual program semantics, not an assumption of the desired output bound.

### Then: exact joint reference and KL

1. Define finite forward KL (with strict positivity hypotheses where logarithmic identities are used), entropy, and total correlation.
2. Prove product-marginal decomposition `KL(p, product q_j) = TC(p) + sum_j KL(p_j,q_j)`, entropy identity, and `TC <= batchSize * log(|V|)`.
3. Define a program evaluator that retains frozen query replies but uses the target's exact *joint* batch conditional at commits.
4. Prove output support preserves the committed history; prove the unique path/cylinder lemma; conclude joint-reference output equals the target conditional law from any history.
5. Prove the finite adaptive KL chain rule on this program tree, then substitute the batch decomposition.
6. Connect structural safety to `TC = 0`, and separately connect the randomized screen process to joint-reference failure mass at most `eta`.

### Construction layer

Banks/probes/screen votes and their deterministic contract can be developed independently of the screen probability estimate. Likewise prove a graph-only peeling theorem taking the low-degree contract and row-size cap as hypotheses. The full upper theorem is complete only after the real randomized sampler is constructed and shown to satisfy these hypotheses and the all-path resource caps.

## Completion criteria

For each final upper theorem, retain the exact target-oracle and seed quantifiers, inspect `#print axioms`, and link the Lean declaration to its manuscript statement. A declaration of type `Prop`, an abstract bound assuming its own output estimate, or a standalone generic composition theorem is not evidence that the complete packed sampler theorem has been formalized.

## Implemented after the audit: adaptive Hellinger composition

`ForestSampling/AdaptiveHellinger.lean` now contains complete proofs of:

- `FinDist.affinity_bind_ge`: the genuine finite-kernel data-processing inequality, proved by finite Cauchy--Schwarz rather than postulated as a kernel contract.
- `FinDist.sqHellinger_bind_le_add`: a common nonnegative continuation budget adds to the current batch loss.
- `History.appendBatch_uncommitted` and `History.appendBatch_uncommitted_card_add`: an actual program commit removes exactly its fresh batch from the residual coordinate set.
- `Program.evalWithCommitOracle` and its diagonal identity with `Program.eval`: queries use the original oracle while commits may use a different oracle.
- `Program.sqHellinger_evalWithCommitOracle_le`: structural induction on the existing dependent `Program` proves the Hellinger bound `uncommitted.card * rowBudget`, for any two commit oracles whose rows satisfy the stated local bound, with the query oracle held fixed.
- `Program.exactCommitEval` and `Program.sqHellinger_exactCommitEval_le`: instantiate this evaluator and bound with the model's existing exact oracle and the existing accuracy hypothesis.
- `Sampler.exactCommitOutputLaw`, `Sampler.sqHellinger_exactCommitOutputLaw_le`, and `Sampler.tv_exactCommitOutputLaw_le`: retain the original all-mask preprocessing reply and fixed seed; obtain `H^2(exactCommitHybrid, oracleOutput) <= rho^2/2` and `TV(exactCommitHybrid, oracleOutput) <= rho`.

This closes the adaptive composition argument of `app:lem:adaptive-hellinger-upper` against the actual generic sampler/program semantics, including arbitrary adaptive batches and queries. It does **not** identify the exact-row hybrid with the target, construct the packed sampler, certify screen success, prove the failed-screen coupling, or establish the complete `rho + eta` upper theorem. Those obligations remain as listed above.

Validation: `lake env lean ForestSampling/AdaptiveHellinger.lean` and `lake build ForestSampling.AdaptiveHellinger` both succeeded on Lean 4.33.0. The new module emitted no warnings. `#print axioms` for the bind-affinity theorem, bind-Hellinger theorem, generic program composition theorem, and both sampler-level bounds listed only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or project-specific axiom dependency.

## Implemented after the audit: exact joint-reference output

`ForestSampling/ExactReference.lean` adds an actual joint-reference evaluator and proves its output identity:

- `FinDist.conditionalMap_apply_ratio` and `FinDist.conditionalMap_bind_conditionOn` prove finite conditional disintegration directly from the finite mass definitions.
- `History.agrees_appendBatch_iff` identifies the post-commit event with the old history and selected batch values. `History.jointBatchLaw_strictlyPositive` proves that every fresh batch assignment has positive probability.
- `History.jointBatchLaw_bind_conditionalLaw` proves that drawing the true joint batch and then conditioning on its realization recovers the initial target conditional law. Empty and complete histories are also handled explicitly.
- `Program.evalJointReference` keeps frozen query replies and uses `History.jointBatchLaw` for each commit.
- `Program.evalJointReference_eq_conditionalLaw` proves by structural induction on the actual adaptive program that its joint-reference output from any history is the target conditional law.
- `Sampler.jointReferenceOutputLaw_eq_target` gives the manuscript's fixed-seed reference-output identity for arbitrary batches, retaining the original oracle's initial all-mask reply as well as subsequent query replies.

This establishes the first assertion of `app:lem:adaptive-joint-kl`: the joint-reference output equals the target even when batches are unsafe. It is not yet the adaptive KL decomposition, because the KL likelihood-ratio chain identity and batch total-correlation decomposition remain to be connected. The product-of-exact-rows hybrid still needs a structural conditional-independence proof to identify it with this joint reference.

The additional bridges `History.jointBatchLaw_map_eval` and `MaskedState.exactRow_commitState` identify its batch marginals with exactly the commit-state rows used by the frozen oracle. `lake build ForestSampling.ExactReference` passes with no new warnings. Axiom checks for disintegration, batch positivity, the program-level identity, and the sampler-level target identity list only `propext`, `Classical.choice`, and `Quot.sound`.

## Implemented after the audit: finite forward-KL calculus

`ForestSampling/FiniteKL.lean` now proves the following finite ingredients, using `FinDist.klDivergence` with natural logarithms and the reference law first:

- `exp_neg_half_klDivergence_le_affinity`, by weighted finite Jensen for `exp`;
- `sqHellinger_le_one_sub_exp_neg_half_klDivergence` and `sqHellinger_le_half_klDivergence`, matching the manuscript's exponential and linear KL-to-Hellinger inequalities;
- `klDivergence_sigmaJoint`, the exact chain rule on retained dependent outcomes, averaging continuation KL under the reference law;
- `klDivergence_map_equiv`, allowing the eventual program replay equivalence to transport the equality to output configurations;
- entropy nonnegativity and `entropy_le_log_card`, via the positive uniform reference law;
- `klDivergence_piProduct_decomposition`, the exact identity `KL(p, product q) = TC(p) + sum_i KL(p_i,q_i)` for a positive, potentially dependent batch law;
- `totalCorrelation_eq_entropy`, `totalCorrelation_nonneg`, `totalCorrelation_le_card_mul_log_card`, and vanishing total correlation for product laws.

All identities needing logarithmic support conditions require strict positivity explicitly. The real-valued KL definition alone is not interpreted as an extended-real divergence at zero denominator mass. The intended target and frozen-oracle laws satisfy the required positivity.

These results establish the finite calculus and batch decomposition needed by `app:lem:adaptive-joint-kl`. The adaptive program chain identity and its row/TC path accounting still need to be composed with the exact reference and retained replay semantics; the randomized-screen guarantee remains separate.

Validation: `lake build ForestSampling.FiniteKL` passes with no warnings. The auxiliary uniform distribution used for the entropy proof is private, avoiding a name collision with the independently developed matching-prior uniform law. Axiom checks for Jensen, KL-to-Hellinger, the dependent chain rule, entropy cap, batch decomposition, total-correlation cap, and equivalence invariance list only the three standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Implemented after the audit: actual-program adaptive KL identity and budgets

`ForestSampling/ProgramKL.lean`, using the independently proved replay equivalence from `ProgramMidpoint.lean`, now connects the finite calculus to the actual sampler:

- `Program.retained_klDivergence_eq_expectation` proves the exact accumulated local-KL identity on actual retained program executions; `Program.output_klDivergence_eq_expectation` transfers it through the proved replay equivalence.
- `Program.joint_oracle_batch_kl_decomposition` uses the actual joint conditional and actual mandatory oracle commit rows, including the marginal/readout bridges.
- `Program.target_output_klDivergence_eq_tc_add_rows` and `Sampler.output_klDivergence_eq_reference_expectation` give the displayed fixed-seed identity in `app:lem:adaptive-joint-kl`: output forward KL equals the true-joint reference expectation of total batch correlation plus singleton row errors.
- `Sampler.referenceRowKL_le` and `Sampler.referenceTotalCorrelation_le` prove the pathwise bounds `N * rowKLBudget` and `N * log(|V|)`, including arbitrary unsafe/fallback paths.
- `Program.PathBatchesFactorize` states the actual conditional independence required along a particular reference path. `Program.retainedTotalCorrelation_eq_zero_of_factorizes` proves that this property forces zero accumulated total correlation.
- `Sampler.output_klDivergence_le_reference_failure_mass` proves the per-seed bound `N*kappa + N*log(|V|)*Pr_reference(bad)` whenever every good retained path has conditionally factorizing batches.

This completes the adaptive joint-reference KL identity and its analytic cost accounting against the real `Sampler.outputLaw` semantics. It does not yet prove the complete finite randomized upper theorem: the graph-based structural-safety implication to `PathBatchesFactorize`, construction of the packed sampler, and reference-law fresh-screen failure probability at most `eta` remain open. The per-seed failure probability is intentionally retained; the manuscript's `eta` guarantee comes only after averaging over seeds.

Validation: `lake build ForestSampling.ProgramKL` succeeds. Existing dependency linter warnings remain; the new module introduces no warnings.
The retained KL identity, actual-target/output identity, both path budgets, and both program/sampler failure-event bounds all passed `#print axioms`, with dependencies exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Implemented after the audit: actual forest conditional independence and safe controllers

`ForestSampling/ForestConditionals.lean` now proves structural conditional independence directly from the stored `ForestModel.factorizes` law:

- `ForestModel.residualLaw_factorizes_over_blocks` conditions on an arbitrary committed history and derives a product law over any finite labeling that keeps adjacent residual vertices in the same block. The proof regroups the actual rooted factors and normalizes each positive block weight. It retains factors from committed children whose parents remain uncommitted, so those conditional unary factors are not discarded.
- `ForestModel.BatchStructurallySafe` means that the selected batch meets each actual residual connected component at most once. `jointBatchLaw_factorizes_of_safe` derives factorization of that batch's true joint conditional from the graph separation, and `jointBatchLaw_eq_exactCommit_of_safe` identifies it with the actual exact-oracle commit product.
- `Program.StructurallySafe` requires this graph property at every commit along every branch reached using the fixed query oracle. `pathBatchesFactorize_of_structurallySafe` closes the structural premise of the adaptive KL theorem.
- `Program.exactCommitEval_eq_conditionalLaw_of_safe` and `Sampler.exactCommitOutputLaw_eq_target_of_safe` prove the exact-row hybrid's target identity for safe actual programs, by conditional disintegration at every commit.
- `Sampler.output_tv_le_of_structurallySafe` now proves the complete generic safe-controller `TV <= rho` statement from the existing oracle-accuracy definition and actual forest model. `referenceTotalCorrelation_eq_zero_of_safe` and `output_klDivergence_le_of_structurallySafe` give zero reference TC and the safe-controller `KL <= N*kappa` bound.

This closes the graph-conditional-independence and generic safe-controller gaps noted in the earlier chronological entries. The remaining upper-bound construction obligations are still substantive: the concrete packed sampler and screens, the graph peeling and all-path resource analysis, the reference-law screen-failure estimate, and the failed-screen comparison with a safe controller have not been constructed by this module. Structural safety itself is not asserted for an unimplemented sampler.

Validation: `lake build ForestSampling.ForestConditionals` succeeds without new module warnings. Nine public graph-independence, exact-hybrid, safe-controller TV, and safe-controller KL declarations were checked separately; each depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Implemented after the audit: actual packed-screen correctness and one-screen probability

The following modules now define the actual screen data and prove its deterministic low-degree contract, rather than assuming a screen row oracle:

- `ScreeningPreprocess.lean` defines the actual all-mask oracle marginals, buffered vocabulary banks, public ordered tail representative, maximum bank length, and shared bank/tail columns with draft padding. The standard floor guarantees a nonempty bank complement. Singleton TV gives the true-tail certificate for every omitted token and mass at least `t/2` for every retained token. Every local bank token is proved to occur in a shared packed column.
- `ScreeningProbes.lean` defines deterministic public color-class ranks and chunks, the exact submitted probe states, and their preservation of committed history. It proves that the masked set is exactly the selected fresh chunk and that a separating coloring reveals every readout neighbor at the fixed-draft boundary value. `MaskedState.exactRow_boundaryState` identifies the fully clamped state's row with the manuscript's boundary row.
- `ScreeningResponse.lean` proves the clipped RT tail diameter, the single-tail-loss bank-to-full response comparison, both row-noise losses, the strict `4*epsilon + nu < signal` edge detection inequality, and absence of incident edges for an empty local bank.
- `Screening.lean` combines these actual states with the separately proved `LocalMarkov.lean` theorem. `probe_exactRow_eq_boundary`, `not_vote_of_separating_nonedge`, and `vote_of_separating_edge` identify the actual observable vote on each separating coloring, using the target's existing RT/UEN assumptions and the actual frozen row-TV accuracy premise.
- `ScreeningAggregate.lean` defines actual strict-majority candidate rows and the returned rows, including the all-empty-bank early exit. `candidateRow_eq_neighbors` and `returnedRow_eq_neighbors` prove exact low-degree recovery on `ScreenSuccess`. `returnedRow_card_le` holds without screen success or any low-degree hypothesis. `PublicRowSelector` requires both its public cardinality cap and its nonoverflow identity; the concrete empty-on-overflow selector is supplied.
- `ScreeningSelector.lean` supplies the actual standard top-vote selector, sorting by decreasing public score and increasing public position on ties, with proved subset, cap, and nonoverflow identity.
- `ScreeningSuccessProbability.lean` connects the independently proved fresh-color concentration in `ScreenColorProbability.lean` to this same `ScreenSuccess` event. `returnedRowsFailure_le_budget` bounds failure of the actual returned low-degree rows by `eta/S` under the actual independent uniform color-block law, after the history and draft have been fixed. The selector transcript may depend on the current colors.

These results close the deterministic low-degree screen contract and fixed-history one-screen probability bound. The preprocessor's logarithmic threshold grid/max selection and RF bank-size estimate remain separate obligations; the current theorem takes an explicit feasible public threshold. The defined chunks still need their sharp chunk cardinality and number-of-chunks bounds. Probe enumeration and its resource cost are not yet represented as a concrete sequence of `Program.query` constructors. The full capped peeling/centroid sampler, its structural safety on successful reached screens, and the adaptive reached-call probability connection to its actual seed/reference semantics also remain to be constructed. Fixed-history independent colors are not being presented as a proof that an arbitrary full controller draws them freshly.

Validation: all seven screen modules pass their individual Lake builds. Eleven public preprocessing, vote, majority, selector, and one-screen probability declarations passed explicit axiom checks, each with only `propext`, `Classical.choice`, and `Quot.sound`.

## Implemented after the audit: actual query schedule and packed resources

`QuerySchedule.lean`, `ScreeningResources.lean`, `ScreeningProgram.lean`, and `ScreenExecution.lean` close the query-enumeration and chunk-accounting gaps in the preceding chronological entry:

- Public order ranks are injective within each color class. Rank remainders therefore prove that each actual chunk contains at most `q` positions. The number of actual nonempty chunks is at most `|U|/q + |Colors|`.
- The finite schedule is indexed by coloring, nonempty chunk, source color different from that chunk's color, and packed column. Masked readouts do not create extra submissions. Its exact cardinality and packed upper bound `T*(|U|/q+K)*(K-1)*(Bmax+1)` are proved.
- `Program.runQuerySchedule` constructs one actual `Program.query` for each schedule index and collects dependent reply tables. Its evaluator identity proves that a complete schedule overwrites the entire table with the actual frozen oracle's replies, independently of arbitrary initialization. The query-budget theorem quantifies over all possible replies.
- `Screening.runScreen` is an actual program builder without a target-model or frozen-oracle argument. It performs the packed queries, reads only the collected table, computes the observed diameter votes and selected rows, and respects the all-empty-bank early exit.
- `eval_runScreen` identifies this concrete program with the previously verified returned-row function for every fixed oracle. `runScreen_withinBudgets` carries the packed query bound into the existing all-path `Program.WithinBudgets` semantics.

These modules do not yet construct the full capped sampler or prove adaptive seed freshness. The fixed-history screen probability remains a one-screen theorem until the controller's indexed color blocks and reached-call/reference semantics are connected.

Validation: all four modules pass their Lake builds. Query evaluator/resource identities, chunk size/count, packed query bounds, and concrete screen evaluator/budgets passed seven core axiom checks, with only the three standard Lean axioms.

## Implemented after the audit: concrete capped sampler and all-path budgets

`CappedController.lean` and `PackedSampler.lean` now construct the feasible-threshold version of the actual sampler through the existing `Program` and `Sampler` interfaces:

- The preprocessing banks are calculated from the supplied distinguished all-mask reply; the constructor has no target-model or frozen-oracle argument. Their equality to the audited oracle banks is proved. The zero-query draft maximizes each supplied marginal, breaking ties by public token order.
- Each screen uses the concrete packed queries, actual collected vote counts, and the standard public top-vote selector. The loop consumes the current indexed color block and passes only the untouched tail to the next phase.
- Frozen peel vertices are committed as singleton batches in public order. The terminal controller forms the undirected union of returned rows, trims an actual maximum-degree cycle vertex with public ties when cyclic, and otherwise selects the smallest public centroid of each actual public connected component. The centroid selection is proved to satisfy the graph centroid property.
- Both peeling and terminal execution reserve one last round for an all-remaining fallback. Every constructed batch is nonempty and fresh. Hard budgets quantify over arbitrary seeds, preprocessing replies, later query replies, and commit outcomes, including failed screens and fallback.
- `loop_withinBudgets` retains the actual bank maximum in the bound `(phases+1)*T*(N/q+K)*(K-1)*(Bmax+1)`. `sampler_withinBudgets` supplies a fully public universal query cap by replacing `Bmax` with the vocabulary size. A separate RF estimate is still needed for the manuscript's sharper rate.
- `seedLaw` is the actual finite product law of independent uniform colors over call indices, repetitions, and positions. Commit randomness remains in the program evaluator.

This closes the absence of a concrete capped sampler and its universal resource contract. It does **not** yet assert the full randomized theorem for that sampler. The remaining construction-specific obligations are: the adaptive reached-screen probability under actual seed and reference-path semantics; successful-screen induced-graph iteration showing structural safety and that the guard never changes a good execution; the comparison with a safe repair; and logarithmic threshold-grid/RF estimates and rate-specific public parameter instantiation. Defining an independent seed law alone is not counted as the adaptive probability proof.

Validation: both modules pass Lake builds. Ten representative definitions and theorems, including the actual sampler, draft/bank bridge, hard guards, all-path budgets, and finite seed law, passed explicit axiom checks with only `propext`, `Classical.choice`, and `Quot.sound`.

## Implemented after the audit: actual adaptive reached-screen probability

`ProgramFailure.lean`, `FiniteSeed.lean`, and `PackedFailure.lean` connect the full concrete capped sampler to the fresh-screen estimate:

- `PrefixRepair.failureMassWith` generalizes the first-marker probability to any fixed history-dependent positive `BatchKernel`. `failureMassWith_eq_event` identifies it with the actual retained-path event under that kernel; oracle-product draws and exact joint-target reference draws are both valid instances.
- `piProduct_expect_cons` proves the exact finite head/tail decomposition of the independent decision seed. `markScreen` lifts markers through the actual collected query table, and `markPeel` lifts them through the actual frozen singleton commits and hard guard.
- `markLoop` marks the first reached screen at which the actual `ScreenSuccess` color-separation event fails. It changes no program, query, commit, or law: its type is a self-annotation of the previously constructed `loop`.
- `mean_markLoop_le` proves the adaptive union bound from fixed-history one-screen estimates. It uses the actual recursive code to show that current queries and frozen peeling cannot inspect future seed blocks; the proof interchanges finite future-seed and commit sums. It does not add an adaptive-freshness assumption.
- `mean_markLoop_le_budget` substitutes the independently proved uniform-color concentration and logarithmic repetition allocation. `sampler_mean_failure_le` applies the result to the actual preprocessing reply and actual finite `seedLaw`. `sampler_reached_screen_failure_le` states it directly as the seed-average retained-path probability of reaching a failed screen, bounded by `eta`.

The same theorem applies with `BatchKernel.ofOracle O` and `BatchKernel.ofTarget M.target M.target_positive`; thus the KL proof's true-joint-reference failure probability is covered directly, rather than inferred from the product sampler's execution. The batch kernel is fixed before seed averaging, as required; a seed-dependent arbitrary kernel is not covered.

This closes the adaptive reached-call probability gap left in previous chronological entries. Successful-controller structural safety and the guard-exhaustion bridge, safe repair/risk integration, RF bank bounds, threshold-grid selection, and final public rate instantiation remain separate obligations.

Validation: all three new modules pass their Lake builds. Nine representative marker, exact event, finite seed, adaptive recursion, and actual sampler declarations passed explicit axiom checks; every dependency list contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Implemented after the audit: exact public finite parameters and stage accounting

`PackedParameters.lean` instantiates the actual program with the manuscript's exact public formulas: `q=ceil(N/L)`, `C=8(D+1)`, `J=phaseCap N D`, `S=J+1`, `T=ceil(8*log(S*N^2/eta))`, `extraRounds=hardRoundCap N D-1`, and row TV error `rho/sqrt(N)`. Its `manuscript_program_withinBudgets` proves the printed bound `Q <= screenColumns*S*T*C*(C+L)` for the actual preprocessing bank, and `R <= hardRoundCap`. The column count is zero when every bank is empty; this branch has zero counterfactual submissions. A fully public arbitrary-preprocessing-reply contract replaces that factor by `|V|+1`. Both Hellinger and forward-KL repetition calibration identities are proved, and the exact ceiling automatically discharges the adaptive failure theorem.

`PackedDepth.lean` introduces an oracle-stage witness whose only query-group constructor requires an entire fixed list of states through the actual `runQuerySchedule`. Commit calls count separately. It proves the total cap `1+hardRoundCap+S`, including the distinguished all-mask preprocessing stage. Individual sequential `Program.query` constructors are not identified with adaptive stages.

`PackedPathDepth.lean` further retains each actual execution path. Its legal `GroupedOracleTrace` follows fixed-state query blocks and actual sampled batches. `retainedRoundCount_querySchedule` proves that grouping removes no commit call, and `manuscript_sampler_pathwiseOracleDepth` proves the exact printed pathwise refinement: a legal grouped trace exists with `1+depth <= 1+actualCommitRounds+S`.

Validation: the exact-parameter/resource module builds cleanly; nine representative declarations passed standard-axiom checks. The uniform grouped-depth module builds cleanly; its four main declarations also passed standard-axiom checks. These are genuine schedule witnesses, not assumed parallel-depth bounds.
The exact pathwise depth module also builds cleanly, and all four core trace/actual-counter/pathwise-depth axiom checks pass with the same three standard axioms.
