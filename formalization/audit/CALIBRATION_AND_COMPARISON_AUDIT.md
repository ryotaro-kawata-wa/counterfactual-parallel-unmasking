# Calibration, selector, comparison, and claim-scope audit

Date: 2026-09-26. Source baseline: `1507791fd7c1137c77ec139cc0b73b5765f1464b`. This audit concerns the current compiled manuscript, not the disabled exponent supplements. `main.tex:44–49` sets `includeexponents` false unless an optional wrapper overrides it; `main.tex:199–212` includes the finite/fixed-accuracy, comparison, and oracle-comparison sections examined here. No manuscript files were edited.

## Findings and limits

**No confirmed mathematical error was found in this bounded inspection** of finite calibration, fixed-accuracy rates, row-selector invariance, or the two-type comparison path. This is a source audit, not a Lean certification. The main remaining risks are omitted formal hypotheses during implementation, confusing several distinct averaging laws, and overstating comparisons of sufficient upper bounds as lower bounds on other algorithms.

The exact five arXiv versions used for the quantitative source checks were accessed on the audit date; source locators and formulas were compared, rather than inferred from titles or abstracts. Contextual bibliography beyond these quantitative comparisons was not exhaustively audited. Experiments and their numerical reproducibility are outside this audit.

## Finite calibration and fixed-accuracy rates

Evidence: [appendix_benchmarks.tex](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/appendix_benchmarks.tex), especially lines 38–97, 109–276, and 310–664.

| Step checked | Result of independent calculation | Formalization burden / priority |
| --- | --- | --- |
| Half-signal preprocessing | From `16 max{x/√N,1/V} ≤ ω`, the public floor is at most `ω/4`. The dyadic point `2^(-ceil(log₂(2/ω)))` lies strictly above `ω/4` and at most `ω/2`, hence is feasible. The selected maximum remains at most `ω/2`. The margin `4x/√N+ω/2 ≤ 3ω/4 < ω` and column cap `(16/ω)^(1/α)+1` follow. | Real logarithm/ceiling and finite maximum lemmas; preserve `N≥10`, `V≥2`, `x>0`, and `ω≤1/2`. Medium priority after preprocessing contract. |
| Matching witness | With `λ=τ=ω`, `K=floor(ω^(-1/α))`, `α>1`, and `0<ω≤1/2`, one gets `1≤K<1/ω<V`, `Kω<1`, and `ω≤K^(-α)`. Thus the finite RF and hard-family hypotheses are met at the actual public parameters, not only asymptotically. | Natural floor cast, monotonic real powers, and explicit finite family inclusion. High priority because it connects the lower theorem to the main target class. |
| Signal substitution | `ω=½(ρ²/N)^(1/3)` gives `ω³=ρ²/(8N)≤ρ²/(2N)`. The only remaining finite-domain condition is `V>2(N/ρ²)^(1/3)`. The query threshold is `floor(2^(1/α)(N/ρ²)^(1/(3α)))/8`; the round threshold is `min{N/16384,N^(1/3)ρ^(4/3)/(3145728 ε)}`. Constants agree with the underlying `786432` corollary. | Algebraic consequences should be proved separately from the unproved structural/process inputs. High priority. |
| Fixed-accuracy feasibility | At fixed `x>0`, `(x/√N)/ω=2x^(1/3)N^(-1/6)→0`; with `V=N^(ν+o(1))`, `ν>1/3`, also `(1/V)/ω→0`. These thresholds are independent of the public cutoff `Δ`. | Formal meaning of a growing integer vocabulary sequence, eventual inequalities, and fixed parameters. Medium priority; do not silently claim joint-limit uniformity in accuracy. |
| Resource logarithms | Phase and screen-call counts are `O(log N)` uniformly over `9≤Δ≤N−1`. Both failure-budget choices make the number of colorings `O(log N)` at fixed accuracy; in the KL case the extra `log log V` is still `O(log log N)`. The multiplier is at most `272Δ²`. Thus queries are `O(ω^(-1/α)Δ²(log N)²)`; rounds/depth are `O((N/Δ)log N)`. | Preserve the separate pathwise resource contract and finite public bank cap. No expected resource bound is substituted for a pathwise one here. |
| Balanced cutoff | Rounding `Δ=ceil((Nω^(1/α))^(1/3))` changes only a constant factor once the unrounded value is at least one; it eventually lies in the permitted cutoff interval. Both polynomial terms have order `N^(2/3)ω^(-1/(3α))`, giving exponent `2/3+1/(9α)<1`. | Eventual cutoff membership, ceiling bounds, and polynomial domination of logarithms. Medium priority. |
| Floor and minimum removal | Once `u_N≥2`, `floor u_N≥u_N/2`. The ratio of the smaller round candidate to `N/16384` equals `ρ^(4/3)/(192 ε N^(2/3))→0`. Both use fixed positive accuracy parameters. | State the eventual threshold before asserting each disjunction. A different alternative may hold at different `N`; do not replace the pointwise eventual disjunction by a single globally chosen branch. |
| Single-accuracy class | `ρ=ε/2`, `ε_KL=ε²/2` yield row allowances `ε²/(8N)` in Hellinger and `ε²/(4N)` in KL. Both give `ω=(ε²/(32N))^(1/3)`. The reported TV is at most `3ε/4`, and expected forward KL at most `ε²/2`. Lower round scaling becomes `N^(1/3)ε^(1/3)`. | Correct substitutions and inequality directions. Retain the difference between the Hellinger/TV lower-bound class and the stronger forward-KL upper-bound class. |

The main upper and lower statements [main_upper.tex](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/main_upper.tex) and [main_lower.tex](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/main_lower.tex) match those calculations. The lower bound is restricted to sufficiently large even `N`. Accuracy is fixed before the limit, and changing it changes the signal-calibrated target class; `main_lower.tex:44–48` explicitly states this.

The abstract's common lower exponent `c=1/(3α)` and accuracy exponent `b=1/3` are weaker summaries of the two actual alternatives. The inequalities at `appendix_benchmarks.tex:653–660` justify the weakening. They do not close the upper/lower exponent gap, and line 664 explicitly says so.

## Public row-selector invariance

Evidence: [row_selector_invariance.tex](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/proofs/row_selector_invariance.tex).

The proof uses precisely three selector obligations: the returned row is a subset of the candidate row, its size is at most `Δ`, and it equals the candidate row whenever that row has size at most `Δ`. The selector is deterministic from currently available public information, costs no additional submission or commit, and cannot inspect future colors. Under successful screening, low-degree rows remain exact; other rows need only satisfy the cap. Thus the original structural and resource arguments can be reused without proving that high-degree selected rows contain only genuine neighbors.

The statistical comparison must be reconstructed for the *chosen* selector. The TV argument compares that selector's actual execution with its own safe controller. The KL argument uses its own exact-joint reference process, and charges failed reference paths by `N log V`. It does not infer KL from a TV coupling or compare sample paths from two different selectors. The inspected source preserves these distinctions.

Formalization priority: package a `RowSelector` interface with its three properties and information availability, then parameterize screening/structural theorems by it. A theorem abstractly assuming the screen contract is useful but does not by itself verify that an implementation of the selector obeys the no-future-randomness requirement. Local arithmetic and memory are intentionally outside the resource guarantee.

## The comparison path: class membership and dependence measures

Evidence: [appendix_comparison.tex](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/appendix_comparison.tex), proposition at lines 104–138 and proof at 140–522.

The construction fixes `p=2^(-α)∈(0,1/2)` and uses a positive two-type joint table `J` with both marginals `(1−p,p)`. Its row/column sums normalize the token kernel and establish stationarity. The detailed-balance calculation verifies either path orientation.

For complete-boundary response, the type odds have multiplier `r_A=(2−3p)/(1−p)` or `r_B=p/(1−p)`. A readout has at most one other neighbor, so only three positive response values `D(1),D(r_A),D(r_B)` arise; their minimum is a positive constant depending only on `p`. Within-type token emissions cancel in TV. This gives UEN uniformly over vocabulary size and boundary.

For RT, thresholds below the heavy atom `1−p` contain only type B, giving response zero. At larger thresholds the response bound `D(q)≤1−p` follows from the explicit odds-ratio maximum `(sqrt(r_A/r_B)−1)/(sqrt(r_A/r_B)+1)` and the positive polynomial `4−6p+4p²`. The RF check uses the heavy first atom, the second mass `p/2≤2^(−α)`, and background mass at most `1/V`; the `V=3` tie does not break the bound. These checks use `N,V≥3` and fixed `α>1`.

For TC, forest entropy factorization reduces the sum to edge mutual informations. Type emission factors cancel in the likelihood ratio. `det J=p(1−2p)/2>0` shows a non-product adjacent type table, so each edge contributes the same positive constant independent of `V`.

For DTC, direct subtraction of the chain-rule and Markov-neighbor conditional entropies gives `I(X₁;X₂)+Σ_{i=2}^{N−1} I(X_i;X_(i+1)|X_(i−1))`. Conditioning on the previous type multiplies the two rows of `J` by positive factors, preserving a nonzero determinant. Each interior term is therefore a fixed positive constant, and binary types bound it above by `log 2`. The token/type conditional mutual information equality is explicitly justified by emission cancellation, rather than assumed from data processing in the wrong direction.

Formalization dependency: finite entropy/KL-zero characterization → chain rule and Markov separation → type-emission transport → positive determinant/non-product lemma → uniform positive constants → exact linear formulas → `Θ(N)`. This is a separate moderate-size formalization project; the already-proved finite KL calculus is only a foundation. It should follow the main sampling bounds in priority, but it cannot be omitted if claiming all mathematical propositions have been verified.

### Effective TC

Evidence: `appendix_comparison.tex:541–706`. The source's formula and upper bound agree with [arXiv:2602.15008v2, Eq. 16 and Lemma 16](https://arxiv.org/html/2602.15008v2). The manuscript correctly does not infer large effective TC merely from large TC/DTC.

The mask expansion contributes `λ²` for the two visible endpoints. Restricting exterior reveal sets to include both outer neighbors contributes another `λ²`. Complete conditioning on those neighbors isolates the pair; its two-type conditional table is a positive row/column scaling of the transition matrix and remains non-product. Taking the minimum over four boundary-type pairs supplies a positive vocabulary-independent constant. There are `N−3` interior edges, counted twice in the ordered pair sum, yielding `2(N−3)c_pair exp(−4t)`. The integrated multiplier is `(1−exp(−4))/16>0`. The cited upper bound by DTC completes linear growth.

Formalization must track ordered versus unordered pairs, independence of mask bits from the data, conditional data processing at each boundary value, and integration of a nonnegative finite sum. A proof for unconditioned adjacent mutual information would not suffice here.

## Quantitative external-source checks and units

Evidence: [appendix_oracle_comparison.tex](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/appendix_oracle_comparison.tex) and [main_resource_table.tex](../../manuscript_2026-09-17/proposals/2026-09-17_c4_terms_and_figures/src/sections/main_resource_table.tex).

- [Anari et al., arXiv:2408.09442v1](https://arxiv.org/pdf/2408.09442v1): Theorem 2 and the query-efficient Algorithm 4 support the exact-row/exact-output row. The proof explicitly states `O(N)` expected queries for that implementation; the table's expected qualifier is appropriate. For polynomial vocabulary, the depth has the stated `N^(2/3)` power up to logarithms.
- [Autospeculation, arXiv:2511.07869v1](https://arxiv.org/pdf/2511.07869v1): Theorem 27 supports `O(N log N)` expected sampling/density queries and the stated square-root depth. Full rows implement either query type at one submission each. Remark 32 separately requires row TV at most `τ/N` for output TV and at most `N^(−3/2)` to retain the resource bounds. The manuscript keeps both requirements and labels the output as mixed-law TV, not mean seedwise TV.
- [Li–Cai, arXiv:2505.21400v2](https://arxiv.org/html/2505.21400v2): Definition 1 and Theorem 1/Corollary 1 use data/mask/time-averaged predictor error and schedule-averaged forward KL. The mutual-information sum equals `TC+DTC` by the definitions. Near-balanced blocks give the manuscript's `O((TC+DTC)/K)` term; singleton blocks remove that factorization term. No uniform counterfactual error condition is supplied by this result.
- [Chen et al., arXiv:2511.04647v2](https://arxiv.org/html/2511.04647v2): Definition 2.1 already returns all remaining conditional marginals per partial assignment. Theorem 1.9 has exactly the displayed `2+(1+log N)(1+ceil(T_hat/ε))` bound and schedule-averaged forward KL. The supplied TC/DTC bound is an input assumption; the table retains it.

Row queries can be simulated by full-row masked-state submissions. This is an upper-bound conversion, not equality of optimal complexities or a claim that external verification algorithms are admissible irreversible product-commit samplers. Their accept/reject and remasking capabilities differ. The manuscript explicitly identifies the external entries as sufficient bounds and says linear dependence-measure substitutions do not show those algorithms require linear work (`appendix_comparison.tex:524–534`, `appendix_oracle_comparison.tex:203–219`). Preserve that wording.

## Main claims and completion priorities

The abstract, main setup, main lower theorem, related-work comparison, and conclusion consistently limit the result to hidden forests, the stated public regularity/scaling assumptions, a frozen approximate conditional oracle, and irreversible product commits. They claim sublinear oracle submissions, not sublinear local arithmetic or measured runtime of learned denoisers. The conclusion leaves closing the tradeoff gap and extending beyond forests open. No stronger lower bound for the KL class is claimed.

Suggested order for remaining all-paper verification:

1. Complete the operational lower/upper chains; these are prerequisites for the calibrated main claims.
2. Formalize finite hard-family inclusion and the scalar finite calibration, including floors and class quantifiers.
3. Package selector invariance and public/pathwise resource parameters with the screen contracts.
4. Prove the fixed-accuracy asymptotic deductions, keeping fixed-accuracy and optional joint-limit regimes separate.
5. Formalize the independent comparison-path proposition and then effective TC, using a documented finite-information-theory library.
6. Keep external theorem verification as versioned source evidence; do not silently turn literature claims into custom Lean axioms and count them as locally proved results.

## Checked extension: public row-selector invariance

The earlier selector section was a source audit. Its main finite proof obligations are now connected to actual executable programs in separate, built modules; the original standard-selector modules were preserved.

- `RowSelectorInvariance.lean` proves that `PublicRowSelector`'s subset/cap/nonoverflow laws are equivalent to the manuscript's candidate-minus-dropped-set construction, including the exact excess-cardinality condition. An arbitrary legal overflow deletion rule constructs the interface via `ofDropRule`.
- `SelectedPackedSampler.lean` defines an actual `Program` loop with an arbitrary public `Policy`, an arbitrary retained-memory type, and an initial-memory function of the public all-mask reply. At each screen, the policy sees the current committed history, the current color block, and the completed list of actual state/reply observations. Its memory update may retain the whole available public transcript. Neither the target/oracle object nor future color blocks are inputs to the policy. `loop_withinBudgets` and `sampler_withinBudgets` prove all-path hard caps for this executable.
- `SelectedPackedFailure.lean` marks the chosen policy's own first failed screen and proves the actual fresh-block adaptive union bound by recursion generalizing over public memory. `mean_markLoop_le_budget` applies to arbitrary batch kernels, including oracle products and the true joint reference. `sampler_reached_screen_failure_le` is the exact retained-event version. No generic future-independence invariant is assumed.
- `SelectedPackedStructure.lean` proves the actual selected loop's successful-prefix safety, using the concrete selected rows, shared forest contraction/peeling bounds, and actual remaining fuel. `samplerMarker_safeBeforeStop` has only the finite manuscript model, oracle, margin, and cap hypotheses; no successful-row or abstract safety premise remains.
- `SelectedPackedParameters.lean` gives `manuscript_program_withinBudgets`, with exactly the standard finite query and round formulas, actual preprocessing banks, and the zero-column early exit.
- `SelectedPackedUpper.lean` proves `SelectedPackedSampler.manuscript_finite_hellinger_upper` and `manuscript_finite_kl_upper` for every such `Policy` and `initialMemory`. The TV bound is `ρ+η`; the forward-KL bound is `Nκ+N log(V)η`. Each proof uses that policy's own safe rule and joint reference. There is no asserted equality of paths or errors between distinct selectors.
- `SelectedGridUpper.lean` proves `SelectedThresholdGrid.grid_seedRisk_le`, `grid_robustRisk_le`, and `grid_seedKLRisk_le` for the original actual public dyadic grid and arbitrary policies. `SelectedPackedRates.lean` connects their actual all-path query counts to the controller-independent rate algebra: `program_within_queryCount` and `program_benchmark_rate_envelopes` use actual RF and row accuracy to establish the same bank/query/round envelopes, rather than assuming bank power estimates. Existing benchmark scalar and limit lemmas can therefore be applied to the unchanged finite expressions; no separate claim that selectors share output laws is used.
- `SelectedPackedDepth.lean` proves `SelectedPackedSampler.manuscript_sampler_pathwiseOracleDepth`. Every retained execution has an actual `Program.GroupedOracleTrace`, and its depth satisfies the printed bound `1+depth ≤ 1+actualCommitRounds+(phaseCap+1)`. The first `1` is the distinguished all-mask call. All screen query states are fixed before the grouped replies; this is not merely a scalar allowance assigned to the program.

Validation: final aggregate `lake build ForestSampling.SelectedGridUpper ForestSampling.SelectedPackedRates` passed (8803 jobs), and `SelectedPackedDepth` built (8754 jobs). Earlier aggregate `SelectedPackedUpper` built (8763 jobs). Fourteen key axiom checks covering selector representation, actual budgets, adaptive failure, successful-prefix safety, both finite losses, grid/robust losses, benchmark envelopes, and pathwise grouped depth return only `[propext, Classical.choice, Quot.sound]`. No source `sorry`, `admit`, or custom axiom occurs. Only unused-section-variable linter warnings remain. These nine modules are frozen after the checks. Local selector computation and memory remain outside the paper's oracle-resource accounting. A separate arbitrary-token relabeling task concerns the public lower theorem, not this selector proof.
