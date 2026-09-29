# Manuscript-to-Lean interface correspondence

This is a translation audit, not a theorem generated from TeX. Its baseline is
exactly the compiled inputs hashed in `claim_inventory.json`. Lean checks the
formal statements below; the interpretation of the manuscript remains a
human-readable audit obligation.

## Target, regularity, and frozen oracle

- `ForestModel` contains the strictly positive finite target, actual undirected
  acyclic graph, one reference rooting, positive endpoint kernels, S0 for that
  rooting, and C0 on both orientations. `History` stores only committed values;
  `CompleteBoundary` really fixes every position except source and readout.
  `ForestConditionals` derives the needed residual conditional factorizations
  from these data; residual Markov structure is not an added model axiom.
- `tailSet` uses exact marginal mass <= t. `TailResponseRegular` is the
  pointwise version of the finite maximum over tail pairs. Empty tails are
  vacuous; singleton tails use TV(p,p)=0. It quantifies all distinct positions
  and every complete boundary. `EdgeNondegenerate` quantifies both ordered
  orientations, so its two bounds are exactly the minimum in UEN.
- `FiniteRankFrequency` quantifies a decreasing marginal ranking. It does not
  fix a tie-breaking convention, but every tie has the same mass, so the bound
  is invariant under the manuscript's public tie order. Actual bank-size bounds
  are derived from RF; a bank-size rate is not inserted as an assumption.
- `MaskedState` uses `Option V`; `none` is the fresh mask. `FrozenOracle` is one
  deterministic map, with a strictly positive full vocabulary row at every
  valid masked coordinate. The exact row conditions on all revealed values.
  Uniform squared Hellinger is rho^2/(2N), with H^2=1-affinity. Forward KL is
  exact-row || oracle-row, not the reverse divergence.
- Public class and eventual theorems put parameters, vocabulary sequences,
  and their deterministic o(1) remainder before target/oracle quantifiers.
  The main RF specialization uses response exponent/constant and frequency
  constant equal to one, as does the manuscript.

## Controller observation and resources

`ObservedProgram`, rather than the older `Program` alone, is the complete
ordinary controller interface for the lower bound. A commit chooses a nonempty
fresh batch before its reply, then observes both the batch probability vectors
and sampled values. The product law is the actual oracle product, with no
filtering or resampling. A query preserves the committed history. Both operation
types enforce no remasking. `done` requires completion.

A query returns all masked rows; this is an allowed readout set and subsumes
any smaller requested set by ignoring rows. Upper screening submissions mask
exactly their needed readout chunk, so the finite bandwidth statement is also
proved (`scheduledSubmission_masked_card_le`). The initial all-mask submission
is separated from Q and is included in total calls and sequential depth.
Providing this deterministic initial reply before the ordinary controller is
also a valid strengthening for the lower bound.

The lower proof compiles observed commits to a free current-history read followed
by the already chosen product commit. `eval_compile`, actual budget preservation,
and seed-risk equality are proved. `FreeMarginalDisclosure` proves that these
extra current-marginal reads produce no new surviving trigger tests, while
retired candidates and posterior fibers are handled explicitly. The stronger
free-read collision and risk theorems therefore imply the full observed lower
bound. **The old value-only commit theorem alone would not be sufficient.**

The formal programs are well-founded finite controller trees. Every controller
with a finite all-path Q/R budget can be unfolded into such a tree on actual
paths; unreachable invalid replies can be completed with a legal fallback.
This representation argument is part of this translation audit, not a parser
from arbitrary executable controllers. Seed probability spaces remain arbitrary;
only the seedwise loss measurability required for the integral is imposed.
Commit randomness is supplied by independent distribution binds after fixing
the seed. Risk is the integral of seed-conditioned TV or forward KL, rather
than divergence of the seed-mixture output.

`WithinOracleBudgets` charges actual frozen replies and every possible sampled
batch value, for every seed. Strictly positive rows make all finite sampled
batch values possible. `PackedPathDepth` uses legal fixed-input parallel query
groups; it does not relabel a sequential query count as parallel depth.
`SuccessfulPathResources` additionally proves the manuscript's sharper
successful-path round count for actual retained paths.

## Vocabulary, selected rows, and finite constructions

The hard family initially uses a bank/background sum type. This is now only an
implementation choice: `VocabularyEquivalence`, `VocabularyModelTransport`, and
`ObservedVocabularyTransport` prove exact pushforward/pullback of target,
boundary conditionals, oracle rows, full observed controllers, Q/R, risk and
class membership. `ArbitraryVocabularyLower` and `ObservedBenchmarkLower`
apply to any preselected finite vocabulary of the required size.

`GridPreprocessing` implements the maximal feasible clipped dyadic threshold
from public data before replies. `ScreeningPreprocess`, `ScreeningProbes`, and
`ScreeningSelector` implement actual observed banks, public tail representative,
zero-query draft, and the public order used for votes. `SelectedPackedSampler`
allows a public, memory-dependent admissible selector, with actual finite
TV/KL bounds, all-path resources, grouped depth, and successful-path rounds.

The matching midpoint law and survivor ledger are analytical proof objects;
they are not extra information exposed to the sampling controller. Original
specification-only declarations in `PaperStatements`/`CurrentStatements` remain
legacy contracts; final inventory entries cite proved observed-controller
and actual-sampler theorems instead.

## Reading the coverage table

A named statement may map to a bundle of Lean declarations rather than one
syntactically identical theorem. Natural ceilings, explicit constants, and
finite feasibility conditions remain visible. Eventual theorems derive the
conditions from literal public vocabulary growth. The lower alternative is
pointwise for every sufficiently large even N; it does not select one disjunct
that must hold for the entire sequence.

This audit does not certify every unlabelled sentence, literature comparison,
experimental conclusion, citation, or exposition choice. Those require a
separate manuscript review. No mathematical TeX input was modified to make a
formal theorem easier to prove.
