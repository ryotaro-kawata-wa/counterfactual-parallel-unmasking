# Uniform-matching Laplace theorem audit

`ForestSampling/MatchingLaplace.lean` proves the actual standalone combinatorial lemma `app:lem:matching-collision-laplace` from the current manuscript's `src/sections/proofs/lower_matching_laplace.tex`.

Final exported theorem:

`PerfectMatching.uniform_internalEdgeCount_laplace`

For even `N >= 2`, any finite subset `S` of `Fin N`, and every `s >= 0`, it proves

`E[exp(-s * Z_S)] <= exp(-(1-exp(-s)) * (max(|S|-1,0))^2 / (32*N))`,

where `Z_S` is the natural cardinality of matching edges contained in `S`, counted once through their smaller endpoint. The positive part is represented by natural subtraction `S.card - 1`. The proof includes `s = 0`, slightly extending the manuscript's positive-parameter statement.

Proof chain:

1. Finite expectation and conditioning identities, including total expectation over a readout with positive-probability fibers.
2. An explicit matching on two exposed endpoint labels; a single mate equation is exactly its extension event.
3. Exact conditional uniform law on the remaining vertex subtype, using `MatchingCollision`.
4. Exact internal-edge recurrence after exposing one edge. A proved cardinality identity equates the intermediate half-endpoint representation with the literal natural edge count.
5. Induction on the number of exposures over arbitrary survivor types. For disjoint starting/target subsets with `|A| >= 2m`, `|B| >= m+r`, and at most `n` ambient vertices, it proves the genuine uniform-matching transform bound `(1-(1-exp(-s))*r/n)^m`.
6. Near-half partition and quarter exposure count, followed by the verified arithmetic in `MatchingLaplaceConstants`. Sets of size two or three use one exposed endpoint; sets of size at most one use the universal transform bound by one.
7. Transport back to the original `PerfectMatching N` type and its existing uniform prior.

No independence between successive exposure successes is assumed. No conditional Laplace estimate, residual uniformity, or exposure probability is supplied as an unproved hypothesis: the relevant finite identities are derived in the dependency chain.

Validation:

- `lake env lean ForestSampling/MatchingLaplace.lean`: passed.
- `lake build ForestSampling.MatchingLaplace`: passed without warnings from the new module; existing dependencies replay their previous linter warnings.
- All 37 public theorems were checked with `#print axioms`. Dependencies contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms.

Remaining boundary: this closes the fixed-subset uniform-matching combinatorial lemma. It does not yet identify the paper's adaptive query/commit transcript distribution, including its midpoint tilt, with a conditional uniform matching law. That separate invariant is needed to apply this lemma inside the main adaptive lower-bound proof.
