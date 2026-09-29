# Minimax verification audit

`ForestSampling/Minimax.lean` adds 28 proved theorems and two baseline-sampler definitions. It imports the existing mathematical interface without changing that interface.

Verified scope:

- A.e. strongly measurable seedwise TV loss is integrable under the stored probability law because its values lie in `[0, 1]`.
- Packaged and unpackaged seed risks lie in `[0, 1]`; upper bounds require the explicit existing TV measurability hypothesis.
- An explicit singleton-seed controller commits all positions independently in one batch. For `N = 0` it terminates without a commit. This witnesses feasible-sampler nonemptiness for every query budget when `R >= 1`, and for every round budget at length zero.
- Worst-case risk lies in `[0, 1]` for nonempty instance families and measurable losses. The relevant real `sSup` set is explicitly bounded above.
- Lower bounds pass from every feasible sampler to minimax only with explicit feasible-class nonemptiness, or with the proved positive-round witness. Upper bounds use an explicitly bounded-below real `sInf` set.
- For any finite prior, seed integration commutes with the finite weighted sum of TV losses. A prior-averaged TV lower bound for each controller seed of every feasible sampler therefore implies the same minimax lower bound. This proof uses only the TV measurability already stored in `BudgetedSampler`; it assumes no Hellinger-affinity measurability.

Validation on Lean 4.33.0 and the pinned mathlib release:

- `lake env lean ForestSampling/Minimax.lean`: passed without warnings.
- `lake build ForestSampling.Minimax`: passed; inherited modules replay their existing linter warnings.
- `#print axioms` for all 28 new theorems: only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms.

The lower-bound collision argument, hard-family membership, upper sampling algorithm, and manuscript main theorems are not proved by these order/probability bridges. No empty-index convention is used to claim a nontrivial minimax bound. The root import file is intentionally unchanged pending integration.
