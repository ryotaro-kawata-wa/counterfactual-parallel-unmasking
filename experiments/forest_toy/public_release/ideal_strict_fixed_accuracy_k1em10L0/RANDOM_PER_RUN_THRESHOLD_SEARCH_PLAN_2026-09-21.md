# Per-run random fixed-accuracy threshold search

The previous ideal-target rerun froze one random batch count `B` on a
development cohort and evaluated it once on six untouched runs.  A fresh
failure was deliberately retained as a failure.  That protocol estimates
holdout success of one fixed `B`; it does **not** estimate the query complexity
needed by each run to reach the target accuracy.

For the paper-facing fixed-accuracy curve, retain the completed proposal runs
and replace only the random measurement as follows.

- Use the same six evaluation pairs and the same per-tree absolute `K_star`.
- For each `(tree, N, data seed, algorithm seed)` independently, evaluate a
  common coarse grid of balanced-random batch counts including `B=N`.
- A point succeeds when `K + 2 MCSE(K) <= K_star`.
- Keep the random order and commit stream fixed within an evaluation run while
  changing `B`; otherwise repeated budget trials would also redraw the random
  partition and create a multiple-lottery advantage.  Balanced batches reuse
  the same random permutation.  Since adjacent balanced partitions are not
  strictly nested, select the first observed successful suffix: the selected
  budget and every larger observed budget must pass.
- Bisect each run's unsafe/safe bracket until its width is at most `0.05 N`.
  The exact singleton endpoint `B=N` guarantees termination.
- Plot the mean of the six selected `B_star` values with their minimum--maximum
  range.  This is an empirical per-run threshold search, not an untouched
  fixed-hyperparameter confirmation.

## Strict-accuracy follow-up

The runner also supports a uniformly scaled threshold.  The strict paper
follow-up uses `threshold_scale=0.01`, hence
`K_star = 1e-5 * L0_total`, for every tree and every `N`.  Proposal results are
reused because all saved fresh proposal runs are structural exact zeros.
Previously measured random KL values are threshold-independent and are
rescored under the strict threshold; only budgets needed to refine the new
unsafe/safe brackets are evaluated anew.  The sampler stream remains coupled
across all old and new budgets within each evaluation pair.
