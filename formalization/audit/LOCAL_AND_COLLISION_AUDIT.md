# Local hard-edge facts and quantitative collision consequences

`HardEdgeDistance.lean` proves the likelihood upper ratio 2, exact edge
chi-square `lambda^2`, and edge Hellinger interval `[lambda^2/12,lambda^2/2]`.
A two-point expectation formula gives the edge affinity independently of both
private trigger labels. The exact endpoint TV response is
`lambda * abs(feature(a)-feature(a'))`; it is at most lambda and a trigger /
background pair attains lambda. These results use the actual normalized hard
edge distributions from `HardMatching`, not abstract distance assumptions.

`CurrentStatements.lean` removes the obsolete global finite-separation
hypothesis in a new parameter structure, preserving the legacy interface.
The current nonlinear minimax statement is explicitly a **definition of a
proposition**, still unproved. Its target-error consequence is proved with
constants 98304 and 786432, conditional on the substantive lower estimate.
The selected-oracle accuracy wrapper discharges the previously exposed
exact-row hypothesis using `HardMatching.exactRowCharacterization`.

`CollisionBudget.lean` proves two separate analytic implications:

1. The adaptive hazard recurrence with denominator `K-k` yields unconditional
   disclosure probability at most `k/K` (including the terminal k=K case).
2. From `E D <= N/8`, the activity bound on `D <= N/4`, and
   `E exp(-Z+A/64) <= 1`, it proves `Pr(Z >= N/(8192 R)) >= 1/4` when
   `1 <= R <= N/16384`. A pointwise event-covering inequality proves the
   intermediate `1/2-exp(-N/(8192 R))` bound.

These are conditional process estimates: the concrete survivor posterior,
actual query hazard, pathwise activity ledger, and compensated matching
Laplace expectation are not assumed to be established by writing these
lemmas. They must still be supplied from the real midpoint execution.

`MatchingLaplaceConstants` checks the integer quarter-exposure inequalities,
including sizes 4 through 7, and the constant-32 exponential comparison for
both large and small batches. `NonlinearPenalty` checks that the actual hard
instance/midpoint process's pointwise exponential penalty and constant tail
would imply the current `98304` minimax value via the already-proved seed
bridge. Its two actual process estimates remain explicit hypotheses.
