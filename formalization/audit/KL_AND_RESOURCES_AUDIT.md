# KL risk and resource semantics integration

`FiniteKL` proves the exact retained sigma KL chain, exponential Jensen
comparison, KL nonnegativity, finite entropy bound, product-marginal
KL decomposition, and total-correlation bounds. `ProgramKL` connects these
facts to the actual irreversible sampler using the independently proved
replay equivalence and joint-reference target identity. It bounds row KL by
`N*kappa` and total correlation by `N*log|V|` on every reference path.

`KLOracle` records the exact-to-oracle direction and the seed-averaged risk
rather than risk of the mixture. The calibrated KL class is proved to imply
the Hellinger class. `KLRisk` first establishes actual output positivity and
a global finite KL bound; those give genuine integrability from seedwise
measurability. It then proves the expected `N*kappa+N*log|V|*eta` bound when
good paths have factorizing batch conditionals and mean failure mass is at
most eta under the joint reference. The actual screen must still discharge
both hypotheses. No conversion of TV coupling into KL is used.

`OracleBudgets` fixes a confirmed specification mismatch without weakening
the original interface: actual fixed-oracle replies define a separate
pathwise budget predicate, and this predicate is proved equivalent to both
retained-path counters (for nonempty vocabulary). This is the appropriate
interface for the finite upper query bound depending on the realized bank.
The old universal-reply budget implies the new predicate, not conversely.
The distinguished all-mask read remains outside the query counter.

`HardMidpoint` separately instantiates the existing lower calculus with the
current explicit hard family and independent uniform instance prior. Its
joint outcome space retains both instance and actual adaptive path. Expected
penalty equals prior Hellinger loss; converting to TV before seed integration
connects any valid process penalty estimate to the genuine minimax infimum.
The collision penalty itself is still an explicit remaining obligation.
