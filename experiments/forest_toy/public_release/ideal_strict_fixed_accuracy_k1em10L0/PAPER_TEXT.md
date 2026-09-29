# Ideal-target fixed-accuracy experiment: paper text

This file is a self-contained handoff for adding the ideal-target experiment
to the paper.  It does not modify the active manuscript.  The proposed split
keeps the empirical conclusion and the comparison figure in the main text,
while placing target construction, tuning, evaluation, seed roles, and
compute details in the appendix.

## Main-text insertion

### Finite-size oracle-round scaling on ideal forest targets

We complement the asymptotic analysis with a controlled finite-size
experiment on four hidden forest families: matchings, paths, binary trees, and
growing stars.  The target uses constant edge strengths and an exact frozen
conditional oracle.  For each forest, we hold fixed across sequence lengths
the stringent total-error requirement
$K+2\operatorname{SE}_{\rm MC}\le K_\star$, where
$K_\star=10^{-5}L_0$ and $L_0$ is the empty-history product-commit KL at
$N=2048$.  Figure X reports the total executable oracle-round count
$Q_{\rm tot}=Q_{\rm pre}+Q_{\rm cf}+R$, including preprocessing,
counterfactual submissions, and commit rounds $R$.

Across $N\in\{8192,10240,12288,14336,16384\}$, the proposal's ratio
$Q_{\rm tot}/N$ is lower at the largest size than at the smallest for all four
forest families.  It uses fewer mean total rounds than the per-run tuned
random-order baseline at every tested size for matchings and growing stars,
and for paths from $N=10240$ onward; random ordering remains less expensive on
binary trees.  Thus the experiment supports sublinear finite-size scaling of
the proposal in the tested ideal regime, while also showing that its present
binary-tree tuning is conservative.  This is a descriptive finite-size
observation, not an additional complexity theorem or a wall-clock claim.

### Main-text figure caption

**Figure X: Fixed-accuracy round scaling on ideal forest targets.** The
vertical quantity is the total executable oracle-round count
$Q_{\rm tot}=Q_{\rm pre}+Q_{\rm cf}+R$, so it includes commit rounds $R$ and
is not the counterfactual-only resource $Q_{\rm cf}$.  Points are means over
six evaluation runs and whiskers show their minimum--maximum range (not
confidence intervals).  The proposal uses one setting frozen separately for
each forest and $N$; each random point averages six empirical minimum-safe
balanced-batch budgets, searched separately on coupled per-run budget curves.
All points satisfy $K+2\operatorname{SE}_{\rm MC}\le10^{-5}L_0$.  The dotted
line $Q_{\rm tot}=N$ is the exact sequential-singleton reference, not a cap.
Proposal whiskers are often contained within the marker because their full
six-run range is at most 78 rounds.

Paper-facing assets:

- [Raster figure (1-by-4, preferred)](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em5L0/ideal_strict_fixed_accuracy_linear_errorbars_1x4.png)
- [Vector figure (1-by-4, preferred)](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em5L0/ideal_strict_fixed_accuracy_linear_errorbars_1x4.pdf)
- [Figure metadata (1-by-4)](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em5L0/ideal_strict_fixed_accuracy_linear_errorbars_1x4.json)
- [Alternative 2-by-2 layout](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em5L0/ideal_strict_fixed_accuracy_linear_errorbars.pdf)

Stricter sensitivity version (same proposal cohort and random-search protocol,
but with $K_\star=10^{-7}L_0$):

- [Raster figure (1-by-4)](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em7L0/ideal_strict_fixed_accuracy_linear_errorbars_1x4.png)
- [Vector figure (1-by-4)](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em7L0/ideal_strict_fixed_accuracy_linear_errorbars_1x4.pdf)
- [Figure metadata](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em7L0/ideal_strict_fixed_accuracy_linear_errorbars_1x4.json)
- [Search audit](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em7L0/audit.json)

The proposal is reused without rerunning because every one of its 120 fresh
evaluation runs has structural exact zero discrepancy.  The random comparator
is rescored and refined separately on each coupled per-run budget curve under
the stricter threshold.

Current ultra-strict candidate (same protocol, but with
$K_\star=10^{-10}L_0$):

- [Raster figure (1-by-4)](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em10L0/ideal_strict_fixed_accuracy_linear_errorbars_1x4.png)
- [Vector figure (1-by-4)](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em10L0/ideal_strict_fixed_accuracy_linear_errorbars_1x4.pdf)
- [Figure metadata](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em10L0/ideal_strict_fixed_accuracy_linear_errorbars_1x4.json)
- [Search audit](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em10L0/audit.json)

This version reuses and rescores all 1,925 observations from the
$10^{-7}L_0$ search and evaluates 11 additional budgets.  All 120 selected
random endpoints pass the $10^{-10}L_0$ criterion; the unchanged proposal
cohort again has structural exact zero discrepancy throughout.

The $10^{-10}L_0$ result was also reproduced from an empty output directory
with no seed records.  The fresh run evaluated 1,566 budgets in 976.5 seconds
on `newton03` with eight workers.  It reproduced all 120 selected budgets,
all unsafe--safe brackets, and all 20 paper-facing random query summaries
exactly.  Across the 1,566 shared KL observations, success labels agreed
throughout and the maximum absolute floating-point difference was
$2.33\times10^{-12}$; at the selected endpoints it was
$1.57\times10^{-21}$.

- [Fresh-run audit](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em10L0_fresh/audit.json)
- [Fresh-run reproduction comparison](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em10L0_fresh/reproduction_comparison.json)
- [Reproduction-comparison script](verify_random_threshold_reproduction.py)

## Appendix insertion

### Ideal-target fixed-accuracy protocol

#### Target law

Let the vocabulary be $\mathcal X=\{0,\ldots,2047\}$ and define
$\phi(0)=1$, $\phi(1)=-1$, and $\phi(x)=0$ otherwise.  For a forest
$G=([N],E)$, the target law is

\[
P(x)\propto
\prod_{i=1}^N\mu_i(x_i)
\prod_{(i,j)\in E}\left(1+W_{ij}\phi(x_i)\phi(x_j)\right).
\]

The unary fields are generated as in the forest-toy construction: for
$h_i\sim\operatorname{Unif}[-1,1]$, the masses of tokens $0$, $1$, and the
remaining vocabulary are proportional to
$(0.4e^{h_i},0.4e^{-h_i},0.2)$, with the last mass uniform over the remaining
2046 tokens.  Within a target-data repeat, one master field vector is reused
by prefix across sequence lengths and forest families.  Vertex labels are
randomly permuted.  All edges have the same strength within a forest family,
so $\mathbb E[W/X]=1$, and the conditional oracle is exact.  The edge scale is
chosen so that the maximum incident edge strength is at most $0.5$:

| Forest family | Structure | Edge strength $X$ |
|---|---|---:|
| Matching | Disjoint pairs | $0.5$ |
| Path | One path | $0.25$ |
| Binary tree | Complete binary tree before relabeling | $1/6$ |
| Growing stars | At most $\max(16,\lceil\sqrt N\rceil)$ leaves per star | $0.5/\max(16,\lceil\sqrt N\rceil)$ |

We evaluate
$N\in\{8192,10240,12288,14336,16384\}$.  The proposal has no external
$Q_{\rm tot}\le N$ cutoff; the random baseline has the intrinsic exact
endpoint $B=N$, where every commit is a singleton.

#### Total round accounting and error metric

The reported resource is the total executable oracle-round count

\[
Q_{\rm tot}=Q_{\rm pre}+Q_{\rm cf}+R,
\]

where preprocessing, counterfactual submissions, and nonempty commit rounds
are each counted once and $R$ is the number of commit rounds.  This differs
from the main theoretical resource $Q_{\rm cf}$, which counts only
counterfactual submissions.  For the random balanced-batch baseline,
$Q_{\rm tot}=B$.

For commit batch $B_t$, let $q_{t,i}$ be the row used to sample position $i$
and let $P_t(X_{B_t}\mid H_t)$ be the exact joint target conditional.  We
evaluate the total forward discrepancy

\[
K=\sum_t\operatorname{KL}\!\left(
\prod_{i\in B_t}q_{t,i}\,\middle\|\,
P_t(X_{B_t}\mid H_t)
\right).
\]

Evaluation is passive and does not add oracle rounds.  Boundary factors of
arity at most four are enumerated exactly; larger factors use 128 independent
Monte Carlo draws per factor.  A run succeeds when it completes and
$K+2\operatorname{SE}_{\rm MC}\le K_\star$.  Structural exact zeros bypass
Monte Carlo evaluation and have $K=\operatorname{SE}_{\rm MC}=0$.

For each forest, define $L_0$ as the empty-history total KL between one joint
all-position commit and the product of exact one-position marginals at
$N=2048$.  We set $K_\star=10^{-5}L_0$ and keep this absolute total-KL
threshold fixed across all $N$ and both methods:

| Forest family | $K_\star$ |
|---|---:|
| Matching | $6.375289\times10^{-4}$ |
| Path | $2.801962\times10^{-4}$ |
| Binary tree | $1.226162\times10^{-4}$ |
| Growing stars | $5.138930\times10^{-7}$ |

#### Proposal tuning and strict-threshold reuse

Proposal hyperparameters are selected separately for each $(\text{forest},N)$
cell, but with one common staged procedure.  Screening varies representative
target-adapted $(p,d)$ facets, normalized preprocessing costs
$q_0/N\in\{0.4,0.8,1.2,1.6,2.0\}$, and two normalized screening thresholds.
The six lowest-round diverse candidates are evaluated on six development
pairs, and the minimum-mean-$Q_{\rm tot}$ candidate succeeding on every pair
is frozen before six fresh confirmation runs.

This proposal search originally used $K_\star^{(0)}=10^{-3}L_0$.  However,
all 720 retained-candidate development runs and all 120 fresh proposal runs
were structural exact zeros.  We therefore reuse the frozen proposal results
under $K_\star=10^{-5}L_0$ without rerunning or retuning them.  This reuse does
not grant a looser accuracy test to the proposal: every reused run has
$K+2\operatorname{SE}_{\rm MC}=0$.  It is conservative with respect to the
reported proposal round count because a new strict-threshold search could
retain the existing feasible setting or find a cheaper one; the binary-tree
panel indicates the largest remaining tuning opportunity.

#### Per-run random threshold search

The comparator partitions the uncommitted positions into balanced random
batches.  For each forest, $N$, target draw, and sampler stream independently,
we search its budget curve for the minimum observed safe batch count.  The
random permutation and commit stream are fixed while $B$ changes, preventing
each budget trial from receiving a new random draw.  Because adjacent balanced
partitions are not nested, an isolated passing budget is insufficient: we
select the first observed successful suffix, meaning that the selected budget
and every larger observed budget must pass.  Bisection continues until the
unsafe--safe bracket has width at most $0.05N$; the observed maximum width is
$0.03125N$.  The exact endpoint $B=N$ guarantees termination.

KL measurements do not depend on the later choice of $K_\star$.  We therefore
rescored 1,701 observations from the preceding $10^{-3}L_0$ search and
evaluated 195 additional budgets needed to refine the stricter brackets.  All
120 selected random endpoints pass the $10^{-5}L_0$ criterion.  This random
curve is an empirical per-run threshold-search estimand, not untouched
holdout performance of one globally frozen random budget; it intentionally
gives the comparator access to its own evaluation-run budget curve.

#### Replicates and error bars

Both curves use three target draws crossed with two sampler streams, for six
runs per $(\text{forest},N)$ point.  Target draws $196,197,198$ are shared;
proposal uses sampler streams $292,293$, whereas random uses disjoint streams
$294,295$.  A plotted point is the arithmetic mean of the six total round
counts.  Whiskers are the minimum and maximum over those same runs, not
standard errors or confidence intervals.  Proposal settings are frozen within
a cell, while each random value is the selected endpoint of its own coupled
budget curve.
Consequently the whiskers describe different operational sources of
variation and should not be interpreted as like-for-like estimator
uncertainty.  Proposal ranges are only 0--78 rounds, whereas the strict random
ranges can span several thousand rounds; the proposal whiskers are therefore
often contained inside the plotted marker.

#### Descriptive results

| Forest family | Proposal log--log slope | $Q_{\rm tot}/N$: first $\to$ last $N$ | Range of $Q_{{\rm tot},\,\rm random}/Q_{{\rm tot},\,\rm proposal}$ | Comparison |
|---|---:|---:|---:|---|
| Matching | $-0.074$ | $0.290\to0.149$ | $1.78$--$4.01$ | Proposal lower at all five sizes |
| Path | $0.149$ | $0.700\to0.398$ | $0.93$--$2.21$ | Proposal lower for $N\ge10240$ |
| Binary tree | $0.394$ | $1.097\to0.715$ | $0.61$--$0.84$ | Random lower at all five sizes |
| Growing stars | $0.152$ | $0.225\to0.124$ | $2.73$--$4.67$ | Proposal lower at all five sizes |

The slopes are ordinary least-squares fits of
$\log\overline Q_{\rm tot}=c+\alpha\log N$ over the five displayed proposal
points.  They are descriptive summaries only.  The decrease in
$Q_{\rm tot}/N$ and slopes below one support sublinear finite-size behavior
over this grid, but neither imply a new asymptotic guarantee nor a practical
wall-clock speedup.

#### Computation and reproducibility

The proposal search, confirmation cohort, and first 1,701 random budget
observations were run with eight worker processes on an Apple-silicon Mac mini
(`RyotaronoMac-mini.local`, macOS 15.7.7, Python 3.13.15, NumPy 2.2.2).  The
parent proposal/random experiment took approximately 64.7 minutes and the
initial per-run random search approximately 7.5 minutes.  The 195 strict
follow-up evaluations were run with eight workers on `newton05`
(Linux 5.4.0, Python 3.10.12, NumPy 1.26.4) and took 178.7 seconds.  BLAS and
OpenMP thread counts were fixed to one for the follow-up.  The audit verifies
all 20 cells, all 120 selected random endpoints, the singleton endpoints,
query identities, coupled random streams, and the recorded source and input
hashes.

Reproducibility artifacts:

- [Strict design](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em5L0/design.json)
- [Selected per-run random budgets](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em5L0/selections.json)
- [Random summary](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em5L0/random_summary.json)
- [Proposal confirmation summary](results/ideal_capless_fixed_accuracy_scaling/proposal_confirmation_summary.json)
- [Figure data](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em5L0/figure_data.json)
- [Execution history](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em5L0/execution_history.json)
- [Audit](results/ideal_capless_fixed_accuracy_scaling/random_per_run_threshold_search_k1em5L0/audit.json)
- [Preferred 1-by-4 figure-generation script](report_ideal_strict_fixed_accuracy_1x4.py)
- [Alternative 2-by-2 figure-generation script](report_ideal_strict_fixed_accuracy.py)

## Integration notes (not paper prose)

- Keep the main text to the two paragraphs and one figure above; the strict
  threshold, random estimand, and whisker definition should remain in the
  caption even if other details move to the appendix.
- Call the diagonal an exact sequential-singleton reference, not a cap.
- Preserve the distinction between total executable rounds
  $Q_{\rm tot}=Q_{\rm pre}+Q_{\rm cf}+R$ here and the theorem's
  counterfactual-only $Q_{\rm cf}$.
- Do not describe the per-run random curve as holdout performance of a frozen
  hyperparameter.
- Do not claim universal superiority: binary trees favor random under the
  present proposal tuning, and the smallest path instance is approximately a
  tie.
