# Uniform upper curve and successful-path resources

`GeneralUpperCurve` assembles the actual public dyadic packed sampler for every
public cutoff 9 <= D <= N-1, with L=D. Parameters are fixed before the target,
ranking, and frozen oracle. Its TV allocation is exactly eta=rho/2, giving
robust seed-averaged TV <= 3rho/2. Its KL allocation is exactly
eta=rho^2/(N log V), row KL <= rho^2/N, and output KL <= 2rho^2.
The finite seed loss is measurable.

`tv_curve_eventually` and `kl_curve_eventually` derive uniform feasibility from
literal V=N^(growth+error(N)), error->0, growth>1/3. The query cap is one public
integer ceiling. Its envelope is bounded by an explicit constant times
signal^(-1/zeta) D^2 logWeight(N)^2. The round cap and actual grouped-depth cap
are bounded by explicit constants times (N/D)logWeight(N), including the
initial preprocessing stage. There is no surrogate bank or depth premise.

Setting rho=epsilon/2 yields TV <=3epsilon/4 and KL <=epsilon^2/2, which imply
the weaker main-text guarantees. The independent KL appendix parameter is
kappaOutput=2rho^2 (equivalently rho=sqrt(kappaOutput/2)). Existing calibration
lemmas establish the square-root substitutions.

`SuccessfulPathResources.sampler_successful_rounds_lt` proves the sharper
strict successful-path round bound for the actual sampler and its actual
repair marker. Terminal exact rows and enough centroid fuel exclude fallback;
each peeling stage costs at most ceil(4N/D)-1. The bound is therefore not
merely a standalone combinatorial inequality about an abstract iteration.
`SelectedPackedSampler.SuccessfulResources.selectedSampler_successful_rounds_lt`
proves the same statement for every public memory-dependent admissible selector.

Validation: the three source modules check against the pinned Lean/mathlib
runtime. Root imports include them for the exhaustive transitive axiom audit.
Balanced total/depth little-o packaging is recorded separately in
`MainResourceTotals` when integrated.
