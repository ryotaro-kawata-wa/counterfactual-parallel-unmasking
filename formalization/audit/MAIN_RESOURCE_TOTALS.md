# Actual balanced total calls and depth

`ForestSampling/MainResourceTotals.lean` adds the aggregate resource conclusions for the existing balanced TV and forward-KL samplers. It imports the frozen `MainUpperTheorem`, `MainKLUpperTheorem`, and `PackedDepth` modules, without depending on the general-cutoff curve being developed separately.

`Sampler.WithinTotalOracleCalls` counts every retained execution's actual preprocessing call, probe count, and nonempty commit count. The generic implication from `WithinOracleBudgets` uses the proved actual retained-path counter theorem; the total is `1 + Q + R`. It is uniform over seeds and all batch values, including executions whose screening fails.

The public balanced depth cap is `1 + roundCap + (phaseCap N balancedCutoff + 1)`. `tv_parameters_withinOracleDepth` and `kl_parameters_withinOracleDepth` instantiate the genuine grouped-query-depth proof for the actual original parameter objects. The KL failure allocation and repetition count remain unchanged. Fixed-input queries within one screen form one simultaneous group; commit calls contribute their own stages. The TV and KL total-call theorems apply their actual oracle-specific bank/counter bounds to the retained executions.

`screenCap_isLittleO` derives sublinearity from the proved finite screen envelope, its logarithmic bound, and `UpperRates.power_logWeight_sq_isLittleO` at power zero. `depthCap_isLittleO`, `tvTotalCallCap_isLittleO`, and `klTotalCallCap_isLittleO` then add the already proved rounded integer round/query cap limits and the single preprocessing call. Their hypotheses are fixed positive radius and exponent greater than one, with no assumed rate estimate.

`tv_totalGuarantee_eventually` and `kl_totalGuarantee_eventually` combine the actual public sampler, its unchanged uniform error guarantee, grouped depth, and full-class total-call bound on the tail supplied by literal vocabulary growth. They also retain the explicit real total envelope `2 + queryEnvelope + roundEnvelope`; the second unit accounts for the query ceiling. The separately proved public caps are `o(N)`, so both total oracle calls and parallel oracle depth are strictly sublinear. The TV package uses the existing independent-radius guarantee `TV ≤ 2 radius`; the usual main substitution is radius = requested accuracy / 2. The KL package retains the original row and failure calibrations.

Validation: `lake build ForestSampling.MainResourceTotals` passed (8804 jobs; 253 lines), with no warnings introduced by this module. No previous source, aggregate import, or manuscript file was edited.

Eleven key axiom checks—including the actual total-call implication, all four little-o theorems, both actual depth and total-call transfers, and both eventual public packages—return exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or custom axiom occurs. The module is frozen after this audit.
