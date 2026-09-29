# Actual balanced main upper theorem

`ForestSampling/MainUpperTheorem.lean` assembles the concrete upper sampler with finite resource bounds and eventual benchmark feasibility. Its 10 public theorems are built; every theorem has been checked with `#print axioms` and uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact statement and quantifiers

`balanced_grid_upper_eventually` assumes fixed `0 < radius ≤ 1`, `ζ > 1`, vocabulary exponent `growth > 1/3`, an error sequence tending to zero, and literal eventual cardinality `card(V N) = N^(growth + error N)`. Each vocabulary has its ordinary finite/order/nonempty instances.

For all sufficiently large lengths, it fixes the actual public parameter object before quantifying over targets or frozen oracles:

- benchmark signal is the existing concrete `benchmarkSignal N radius`;
- the degree cutoff and chunk parameter both equal `ceil((N signal^(1/ζ))^(1/3))`;
- response and frequency constants are one, the tail allowance is `signal/2`, and the failure allocation is `radius`;
- the threshold is the maximum feasible point of the original public clipped dyadic grid;
- phases, repetitions, color count, and the hard round allowance are the exact manuscript formulas.

For every forest target and ranking satisfying actual RF, RT, and UEN conditions, the same sampler has measurable risk and robust TV risk at most `2*radius` over the full frozen Hellinger oracle class. For every accurate frozen oracle, every seed, and every retained commit path, its queries and rounds satisfy one common public query cap and the actual public hard-round cap. The query cap does not depend on the target, ranking, oracle, or observed bank.

## Rates and connection to the algorithm

The proof derives actual observed-bank cardinality from RF and actual oracle accuracy, then applies the concrete program's all-path resource theorem. It enlarges that count to the ceiling of the explicit balanced query envelope. No assumed bank rate, assumed screening success, assumed structural safety, or existential oracle-dependent budget replaces this connection.

The public query cap is at most the explicit envelope plus one. The query envelope is a fixed constant times `balancedScale * (1+log(N+1))²`; the round envelope is a fixed constant times `balancedScale * (1+log(N+1))`. `UpperRates.balancedScale_benchmark` identifies the exact common scale as

`2^(1/(3ζ)) * N^(2/3 + 1/(9ζ)) / radius^(2/(9ζ))`.

`queryCap_isLittleO` and `roundCap_isLittleO` separately prove the actual integer caps are `o(N)`, including all logarithmic and rounding losses. The eventual cutoff and finite grid margin are derived from `UpperFeasibilityGrowth`, not supplied as rate assumptions.

## Scope

This module completes the fixed-accuracy Hellinger-to-TV main upper construction. The finite forward-KL sampler theorem is in `GridUpperTheorem`; its separate benchmark logarithmic allocation is not asserted by this module. Grouped oracle-depth accounting and arbitrary public row-selector extensions are separate modules. The general appendix regime with varying accuracy is not identified with this fixed-radius theorem.

## Validation

`lake build ForestSampling.MainUpperTheorem` completed successfully (8801 targets). The dedicated 10-theorem axiom audit completed successfully. No `sorry`, admitted result, or additional axiom appears in either this module or its rate assembly.
