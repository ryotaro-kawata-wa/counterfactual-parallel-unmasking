# Actual balanced main KL upper theorem

`ForestSampling/MainKLUpperTheorem.lean` is built with 12 public theorems. Every theorem's `#print axioms` report contains only `propext`, `Classical.choice`, and `Quot.sound`; there are no admitted proofs or new axioms.

## Actual algorithm and loss

The parameter constructor uses the original maximal feasible clipped-dyadic threshold, equal degree/chunk parameter `ceil((N*signal^(1/ζ))^(1/3))`, and the exact public manuscript phase, repetition, color, and hard-round caps. The signal is the existing `benchmarkSignal N radius`.

The forward-KL row allowance is exactly `radius²/N`. The screen-failure allocation is exactly `radius²/(N log(card V))`. The proven seed-averaged forward KL has the target in its first argument. Both error contributions equal `radius²`, so the actual original sampler has loss at most `2*radius²` for every frozen oracle in that full forward-KL class. Measurability is included. The sampler and one common public query cap are chosen before the target/ranking/oracle quantifiers.

`balanced_grid_kl_upper_eventually` discharges public finite feasibility from fixed positive radius, `ζ>1`, and literal vocabulary growth `card(V N)=N^(growth+error N)`, with `growth>1/3` and `error→0`. In particular, it derives `log(card V)≥1` and

`failureBudget ≥ [radius²/(growth+1)] / N²`

from the literal growth assumption. No repetition-rate assumption replaces this step. RF and actual oracle accuracy bound the observed banks, the real program resource theorem supplies the path budgets, and the resulting public integer query cap is bounded by its explicit squared-log envelope plus one.

## Main single-accuracy specialization

`balanced_grid_kl_target_error_eventually` uses the same public radius `epsilon/2` in the class and sampler and proves actual output KL at most `epsilon`, for `0<epsilon≤1`. The stronger intermediate guarantee is `epsilon²/2`. The target-independent query/round caps and the actual sampler are preserved by this specialization.

`queryCap_isLittleO` formally proves the complete integer KL query cap is `o(N)`. Rounds use exactly `MainUpperTheorem.roundCap`, whose integer little-o theorem is already proved. Both envelopes share the exact scale `2^(1/(3ζ))*N^(2/3+1/(9ζ))/radius^(2/(9ζ))`. The generic-radius theorem also supports the separate appendix calibration `radius=sqrt(epsilon/2)`; no unproved assertion about that substitution is needed for the main single-accuracy result.

## Scope and validation

The theorem gives uniform bounds for every target satisfying the actual RF/RT/UEN predicates and every accurate frozen forward-KL oracle. It does not replace seed-averaged KL by KL to the seed-mixture output. Grouped oracle depth and public row-selector extensions are separate modules.

`lake build ForestSampling.MainKLUpperTheorem` passed (8802 targets). All 12 theorem axiom checks passed. This module is frozen for integration.
