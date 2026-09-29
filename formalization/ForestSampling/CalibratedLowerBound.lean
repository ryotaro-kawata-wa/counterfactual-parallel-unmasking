import ForestSampling.HardFiniteCalibration
import ForestSampling.CurrentLowerTheorem

set_option autoImplicit false

namespace ForestSampling

/-- The finite signal-calibrated target-error alternative for the actual
constructed matching family and its actual-oracle admissible sampler class.
The integer floor-division branches are converted to the real thresholds
printed in the manuscript. -/
theorem signalCalibrated_target_error_alternative (N V : ℕ) (signal exponent : ℝ)
    (hN : Even N) (hs0 : 0 < signal) (hs1 : signal ≤ (1 / 2 : ℝ))
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * signal)
    (Q R : ℕ)
    (A : InstanceFamily.OracleBudgetedSampler
      (signalCalibratedParameters N V signal exponent hN hs0 hs1 he hV).hardFamily Q R)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ))
    (hrisk : InstanceFamily.worstCaseRisk
      (signalCalibratedParameters N V signal exponent hN hs0 hs1 he hV).hardFamily A.1 ≤ ε) :
    (calibratedBank signal exponent : ℝ) / 8 < (Q : ℝ) ∨
      min ((N : ℝ) / 16384) ((N : ℝ) * signal ^ 2 / (786432 * ε)) ≤ (R : ℝ) := by
  let P := signalCalibratedParameters N V signal exponent hN hs0 hs1 he hV
  rcases P.oracle_target_error_alternative Q R A ε hε0 hε1 hrisk with hQ | hR | hround
  · left
    change calibratedBank signal exponent / 8 < Q at hQ
    have hnat : calibratedBank signal exponent < 8 * Q := by omega
    have hreal : (calibratedBank signal exponent : ℝ) < 8 * (Q : ℝ) := by exact_mod_cast hnat
    linarith
  · right
    apply (min_le_left _ _).trans
    have hnat : N < 16384 * R := by omega
    have hreal : (N : ℝ) < 16384 * (R : ℝ) := by exact_mod_cast hnat
    linarith
  · right
    exact (min_le_right _ _).trans hround

/-- The benchmark signal used for the Hellinger/TV finite calibration. -/
noncomputable def benchmarkSignal (N : ℕ) (radius : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (radius ^ 2 / (N : ℝ)) ^ (1 / 3 : ℝ)

/-- Its cube is exactly one quarter of the permitted cubic A2 budget. -/
theorem benchmarkSignal_cube (N : ℕ) (radius : ℝ) :
    benchmarkSignal N radius ^ 3 = radius ^ 2 / (8 * (N : ℝ)) := by
  unfold benchmarkSignal
  rw [mul_pow]
  have hx : 0 ≤ radius ^ 2 / (N : ℝ) := by positivity
  have hp : ((radius ^ 2 / (N : ℝ)) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) =
      radius ^ 2 / (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  rw [hp]
  ring

/-- Positive finite radius and positive sequence length give a positive
benchmark signal within the finite hard-family range. -/
theorem benchmarkSignal_bounds (N : ℕ) (radius : ℝ) (hN : 1 ≤ N)
    (hr0 : 0 < radius) (hr1 : radius ≤ 1) :
    0 < benchmarkSignal N radius ∧ benchmarkSignal N radius ≤ (1 / 2 : ℝ) ∧
      benchmarkSignal N radius ^ 3 ≤ radius ^ 2 / (2 * (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < radius ^ 2 / (N : ℝ) := div_pos (sq_pos_of_pos hr0) hNr
  have hx1 : radius ^ 2 / (N : ℝ) ≤ 1 := by
    apply (div_le_one hNr).mpr
    nlinarith
  refine ⟨by unfold benchmarkSignal; positivity, ?_, ?_⟩
  · unfold benchmarkSignal
    have hp := Real.rpow_le_one hx0.le hx1 (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    linarith
  · rw [benchmarkSignal_cube]
    have hpos : 0 ≤ radius ^ 2 / (N : ℝ) := hx0.le
    have hleft : radius ^ 2 / (8 * (N : ℝ)) = (radius ^ 2 / (N : ℝ)) / 8 := by ring
    have hright : radius ^ 2 / (2 * (N : ℝ)) = (radius ^ 2 / (N : ℝ)) / 2 := by ring
    rw [hleft, hright]
    linarith

end ForestSampling
