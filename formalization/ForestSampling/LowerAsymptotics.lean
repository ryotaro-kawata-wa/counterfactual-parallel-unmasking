import ForestSampling.CalibratedLowerBound
import ForestSampling.HardClassMembership

set_option autoImplicit false

namespace ForestSampling

/-- Removing the bank floor loses at most a factor two. This estimate
holds throughout the finite signal range, without an asymptotic limit. -/
theorem calibratedBank_half_power_lt (signal exponent : ℝ)
    (hs0 : 0 < signal) (hs1 : signal < 1) (he : 1 < exponent) :
    signal ^ (-1 / exponent) / 2 < (calibratedBank signal exponent : ℝ) := by
  have hk := (calibratedBank_bounds signal exponent hs0 hs1 he).1
  have hkr : (1 : ℝ) ≤ calibratedBank signal exponent := by exact_mod_cast hk
  have hfloor := Nat.lt_floor_add_one (signal ^ (-1 / exponent))
  change signal ^ (-1 / exponent) < (calibratedBank signal exponent : ℝ) + 1 at hfloor
  linarith

/-- The exact query scale after substituting the concrete benchmark signal. -/
theorem benchmarkSignal_query_power (N : ℕ) (radius exponent : ℝ)
    (hN : 1 ≤ N) (hr : 0 < radius) :
    benchmarkSignal N radius ^ (-1 / exponent) =
      (2 : ℝ) ^ (1 / exponent) * ((N : ℝ) / radius ^ 2) ^ (1 / (3 * exponent)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ radius ^ 2 / (N : ℝ) := by positivity
  unfold benchmarkSignal
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx _), ← Real.rpow_mul hx]
  have hhalf : (1 / 2 : ℝ) ^ (-1 / exponent) = (2 : ℝ) ^ (1 / exponent) := by
    rw [neg_div, Real.rpow_neg_eq_inv_rpow]
    norm_num
  rw [hhalf]
  congr 1
  have hexp : (1 / 3 : ℝ) * (-1 / exponent) = -(1 / (3 * exponent)) := by ring
  rw [hexp, Real.rpow_neg_eq_inv_rpow, inv_div]

/-- The exact round scale after substituting the concrete benchmark signal. -/
theorem benchmarkSignal_round_power (N : ℕ) (radius tolerance : ℝ)
    (hN : 1 ≤ N) (hr : 0 < radius) :
    (N : ℝ) * benchmarkSignal N radius ^ 2 / (786432 * tolerance) =
      (N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * tolerance) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ radius ^ 2 / (N : ℝ) := by positivity
  have hpow : ((radius ^ 2 / (N : ℝ)) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) =
      radius ^ (4 / 3 : ℝ) / (N : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
    rw [Real.div_rpow (sq_nonneg radius) hNr.le]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  have hNpow : (N : ℝ) = (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hNr]
    norm_num
  unfold benchmarkSignal
  rw [mul_pow, hpow]
  have hnz : (N : ℝ) ^ (2 / 3 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hNr _)
  calc
    _ = ((N : ℝ) / (N : ℝ) ^ (2 / 3 : ℝ)) * radius ^ (4 / 3 : ℝ) /
        (3145728 * tolerance) := by ring
    _ = _ := by
      have hquot : (N : ℝ) / (N : ℝ) ^ (2 / 3 : ℝ) = (N : ℝ) ^ (1 / 3 : ℝ) :=
        (div_eq_iff hnz).mpr hNpow
      rw [hquot]

/-- The actual integer hard witness at the benchmark signal. Its scalar
validity fields are discharged from the public finite parameter range. -/
noncomputable def benchmarkParameters (N V : ℕ) (radius exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hr0 : 0 < radius) (hr1 : radius ≤ 1)
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * benchmarkSignal N radius) :
    NonlinearMatchingParameters N :=
  signalCalibratedParameters N V (benchmarkSignal N radius) exponent hNeven
    (benchmarkSignal_bounds N radius hN hr0 hr1).1
    (benchmarkSignal_bounds N radius hN hr0 hr1).2.1 he hV

/-- The concrete benchmark family satisfies every finite hard-class
inclusion clause at the public radius and signal. -/
theorem benchmarkParameters_finiteIncluded (N V : ℕ) (radius exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hr0 : 0 < radius) (hr1 : radius ≤ 1)
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * benchmarkSignal N radius) :
    let P := benchmarkParameters N V radius exponent hNeven hN hr0 hr1 he hV
    letI : Nonempty (HardVocabulary P.bankSize P.backgroundSize) :=
      ⟨Sum.inr ⟨0, P.backgroundSize_pos⟩⟩
    FiniteHardFamilyIncluded P.hardFamily (P.hardFamilyRanking hV)
      exponent (benchmarkSignal N radius) radius := by
  exact signalCalibratedParameters_finiteIncluded N V (benchmarkSignal N radius) exponent radius
    hNeven (benchmarkSignal_bounds N radius hN hr0 hr1).1
    (benchmarkSignal_bounds N radius hN hr0 hr1).2.1 he hV hr0.le hr1
    (benchmarkSignal_bounds N radius hN hr0 hr1).2.2

/-- An explicit finite form of the independent-radius lower exponents.
Both thresholds are obtained from the actual constructed witness, including
its integer bank floor and its actual-oracle admissible sampler class. -/
theorem benchmark_target_error_power_alternative (N V : ℕ) (radius exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hr0 : 0 < radius) (hr1 : radius ≤ 1)
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * benchmarkSignal N radius)
    (Q R : ℕ)
    (A : InstanceFamily.OracleBudgetedSampler
      (benchmarkParameters N V radius exponent hNeven hN hr0 hr1 he hV).hardFamily Q R)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ))
    (hrisk : InstanceFamily.worstCaseRisk
      (benchmarkParameters N V radius exponent hNeven hN hr0 hr1 he hV).hardFamily A.1 ≤ ε) :
    (2 : ℝ) ^ (1 / exponent) * ((N : ℝ) / radius ^ 2) ^ (1 / (3 * exponent)) / 16 <
        (Q : ℝ) ∨
      min ((N : ℝ) / 16384)
        ((N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * ε)) ≤ (R : ℝ) := by
  have hb := benchmarkSignal_bounds N radius hN hr0 hr1
  rcases signalCalibrated_target_error_alternative N V (benchmarkSignal N radius) exponent
    hNeven hb.1 hb.2.1 he hV Q R A ε hε0 hε1 hrisk with hquery | hround
  · left
    have hfloor := calibratedBank_half_power_lt (benchmarkSignal N radius) exponent
      hb.1 (by linarith [hb.2.1]) he
    rw [benchmarkSignal_query_power N radius exponent hN hr0] at hfloor
    linarith
  · right
    rwa [benchmarkSignal_round_power N radius ε hN hr0] at hround

/-- The single-accuracy substitution only increases the query threshold
relative to the main text's displayed scale. -/
theorem main_query_scale_le (N : ℕ) (ε exponent : ℝ)
    (hε : 0 < ε) (he : 1 < exponent) :
    ((N : ℝ) / ε ^ 2) ^ (1 / (3 * exponent)) ≤
      (2 : ℝ) ^ (1 / exponent) *
        ((N : ℝ) / (ε / 2) ^ 2) ^ (1 / (3 * exponent)) := by
  have he0 : 0 < exponent := by linarith
  have hbase : (N : ℝ) / ε ^ 2 ≤ (N : ℝ) / (ε / 2) ^ 2 := by
    have hh : (N : ℝ) / (ε / 2) ^ 2 = 4 * ((N : ℝ) / ε ^ 2) := by ring
    rw [hh]
    have hn : 0 ≤ (N : ℝ) / ε ^ 2 := by positivity
    linarith
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (N : ℝ) / ε ^ 2) hbase
    (show (0 : ℝ) ≤ 1 / (3 * exponent) by positivity)
  have htwo := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
    (show (0 : ℝ) ≤ 1 / exponent by positivity)
  exact hp.trans (le_mul_of_one_le_left (by positivity) htwo)

/-- The main round scale, with a rational constant, lies below both
branches of the finite minimum. Thus no large-length condition is needed
to remove that minimum in the single-accuracy specialization. -/
theorem main_round_scale_le_min (N : ℕ) (ε : ℝ)
    (hN : 1 ≤ N) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) / 12582912 ≤
      min ((N : ℝ) / 16384)
        ((N : ℝ) ^ (1 / 3 : ℝ) * (ε / 2) ^ (4 / 3 : ℝ) / (3145728 * ε)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnroot := Real.rpow_le_self_of_one_le hNr (show (1 / 3 : ℝ) ≤ 1 by norm_num)
  have heroot := Real.rpow_le_one hε0.le hε1 (show (0 : ℝ) ≤ 1 / 3 by norm_num)
  have hroot0 : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have hepow : ε ^ (4 / 3 : ℝ) = ε ^ (1 / 3 : ℝ) * ε := by
    calc
      _ = ε ^ ((1 / 3 : ℝ) + 1) := by norm_num
      _ = _ := by rw [Real.rpow_add hε0, Real.rpow_one]
  have htwopow : (2 : ℝ) ^ (4 / 3 : ℝ) ≤ 4 := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (4 / 3 : ℝ) ≤ 2 by norm_num)
    norm_num at hp ⊢
    exact hp
  refine le_min ?_ ?_
  · have hm : (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) ≤ N := by
      exact (mul_le_of_le_one_right hroot0 heroot).trans hnroot
    have hn0 : (0 : ℝ) ≤ N := by positivity
    linarith
  · rw [Real.div_rpow hε0.le (by norm_num), hepow]
    have htwo0 : 0 < (2 : ℝ) ^ (4 / 3 : ℝ) := by positivity
    have he0 : ε ≠ 0 := ne_of_gt hε0
    have hrewrite : (N : ℝ) ^ (1 / 3 : ℝ) *
        (ε ^ (1 / 3 : ℝ) * ε / (2 : ℝ) ^ (4 / 3 : ℝ)) / (3145728 * ε) =
        (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) /
          (3145728 * (2 : ℝ) ^ (4 / 3 : ℝ)) := by
      field_simp
    rw [hrewrite]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith [htwopow])

/-- Concrete finite lower bounds with precisely the powers printed in
the main theorem. The witness uses the public calibration radius ε/2 and
the actual integer bank. The remaining vocabulary hypothesis is explicit. -/
theorem main_target_error_power_alternative (N V : ℕ) (ε exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ))
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * benchmarkSignal N (ε / 2))
    (Q R : ℕ)
    (A : InstanceFamily.OracleBudgetedSampler
      (benchmarkParameters N V (ε / 2) exponent hNeven hN
        (by positivity) (by linarith) he hV).hardFamily Q R)
    (hrisk : InstanceFamily.worstCaseRisk
      (benchmarkParameters N V (ε / 2) exponent hNeven hN
        (by positivity) (by linarith) he hV).hardFamily A.1 ≤ ε) :
    ((N : ℝ) / ε ^ 2) ^ (1 / (3 * exponent)) / 16 < (Q : ℝ) ∨
      (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) / 12582912 ≤ (R : ℝ) := by
  rcases benchmark_target_error_power_alternative N V (ε / 2) exponent
    hNeven hN (by positivity) (by linarith) he hV Q R A ε hε0 hε1 hrisk with hq | hr
  · exact Or.inl (lt_of_le_of_lt (div_le_div_of_nonneg_right
      (main_query_scale_le N ε exponent hε0 he) (by norm_num)) hq)
  · exact Or.inr ((main_round_scale_le_min N ε hN hε0 (by linarith)).trans hr)

end ForestSampling
