import ForestSampling.LowerAsymptotics

set_option autoImplicit false

open Filter Topology

namespace ForestSampling

/-- Separating the benchmark's length and radius factors makes the public
vocabulary-growth requirement explicit. -/
theorem benchmarkSignal_factor (N : ℕ) (radius : ℝ) (hN : 1 ≤ N)
    (hr : 0 < radius) :
    benchmarkSignal N radius = radius ^ (2 / 3 : ℝ) /
      (2 * (N : ℝ) ^ (1 / 3 : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold benchmarkSignal
  rw [Real.div_rpow (sq_nonneg radius) hNr.le]
  have hp : (radius ^ 2) ^ (1 / 3 : ℝ) = radius ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  rw [hp]
  ring

/-- A finite sufficient vocabulary-growth inequality for the actual
benchmark witness. The excess exponent is measured above one third. -/
theorem benchmark_vocabulary_spread_of_power (N V : ℕ) (radius excess : ℝ)
    (hN : 1 ≤ N) (hr : 0 < radius)
    (hV : (N : ℝ) ^ ((1 / 3 : ℝ) + excess) ≤ V)
    (hlarge : 2 / radius ^ (2 / 3 : ℝ) < (N : ℝ) ^ excess) :
    1 < (V : ℝ) * benchmarkSignal N radius := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrpow : 0 < radius ^ (2 / 3 : ℝ) := by positivity
  have hnroot : (N : ℝ) ^ (1 / 3 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hNr _)
  have hsig : 0 ≤ benchmarkSignal N radius := by unfold benchmarkSignal; positivity
  have hfactor : (N : ℝ) ^ ((1 / 3 : ℝ) + excess) * benchmarkSignal N radius =
      (N : ℝ) ^ excess * radius ^ (2 / 3 : ℝ) / 2 := by
    rw [Real.rpow_add hNr, benchmarkSignal_factor N radius hN hr]
    field_simp
  have hbig : 1 < (N : ℝ) ^ excess * radius ^ (2 / 3 : ℝ) / 2 := by
    have hm := (div_lt_iff₀ hrpow).mp hlarge
    linarith
  rw [← hfactor] at hbig
  exact hbig.trans_le (mul_le_mul_of_nonneg_right hV hsig)

/-- Literal `N^(growth + o(1))` vocabulary growth with exponent above one
third eventually satisfies the finite witness's strict vocabulary condition.
The error is a real sequence tending to zero; no power lower bound is assumed. -/
theorem benchmark_vocabulary_spread_eventually (vocabulary : ℕ → ℕ)
    (radius growth : ℝ) (error : ℕ → ℝ)
    (hr : 0 < radius) (hg : (1 / 3 : ℝ) < growth)
    (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (vocabulary N : ℝ) = (N : ℝ) ^ (growth + error N)) :
    ∀ᶠ N in atTop, 1 < (vocabulary N : ℝ) * benchmarkSignal N radius := by
  let excess := (growth - (1 / 3 : ℝ)) / 2
  have hexcess : 0 < excess := by dsimp [excess]; linarith
  have herr : ∀ᶠ N in atTop, -excess < error N :=
    herror.eventually_const_lt (by linarith)
  have hpow : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ excess) atTop atTop :=
    (tendsto_rpow_atTop hexcess).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, 2 / radius ^ (2 / 3 : ℝ) < (N : ℝ) ^ excess :=
    hpow.eventually (eventually_gt_atTop _)
  filter_upwards [hvocab, herr, hlarge, eventually_ge_atTop (1 : ℕ)] with N hV herrN hlargeN hN
  apply benchmark_vocabulary_spread_of_power N (vocabulary N) radius excess hN hr ?_ hlargeN
  rw [hV]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  dsimp [excess] at herrN ⊢
  linarith


/-- A finite sufficient length threshold for removing the independent-radius
round minimum. This inequality keeps the tolerance dependence explicit. -/
theorem benchmark_round_scale_le_length (N : ℕ) (radius ε : ℝ)
    (hN : 1 ≤ N) (hε : 0 < ε)
    (hlarge : radius ^ (4 / 3 : ℝ) / (192 * ε) ≤ (N : ℝ) ^ (2 / 3 : ℝ)) :
    (N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * ε) ≤
      (N : ℝ) / 16384 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hprod : (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) = N := by
    rw [← Real.rpow_add hNr]
    norm_num
  have hscale := (div_le_iff₀ (by positivity : 0 < 192 * ε)).mp hlarge
  apply (div_le_iff₀ (by positivity : 0 < 3145728 * ε)).mpr
  calc
    _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * ((N : ℝ) ^ (2 / 3 : ℝ) * (192 * ε)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by rw [← mul_assoc, hprod]; ring

/-- For fixed positive independent budgets, the sublinear round branch
is eventually the smaller branch of the exact finite minimum. -/
theorem benchmark_round_min_eventually (radius ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      min ((N : ℝ) / 16384)
        ((N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * ε)) =
        (N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * ε) := by
  have hpow : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (2 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      radius ^ (4 / 3 : ℝ) / (192 * ε) ≤ (N : ℝ) ^ (2 / 3 : ℝ) :=
    hpow.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with N hlargeN hN
  exact min_eq_right (benchmark_round_scale_le_length N radius ε hN hε hlargeN)

/-- The independent-radius lower exponents hold eventually under the
literal public vocabulary-growth assumption. This is the lower part of
the fixed-accuracy appendix specialization, with constants displayed. -/
theorem benchmark_target_error_power_alternative_eventually (vocabulary : ℕ → ℕ)
    (radius ε exponent growth : ℝ) (error : ℕ → ℝ)
    (hr0 : 0 < radius) (hr1 : radius ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ)) (he : 1 < exponent)
    (hg : (1 / 3 : ℝ) < growth) (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (vocabulary N : ℝ) = (N : ℝ) ^ (growth + error N)) :
    ∀ᶠ N in atTop,
      ∃ hN : 1 ≤ N, ∃ hV : 1 < (vocabulary N : ℝ) * benchmarkSignal N radius,
      ∀ (hNeven : Even N) (Q R : ℕ)
        (A : InstanceFamily.OracleBudgetedSampler
          (benchmarkParameters N (vocabulary N) radius exponent hNeven hN hr0 hr1 he hV).hardFamily Q R),
        InstanceFamily.worstCaseRisk
          (benchmarkParameters N (vocabulary N) radius exponent hNeven hN hr0 hr1 he hV).hardFamily A.1 ≤ ε →
        (2 : ℝ) ^ (1 / exponent) * ((N : ℝ) / radius ^ 2) ^ (1 / (3 * exponent)) / 16 <
            (Q : ℝ) ∨
          (N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * ε) ≤ (R : ℝ) := by
  have hspread := benchmark_vocabulary_spread_eventually vocabulary radius growth error
    hr0 hg herror hvocab
  filter_upwards [hspread, benchmark_round_min_eventually radius ε hε0,
    eventually_ge_atTop (1 : ℕ)] with N hV hmin hN
  refine ⟨hN, hV, ?_⟩
  intro hNeven Q R A hrisk
  have halt := benchmark_target_error_power_alternative N (vocabulary N) radius exponent
    hNeven hN hr0 hr1 he hV Q R A ε hε0 hε1 hrisk
  rwa [hmin] at halt

/-- The main lower exponents hold eventually for the declared public
vocabulary growth, with explicit positive constants and the actual finite
benchmark family. Every even length in this tail is covered uniformly over
its actual-oracle budgeted samplers. -/
theorem main_target_error_power_alternative_eventually (vocabulary : ℕ → ℕ)
    (ε exponent growth : ℝ) (error : ℕ → ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ)) (he : 1 < exponent)
    (hg : (1 / 3 : ℝ) < growth) (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (vocabulary N : ℝ) = (N : ℝ) ^ (growth + error N)) :
    ∀ᶠ N in atTop,
      ∃ hN : 1 ≤ N, ∃ hV : 1 < (vocabulary N : ℝ) * benchmarkSignal N (ε / 2),
      ∀ (hNeven : Even N) (Q R : ℕ)
        (A : InstanceFamily.OracleBudgetedSampler
          (benchmarkParameters N (vocabulary N) (ε / 2) exponent hNeven hN
            (by positivity) (by linarith) he hV).hardFamily Q R),
        InstanceFamily.worstCaseRisk
          (benchmarkParameters N (vocabulary N) (ε / 2) exponent hNeven hN
            (by positivity) (by linarith) he hV).hardFamily A.1 ≤ ε →
        ((N : ℝ) / ε ^ 2) ^ (1 / (3 * exponent)) / 16 < (Q : ℝ) ∨
          (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) / 12582912 ≤ (R : ℝ) := by
  have hspread := benchmark_vocabulary_spread_eventually vocabulary (ε / 2) growth error
    (by positivity) hg herror hvocab
  filter_upwards [hspread, eventually_ge_atTop (1 : ℕ)] with N hV hN
  refine ⟨hN, hV, ?_⟩
  intro hNeven Q R A hrisk
  exact main_target_error_power_alternative N (vocabulary N) ε exponent
    hNeven hN hε0 hε1 he hV Q R A hrisk

end ForestSampling
