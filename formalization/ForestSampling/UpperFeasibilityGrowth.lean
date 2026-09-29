import ForestSampling.LowerVocabularyGrowth
import ForestSampling.UpperRates

set_option autoImplicit false
open Filter Topology

namespace ForestSampling
namespace UpperFeasibilityGrowth

/-- Any fixed vocabulary multiple is eventually dominated by the actual
benchmark signal under the literal public RF vocabulary-growth assumption. -/
theorem vocabulary_multiple_eventually (vocabulary : ℕ → ℕ)
    (radius growth multiple : ℝ) (error : ℕ → ℝ)
    (hr : 0 < radius) (hg : (1/3 : ℝ) < growth)
    (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (vocabulary N : ℝ) = (N : ℝ) ^ (growth + error N)) :
    ∀ᶠ N in atTop, multiple ≤ (vocabulary N : ℝ) * benchmarkSignal N radius := by
  let excess := (growth - (1/3 : ℝ))/2
  have he : 0 < excess := by dsimp [excess]; linarith
  have herr : ∀ᶠ N in atTop, -excess < error N := herror.eventually_const_lt (by linarith)
  have hp : Tendsto (fun N : ℕ ↦ (N : ℝ)^excess) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  have hb := hp.eventually (eventually_ge_atTop (2 * multiple / radius^(2/3 : ℝ)))
  filter_upwards [hvocab, herr, hb, eventually_ge_atTop (1 : ℕ)] with N hV herrorN hlarge hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrad : 0 < radius^(2/3 : ℝ) := by positivity
  have hpow : (N : ℝ)^((1/3 : ℝ)+excess) ≤ vocabulary N := by
    rw [hV]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    dsimp [excess] at herrorN ⊢
    linarith
  have hfactor : (N : ℝ)^((1/3 : ℝ)+excess) * benchmarkSignal N radius =
      (N : ℝ)^excess * radius^(2/3 : ℝ)/2 := by
    rw [Real.rpow_add hNr, benchmarkSignal_factor N radius hN hr]
    have hh : (N : ℝ)^(1/3 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hNr _)
    field_simp
  have hlow : multiple ≤ (N : ℝ)^excess * radius^(2/3 : ℝ)/2 := by
    have hh := (div_le_iff₀ hrad).mp hlarge
    linarith
  rw [← hfactor] at hlow
  exact hlow.trans (mul_le_mul_of_nonneg_right hpow (by unfold benchmarkSignal; positivity))

/-- The actual row-noise scale is eventually smaller than one sixteenth
of the benchmark signal; the positive N^(1/6) gap is derived explicitly. -/
theorem noise_eventually (radius : ℝ) (hr : 0 < radius) :
    ∀ᶠ N : ℕ in atTop, 16 * (radius / Real.sqrt N) ≤ benchmarkSignal N radius := by
  have hp : Tendsto (fun N : ℕ ↦ (N : ℝ)^(1/6 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/6)).comp tendsto_natCast_atTop_atTop
  have hb := hp.eventually (eventually_ge_atTop (32 * radius / radius^(2/3 : ℝ)))
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with N hlarge hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hthird : 0 < (N : ℝ)^(1/3 : ℝ) := by positivity
  have hrad : 0 < radius^(2/3 : ℝ) := by positivity
  have hmul : (N : ℝ)^(1/3 : ℝ) * (N : ℝ)^(1/6 : ℝ) = Real.sqrt N := by
    rw [← Real.rpow_add hNr]
    norm_num
    exact (Real.sqrt_eq_rpow _).symm
  have hh := (div_le_iff₀ hrad).mp hlarge
  rw [benchmarkSignal_factor N radius hN hr]
  apply (le_div_iff₀ (by positivity : 0 < 2 * (N : ℝ)^(1/3 : ℝ))).mpr
  have hh' := mul_le_mul_of_nonneg_right hh hthird.le
  calc
    _ = (32 * radius * (N : ℝ)^(1/3 : ℝ)) / Real.sqrt N := by ring
    _ ≤ radius^(2/3 : ℝ) := by
      apply (div_le_iff₀ hs).mpr
      calc
        _ ≤ ((N : ℝ)^(1/6 : ℝ) * radius^(2/3 : ℝ)) * (N : ℝ)^(1/3 : ℝ) := hh'
        _ = radius^(2/3 : ℝ) * Real.sqrt N := by rw [← hmul]; ring

/-- The complete finite benchmark feasibility inequality follows eventually
from the actual row-noise and vocabulary sequences, without a rate premise
for either term in the maximum. -/
theorem benchmark_floor_eventually (vocabulary : ℕ → ℕ)
    (radius growth : ℝ) (error : ℕ → ℝ) (hr : 0 < radius)
    (hg : (1/3 : ℝ) < growth) (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (vocabulary N : ℝ) = (N : ℝ)^(growth + error N)) :
    ∀ᶠ N : ℕ in atTop,
      16 * max (radius / Real.sqrt N) (1 / (vocabulary N : ℝ)) ≤ benchmarkSignal N radius := by
  have hv := vocabulary_multiple_eventually vocabulary radius growth 16 error hr hg herror hvocab
  filter_upwards [hv, noise_eventually radius hr, eventually_ge_atTop (1 : ℕ)] with N hV hnoise hN
  have hs : 0 < benchmarkSignal N radius := by unfold benchmarkSignal; positivity
  have hVp : (0 : ℝ) < vocabulary N := by
    by_contra hn
    have hz : (vocabulary N : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
    rw [hz, zero_mul] at hV
    norm_num at hV
  rw [mul_max_of_nonneg _ _ (by norm_num)]
  apply max_le hnoise
  rw [mul_one_div, div_le_iff₀ hVp]
  nlinarith

/-- A positive sublinear power, multiplied by any positive fixed constant,
produces an actual integer ceiling in the manuscript's degree range. -/
theorem power_ceiling_eventually (a δ : ℝ) (ha : 0 < a) (hd0 : 0 < δ) (hd1 : δ < 1) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ a*(N : ℝ)^δ ∧ 9 ≤ ⌈a*(N : ℝ)^δ⌉₊ ∧ ⌈a*(N : ℝ)^δ⌉₊ ≤ N-1 := by
  have hp := (tendsto_rpow_atTop hd0).comp tendsto_natCast_atTop_atTop
  have hq := (tendsto_rpow_atTop (show 0 < 1-δ by linarith)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, 9/a ≤ (N : ℝ)^δ := hp.eventually (eventually_ge_atTop _)
  have hsmall : ∀ᶠ N : ℕ in atTop, 4*a ≤ (N : ℝ)^(1-δ) := hq.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge, hsmall, eventually_ge_atTop (2 : ℕ)] with N hl hs hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hval : 9 ≤ a*(N : ℝ)^δ := by have hh := (div_le_iff₀ ha).mp hl; nlinarith
  have hprod : (N : ℝ)^(1-δ) * (N : ℝ)^δ = N := by
    rw [← Real.rpow_add hNr]
    simp
  have hscale := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hNr.le δ)
  rw [hprod] at hscale
  have hc : (⌈a*(N : ℝ)^δ⌉₊ : ℝ) ≤ 2*(a*(N : ℝ)^δ) :=
    (Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith)
  refine ⟨by linarith, ?_, ?_⟩
  · have hh := hval.trans (Nat.le_ceil _)
    exact_mod_cast hh
  · have hnreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hh : (⌈a*(N : ℝ)^δ⌉₊ : ℝ) + 1 ≤ N := by nlinarith
    have hh' : ⌈a*(N : ℝ)^δ⌉₊ + 1 ≤ N := by exact_mod_cast hh
    omega

/-- Fixed positive coefficient and sublinear exponent of the actual
benchmark-balanced cutoff; the ceiling is taken only after this quantity. -/
noncomputable def cutoffCoefficient (radius ζ : ℝ) : ℝ :=
  radius^(2/(9*ζ)) / (2 : ℝ)^(1/(3*ζ))

noncomputable def cutoffExponent (ζ : ℝ) : ℝ := (1/3 : ℝ) - 1/(9*ζ)

/-- Exact algebraic specialization of the real cutoff, before rounding. -/
theorem benchmark_cutoffReal_eq (N : ℕ) (radius ζ : ℝ)
    (hN : 1 ≤ N) (hr : 0 < radius) :
    UpperRates.balancedCutoffReal N (benchmarkSignal N radius) ζ =
      cutoffCoefficient radius ζ * (N : ℝ)^cutoffExponent ζ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsig : 0 ≤ benchmarkSignal N radius := by unfold benchmarkSignal; positivity
  rw [UpperRates.balancedCutoffReal_eq N _ ζ hsig, benchmarkSignal_factor N radius hN hr]
  rw [Real.div_rpow (Real.rpow_nonneg hr.le _) (by positivity),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hNr.le _),
    ← Real.rpow_mul hr.le, ← Real.rpow_mul hNr.le]
  unfold cutoffCoefficient cutoffExponent
  rw [Real.rpow_sub hNr]
  have he1 : (2/3 : ℝ)*(1/(3*ζ)) = 2/(9*ζ) := by ring
  have he2 : (1/3 : ℝ)*(1/(3*ζ)) = 1/(9*ζ) := by ring
  rw [he1, he2]
  ring

/-- The actual rounded benchmark-balanced cutoff eventually satisfies the
finite theorem's lower and upper degree restrictions, with its unrounded
value also at least one for the proved rounding-loss inequalities. -/
theorem benchmark_balancedCutoff_eventually (radius ζ : ℝ) (hr : 0 < radius) (hζ : 1 < ζ) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ UpperRates.balancedCutoffReal N (benchmarkSignal N radius) ζ ∧
      9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ ∧
      UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ ≤ N-1 := by
  have ha : 0 < cutoffCoefficient radius ζ := by unfold cutoffCoefficient; positivity
  have hz : 0 < ζ := by linarith
  have hf0 : 0 < 1/(9*ζ) := by positivity
  have hf1 : 1/(9*ζ) ≤ (1/9 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have he0 : 0 < cutoffExponent ζ := by unfold cutoffExponent; linarith
  have he1 : cutoffExponent ζ < 1 := by unfold cutoffExponent; linarith
  have hh := power_ceiling_eventually (cutoffCoefficient radius ζ) (cutoffExponent ζ) ha he0 he1
  filter_upwards [hh, eventually_ge_atTop (1 : ℕ)] with N hb hN
  simpa only [UpperRates.balancedCutoff, benchmark_cutoffReal_eq N radius ζ hN hr] using hb

end UpperFeasibilityGrowth
end ForestSampling
