import ForestSampling.GeneralUpperCurve
import ForestSampling.MainResourceTotals

set_option autoImplicit false
open Filter Topology

namespace ForestSampling.GeneralResourceTotals

noncomputable section

/-- The generic public curve at the actual rounded balancing cutoff. -/
def balancedQueryCap (N : ℕ) (ρ ζ c a : ℝ) : ℕ :=
  GeneralUpperCurve.queryCap N (UpperRates.balancedCutoff N (benchmarkSignal N ρ) ζ) ρ ζ c a

def balancedTotalCallCap (N : ℕ) (ρ ζ c a : ℝ) : ℕ :=
  1 + balancedQueryCap N ρ ζ c a + MainUpperTheorem.roundCap N ρ ζ

/-- Finite balancing of the full generic column envelope, including the
natural ceiling of the actual cutoff. -/
theorem balanced_queryEnvelope_le (N : ℕ) (ρ ζ c a : ℝ)
    (hN : 0 < N) (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (ha : 0 ≤ a)
    (hx : 1 ≤ UpperRates.balancedCutoffReal N (benchmarkSignal N ρ) ζ) :
    GeneralUpperCurve.queryEnvelope N (UpperRates.balancedCutoff N (benchmarkSignal N ρ) ζ)
      ρ ζ c a ≤
      1088 * UpperRates.screenConstant * UpperRates.repetitionConstant c a *
        ((16 : ℝ)^(1/ζ)+1) * UpperRates.balancedScale N (benchmarkSignal N ρ) ζ *
          UpperRates.logWeight N^2 := by
  have hs := benchmarkSignal_bounds N ρ (by omega) hr hr1
  have hcolumn := UpperRates.balanced_column_scale N (benchmarkSignal N ρ) ζ
    hN hs.1 (by linarith [hs.2.1]) (by linarith) hx
  have hk : 0 ≤ 272 * UpperRates.screenConstant * UpperRates.repetitionConstant c a *
      UpperRates.logWeight N^2 := by
    have hscreen := UpperRates.screenConstant_pos
    have hrep := UpperRates.repetitionConstant_pos c a ha
    positivity
  have hb := mul_le_mul_of_nonneg_left hcolumn hk
  unfold GeneralUpperCurve.queryEnvelope
  nlinarith only [hb]

/-- The generic public query cap is sublinear for every fixed positive
failure coefficient and nonnegative inverse-polynomial exponent. This
includes the literal appendix allocation eta = rho/2. -/
theorem balancedQueryCap_isLittleO (ρ ζ c a : ℝ)
    (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (_hc : 0 < c) (ha : 0 ≤ a) :
    (fun N : ℕ ↦ (balancedQueryCap N ρ ζ c a : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  let C := 1088 * UpperRates.screenConstant * UpperRates.repetitionConstant c a *
    ((16 : ℝ)^(1/ζ)+1)
  have hrate := (UpperRates.benchmark_balanced_logWeight_sq_isLittleO ρ ζ hr hζ).const_mul_left C
  have hb : (fun N : ℕ ↦ (balancedQueryCap N ρ ζ c a : ℝ)) =O[atTop]
      (fun N : ℕ ↦ C * (UpperRates.balancedScale N (benchmarkSignal N ρ) ζ *
        UpperRates.logWeight N^2) + 1) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [UpperFeasibilityGrowth.benchmark_balancedCutoff_eventually ρ ζ hr hζ,
      eventually_ge_atTop (1 : ℕ)] with N hcut hN
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hq := GeneralUpperCurve.queryCap_le N
      (UpperRates.balancedCutoff N (benchmarkSignal N ρ) ζ) ρ ζ c a ha
    have henv := balanced_queryEnvelope_le N ρ ζ c a (by omega) hr hr1 hζ ha hcut.1
    change (GeneralUpperCurve.queryCap N _ ρ ζ c a : ℝ) ≤ _
    dsimp only [C]
    nlinarith only [hq, henv]
  exact hb.trans_isLittleO (hrate.add MainResourceTotals.one_isLittleO)

/-- Total actual calls at the generic balanced cap are sublinear too. -/
theorem balancedTotalCallCap_isLittleO (ρ ζ c a : ℝ)
    (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (hc : 0 < c) (ha : 0 ≤ a) :
    (fun N : ℕ ↦ (balancedTotalCallCap N ρ ζ c a : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  simpa only [balancedTotalCallCap, Nat.cast_add, Nat.cast_one] using
    (MainResourceTotals.one_isLittleO.add (balancedQueryCap_isLittleO ρ ζ c a hr hr1 hζ hc ha)).add
      (MainUpperTheorem.roundCap_isLittleO ρ ζ hr hζ)

/-- The generic balanced curve's genuine grouped depth is the already
proved sublinear preprocessing/commit/screen cap. -/
theorem balancedDepthCap_isLittleO (ρ ζ : ℝ) (hr : 0 < ρ) (hζ : 1 < ζ) :
    (fun N : ℕ ↦ (GeneralUpperCurve.depthCap N
      (UpperRates.balancedCutoff N (benchmarkSignal N ρ) ζ) : ℝ)) =o[atTop]
        (fun N : ℕ ↦ (N : ℝ)) :=
  MainResourceTotals.depthCap_isLittleO ρ ζ hr hζ

/-- The actual appendix TV public sampler, together with every retained
execution's total calls, using exactly eta = rho/2. Grouped depth and
robust TV <= 3 rho/2 are retained inside the original uniform guarantee. -/
def TVTotalGuarantee (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (ρ ζ : ℝ) (P : PackedSampler.Parameters N V) : Prop :=
  let D := UpperRates.balancedCutoff N (benchmarkSignal N ρ) ζ
  let A := PackedSampler.sampler (Color := Fin (PackedSampler.colorCount D)) P
  GeneralUpperCurve.UniformTVGuarantee N V D ρ ζ P ∧
    ∀ (M : ForestModel N V) (ranking : MarginalRanking M),
      FiniteRankFrequency M ranking ζ 1 → M.TailResponseRegular 1 1 →
      M.EdgeNondegenerate (benchmarkSignal N ρ) →
      ∀ O, O.Accurate M ρ → A.WithinTotalOracleCalls O (balancedTotalCallCap N ρ ζ (ρ/2) 0)

/-- The actual generic-curve KL calibration with its total calls attached. -/
def KLTotalGuarantee (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (ρ ζ growth : ℝ) (P : PackedSampler.Parameters N V) : Prop :=
  let D := UpperRates.balancedCutoff N (benchmarkSignal N ρ) ζ
  let A := PackedSampler.sampler (Color := Fin (PackedSampler.colorCount D)) P
  GeneralUpperCurve.UniformKLGuarantee N V D ρ ζ growth P ∧
    ∀ (M : ForestModel N V) (ranking : MarginalRanking M),
      FiniteRankFrequency M ranking ζ 1 → M.TailResponseRegular 1 1 →
      M.EdgeNondegenerate (benchmarkSignal N ρ) →
      ∀ O, O.ForwardKLAccurate M (MainKLUpperTheorem.rowBudget N ρ) →
        A.WithinTotalOracleCalls O
          (balancedTotalCallCap N ρ ζ (MainKLUpperTheorem.failureCoefficient ρ growth) 2)

/-- Literal vocabulary growth supplies all finite feasibility conditions
for the appendix's balanced TV algorithm, with its original allocation. -/
theorem balanced_tv_totalGuarantee_eventually (V : ℕ → Type*)
    [∀ N, Fintype (V N)] [∀ N, DecidableEq (V N)] [∀ N, LinearOrder (V N)] [∀ N, Nonempty (V N)]
    (ρ ζ growth : ℝ) (error : ℕ → ℝ)
    (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (hg : (1/3 : ℝ) < growth)
    (he : Tendsto error atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, (Fintype.card (V N) : ℝ) = (N : ℝ)^(growth+error N)) :
    ∀ᶠ N : ℕ in atTop,
      ∃ (hN : 0 < N) (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N ρ) ζ)
        (hm : 16 * max (ρ/Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N ρ),
      TVTotalGuarantee N (V N) ρ ζ
        (GeneralUpperCurve.parameters N (V N) (UpperRates.balancedCutoff N (benchmarkSignal N ρ) ζ)
          ρ (ρ/2) hN hr hr1 hD hm) := by
  filter_upwards [GeneralUpperCurve.tv_curve_eventually V ρ ζ growth error hr hr1 hζ hg he hv,
    UpperFeasibilityGrowth.benchmark_balancedCutoff_eventually ρ ζ hr hζ] with N hcurve hcut
  obtain ⟨hn, hm, hall⟩ := hcurve
  have h := (hall _ hcut.2.1 hcut.2.2).1
  refine ⟨hn, hcut.2.1, hm, h, ?_⟩
  intro M ranking hRF hRT hUEN O hO
  exact ((h.2 M ranking hRF hRT hUEN).2.2 O hO).withinTotalOracleCalls

/-- The KL counterpart preserves its inverse-polynomial failure budget,
actual seed loss, grouped depth, and total call count. -/
theorem balanced_kl_totalGuarantee_eventually (V : ℕ → Type*)
    [∀ N, Fintype (V N)] [∀ N, DecidableEq (V N)] [∀ N, LinearOrder (V N)] [∀ N, Nonempty (V N)]
    (ρ ζ growth : ℝ) (error : ℕ → ℝ)
    (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (hg : (1/3 : ℝ) < growth)
    (he : Tendsto error atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, (Fintype.card (V N) : ℝ) = (N : ℝ)^(growth+error N)) :
    ∀ᶠ N : ℕ in atTop,
      ∃ (hN : 0 < N) (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N ρ) ζ)
        (hm : 16 * max (ρ/Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N ρ),
      KLTotalGuarantee N (V N) ρ ζ growth
        (GeneralUpperCurve.parameters N (V N) (UpperRates.balancedCutoff N (benchmarkSignal N ρ) ζ)
          ρ (MainKLUpperTheorem.failureBudget N (Fintype.card (V N)) ρ) hN hr hr1 hD hm) := by
  filter_upwards [GeneralUpperCurve.kl_curve_eventually V ρ ζ growth error hr hr1 hζ hg he hv,
    UpperFeasibilityGrowth.benchmark_balancedCutoff_eventually ρ ζ hr hζ] with N hcurve hcut
  obtain ⟨hn, hm, hall⟩ := hcurve
  have h := (hall _ hcut.2.1 hcut.2.2).1
  refine ⟨hn, hcut.2.1, hm, h, ?_⟩
  intro M ranking hRF hRT hUEN O hO
  exact (h.2 M ranking hRF hRT hUEN O hO).2.2.withinTotalOracleCalls

/-- The literal TV allocation's total cap is strictly sublinear. -/
theorem appendix_tv_total_isLittleO (ρ ζ : ℝ)
    (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) :
    (fun N : ℕ ↦ (balancedTotalCallCap N ρ ζ (ρ/2) 0 : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) :=
  balancedTotalCallCap_isLittleO ρ ζ (ρ/2) 0 hr hr1 hζ (by positivity) (by norm_num)

/-- The calibrated KL allocation also fits the generic fixed coefficient. -/
theorem appendix_kl_total_isLittleO (ρ ζ growth : ℝ)
    (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (hg : 0 < growth) :
    (fun N : ℕ ↦ (balancedTotalCallCap N ρ ζ
      (MainKLUpperTheorem.failureCoefficient ρ growth) 2 : ℝ)) =o[atTop]
        (fun N : ℕ ↦ (N : ℝ)) :=
  balancedTotalCallCap_isLittleO ρ ζ _ 2 hr hr1 hζ
    (by unfold MainKLUpperTheorem.failureCoefficient; positivity) (by norm_num)

end
end ForestSampling.GeneralResourceTotals
