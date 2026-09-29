import ForestSampling.MainUpperTheorem
import ForestSampling.MainKLUpperTheorem
import ForestSampling.PackedDepth

set_option autoImplicit false
open Filter Topology

namespace ForestSampling

namespace Sampler

variable {N : ℕ} {V Seed : Type*} [Fintype V] [DecidableEq V]

/-- The total number of actual oracle calls on every retained execution,
including one distinguished all-mask preprocessing call, every probe,
and every nonempty commit call. -/
def WithinTotalOracleCalls (A : Sampler N V Seed) (O : FrozenOracle N V) (total : ℕ) : Prop :=
  ∀ w, ∀ path : Program.RetainedPath O (A.program w (O.readState (MaskedState.allMask N V))),
    1 + Program.retainedQueryCount O _ path + Program.retainedRoundCount O _ path ≤ total

/-- Separate actual-oracle budgets bound the actual total without an
extra probabilistic or successful-screen assumption. -/
theorem WithinOracleBudgets.withinTotalOracleCalls {A : Sampler N V Seed}
    {O : FrozenOracle N V} {Q R : ℕ} (hb : A.WithinOracleBudgets O Q R) :
    A.WithinTotalOracleCalls O (1 + Q + R) := by
  intro w path
  have hh := Program.retainedPath_withinOracleBudgets O _ path Q R (hb w)
  omega

end Sampler

namespace MainResourceTotals

noncomputable section

/-- All screen groups in the rounded balanced public schedule. -/
def screenCap (N : ℕ) (radius ζ : ℝ) : ℕ :=
  ForestIteration.phaseCap N (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ) + 1

/-- Preprocessing, commit stages, and simultaneous fixed-input screen groups. -/
def depthCap (N : ℕ) (radius ζ : ℝ) : ℕ :=
  1 + MainUpperTheorem.roundCap N radius ζ + screenCap N radius ζ

/-- The public Hellinger/TV total-call bound includes preprocessing once. -/
def tvTotalCallCap (N : ℕ) (radius ζ : ℝ) : ℕ :=
  1 + MainUpperTheorem.queryCap N radius ζ + MainUpperTheorem.roundCap N radius ζ

/-- The public forward-KL total includes its calibrated repetition budget. -/
def klTotalCallCap (N : ℕ) (radius ζ growth : ℝ) : ℕ :=
  1 + MainKLUpperTheorem.queryCap N radius ζ growth + MainUpperTheorem.roundCap N radius ζ

theorem one_isLittleO :
    (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  simpa only [Function.comp_def, id_eq] using
    (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop)

/-- The actual number of balanced screen slots is sublinear. The proof
uses its finite logarithmic bound and the proved power-log estimate at
power zero, rather than assuming an asymptotic screen-count bound. -/
theorem screenCap_isLittleO (radius ζ : ℝ) (hr : 0 < radius) (hζ : 1 < ζ) :
    (fun N : ℕ ↦ (screenCap N radius ζ : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have hw : (fun N : ℕ ↦ UpperRates.logWeight N ^ 2) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
    simpa only [Real.rpow_zero, one_mul] using
      UpperRates.power_logWeight_sq_isLittleO 0 (by norm_num)
  have hb : (fun N : ℕ ↦ (screenCap N radius ζ : ℝ)) =O[atTop]
      (fun N : ℕ ↦ UpperRates.screenConstant * UpperRates.logWeight N ^ 2) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [UpperFeasibilityGrowth.benchmark_balancedCutoff_eventually radius ζ hr hζ,
      eventually_ge_atTop (1 : ℕ)] with N hD hN
    have hn : 0 < N := by omega
    have hscreen := UpperRates.screenCap_le_envelope N _ hn hD.2.1
    have henvelope := UpperRates.screenEnvelope_le_logWeight N hn
    have hw1 := (UpperRates.logWeight_bounds N hn).1
    have hw2 : UpperRates.logWeight N ≤ UpperRates.logWeight N ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hw2 UpperRates.screenConstant_pos.le
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hscreen.trans (henvelope.trans hmul)
  exact hb.trans_isLittleO (hw.const_mul_left UpperRates.screenConstant)

/-- Both sources of adaptivity and preprocessing are included in the
strictly sublinear depth cap. -/
theorem depthCap_isLittleO (radius ζ : ℝ) (hr : 0 < radius) (hζ : 1 < ζ) :
    (fun N : ℕ ↦ (depthCap N radius ζ : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  simpa only [depthCap, Nat.cast_add, Nat.cast_one] using
    (one_isLittleO.add (MainUpperTheorem.roundCap_isLittleO radius ζ hr hζ)).add
      (screenCap_isLittleO radius ζ hr hζ)

/-- Actual total TV oracle calls remain sublinear after adding the
mandatory commit calls and the distinguished preprocessing call. -/
theorem tvTotalCallCap_isLittleO (radius ζ : ℝ) (hr : 0 < radius) (hζ : 1 < ζ) :
    (fun N : ℕ ↦ (tvTotalCallCap N radius ζ : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  simpa only [tvTotalCallCap, Nat.cast_add, Nat.cast_one] using
    (one_isLittleO.add (MainUpperTheorem.queryCap_isLittleO radius ζ hr hζ)).add
      (MainUpperTheorem.roundCap_isLittleO radius ζ hr hζ)

/-- The additional logarithmic KL repetition cost is already included in
the same sublinear total-call conclusion. -/
theorem klTotalCallCap_isLittleO (radius ζ growth : ℝ) (hr : 0 < radius) (hζ : 1 < ζ) :
    (fun N : ℕ ↦ (klTotalCallCap N radius ζ growth : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  simpa only [klTotalCallCap, Nat.cast_add, Nat.cast_one] using
    (one_isLittleO.add (MainKLUpperTheorem.queryCap_isLittleO radius ζ growth hr hζ)).add
      (MainUpperTheorem.roundCap_isLittleO radius ζ hr hζ)

section Finite

variable {N : ℕ} {V : Type*}
  [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]

/-- Genuine grouped depth of the actual balanced TV sampler, uniform over
all seeds and all preprocessing replies. -/
theorem tv_parameters_withinOracleDepth (radius ζ : ℝ)
    (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius) :
    (PackedSampler.sampler
      (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)))
      (MainUpperTheorem.parameters N V radius ζ hN hr hr1 hD hm)).WithinOracleDepth
        (depthCap N radius ζ) :=
  PackedSampler.manuscript_sampler_withinOracleDepth _ _ _ radius radius hN (by omega) _

/-- The actual KL sampler has the same grouped depth despite using its
different calibrated failure budget and repetition count. -/
theorem kl_parameters_withinOracleDepth (radius ζ : ℝ)
    (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius) :
    (PackedSampler.sampler
      (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)))
      (MainKLUpperTheorem.parameters N V radius ζ hN hr hr1 hD hm)).WithinOracleDepth
        (depthCap N radius ζ) :=
  PackedSampler.manuscript_sampler_withinOracleDepth _ _ _ radius
    (MainKLUpperTheorem.failureBudget N (Fintype.card V) radius) hN (by omega) _

/-- Actual retained executions satisfy the total TV call cap. Its proof
uses the concrete ranked bank bound and the actual frozen oracle budget. -/
theorem tv_parameters_withinTotalOracleCalls (M : ForestModel N V) (O : FrozenOracle N V)
    (ranking : MarginalRanking M) (radius ζ : ℝ)
    (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1) (hζ : 1 < ζ)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hx : 1 ≤ UpperRates.balancedCutoffReal N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius)
    (hRF : FiniteRankFrequency M ranking ζ 1) (hO : O.Accurate M radius) :
    (PackedSampler.sampler
      (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)))
      (MainUpperTheorem.parameters N V radius ζ hN hr hr1 hD hm)).WithinTotalOracleCalls O
        (tvTotalCallCap N radius ζ) :=
  (MainUpperTheorem.parameters_withinOracleBudgets M O ranking radius ζ
    hN hr hr1 hζ hD hx hm hRF hO).withinTotalOracleCalls

/-- The actual forward-KL sampler obeys its total cap for every seed and
batch assignment, including the radius-dependent repeated screens. -/
theorem kl_parameters_withinTotalOracleCalls (M : ForestModel N V) (O : FrozenOracle N V)
    (ranking : MarginalRanking M) (radius ζ growth : ℝ)
    (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1) (hζ : 1 < ζ)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hx : 1 ≤ UpperRates.balancedCutoffReal N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius)
    (hg : 0 < growth)
    (hη : 0 < MainKLUpperTheorem.failureBudget N (Fintype.card V) radius)
    (hη1 : MainKLUpperTheorem.failureBudget N (Fintype.card V) radius ≤ 1)
    (hlower : MainKLUpperTheorem.failureCoefficient radius growth / (N : ℝ)^(2 : ℝ) ≤
      MainKLUpperTheorem.failureBudget N (Fintype.card V) radius)
    (hRF : FiniteRankFrequency M ranking ζ 1)
    (hO : O.ForwardKLAccurate M (MainKLUpperTheorem.rowBudget N radius)) :
    (PackedSampler.sampler
      (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)))
      (MainKLUpperTheorem.parameters N V radius ζ hN hr hr1 hD hm)).WithinTotalOracleCalls O
        (klTotalCallCap N radius ζ growth) :=
  (MainKLUpperTheorem.parameters_withinOracleBudgets M O ranking radius ζ growth
    hN hr hr1 hζ hD hx hm hg hη hη1 hlower hRF hO).withinTotalOracleCalls

/-- The TV public guarantee with actual total calls and grouped depth
attached to the very same sampler parameter object. -/
def TVTotalGuarantee (radius ζ : ℝ) (P : PackedSampler.Parameters N V) : Prop :=
  let A := PackedSampler.sampler
    (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P
  MainUpperTheorem.UniformGuarantee N V radius ζ P ∧
    A.WithinOracleDepth (depthCap N radius ζ) ∧
    ∀ (M : ForestModel N V) (ranking : MarginalRanking M),
      FiniteRankFrequency M ranking ζ 1 → M.TailResponseRegular 1 1 →
      M.EdgeNondegenerate (benchmarkSignal N radius) →
      ∀ O, O.Accurate M radius → A.WithinTotalOracleCalls O (tvTotalCallCap N radius ζ)

/-- The forward-KL public guarantee with its own total call cap and the
same actual parallel grouping of screens. -/
def KLTotalGuarantee (radius ζ growth : ℝ) (P : PackedSampler.Parameters N V) : Prop :=
  let A := PackedSampler.sampler
    (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P
  MainKLUpperTheorem.UniformGuarantee N V radius ζ growth P ∧
    A.WithinOracleDepth (depthCap N radius ζ) ∧
    ∀ (M : ForestModel N V) (ranking : MarginalRanking M),
      FiniteRankFrequency M ranking ζ 1 → M.TailResponseRegular 1 1 →
      M.EdgeNondegenerate (benchmarkSignal N radius) →
      ∀ O, O.ForwardKLAccurate M (MainKLUpperTheorem.rowBudget N radius) →
        A.WithinTotalOracleCalls O (klTotalCallCap N radius ζ growth)

end Finite
/-- The total-call and depth guarantees are uniform over the public target
class for the actual balanced TV parameter choice on a genuine tail. -/
theorem tv_totalGuarantee_eventually (V : ℕ → Type*)
    [∀ N, Fintype (V N)] [∀ N, DecidableEq (V N)] [∀ N, LinearOrder (V N)] [∀ N, Nonempty (V N)]
    (radius ζ growth : ℝ) (error : ℕ → ℝ)
    (hr : 0 < radius) (hr1 : radius ≤ 1) (hζ : 1 < ζ) (hg : (1/3 : ℝ) < growth)
    (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (Fintype.card (V N) : ℝ) = (N : ℝ)^(growth + error N)) :
    ∀ᶠ N : ℕ in atTop,
      ∃ (hN : 0 < N) (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
        (hm : 16 * max (radius / Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N radius),
      TVTotalGuarantee radius ζ (MainUpperTheorem.parameters N (V N) radius ζ hN hr hr1 hD hm) ∧
        (tvTotalCallCap N radius ζ : ℝ) ≤
          2 + MainUpperTheorem.queryEnvelope N radius ζ + MainUpperTheorem.roundEnvelope N radius ζ := by
  filter_upwards [MainUpperTheorem.balanced_grid_upper_eventually V radius ζ growth error
    hr hr1 hζ hg herror hvocab] with N hN
  obtain ⟨hn, hD, hm, hg, hq, hround⟩ := hN
  refine ⟨hn, hD, hm, ?_, ?_⟩
  · refine ⟨hg, tv_parameters_withinOracleDepth radius ζ hn hr hr1 hD hm, ?_⟩
    intro M ranking hRF hRT hUEN O hO
    exact ((hg M ranking hRF hRT hUEN).2.2 O hO).withinTotalOracleCalls
  · unfold tvTotalCallCap
    push_cast
    linarith

/-- The same packaged conclusion for the actual KL failure allocation;
no replacement repetition schedule or seed law is introduced. -/
theorem kl_totalGuarantee_eventually (V : ℕ → Type*)
    [∀ N, Fintype (V N)] [∀ N, DecidableEq (V N)] [∀ N, LinearOrder (V N)] [∀ N, Nonempty (V N)]
    (radius ζ growth : ℝ) (error : ℕ → ℝ)
    (hr : 0 < radius) (hr1 : radius ≤ 1) (hζ : 1 < ζ) (hg : (1/3 : ℝ) < growth)
    (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (Fintype.card (V N) : ℝ) = (N : ℝ)^(growth + error N)) :
    ∀ᶠ N : ℕ in atTop,
      ∃ (hN : 0 < N) (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
        (hm : 16 * max (radius / Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N radius),
      KLTotalGuarantee radius ζ growth
        (MainKLUpperTheorem.parameters N (V N) radius ζ hN hr hr1 hD hm) ∧
        (klTotalCallCap N radius ζ growth : ℝ) ≤
          2 + MainKLUpperTheorem.queryEnvelope N radius ζ growth + MainUpperTheorem.roundEnvelope N radius ζ := by
  filter_upwards [MainKLUpperTheorem.balanced_grid_kl_upper_eventually V radius ζ growth error
    hr hr1 hζ hg herror hvocab] with N hN
  obtain ⟨hn, hD, hm, hg, hq, hround⟩ := hN
  refine ⟨hn, hD, hm, ?_, ?_⟩
  · refine ⟨hg, kl_parameters_withinOracleDepth radius ζ hn hr hr1 hD hm, ?_⟩
    intro M ranking hRF hRT hUEN O hO
    exact (hg M ranking hRF hRT hUEN O hO).2.2.withinTotalOracleCalls
  · unfold klTotalCallCap
    push_cast
    linarith

end
end MainResourceTotals
end ForestSampling
