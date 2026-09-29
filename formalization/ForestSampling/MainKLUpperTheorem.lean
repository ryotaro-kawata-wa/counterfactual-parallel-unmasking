import ForestSampling.MainUpperTheorem

set_option autoImplicit false
open Filter Topology

namespace ForestSampling.MainKLUpperTheorem
noncomputable section

/-- The exact calibrated public KL row and screen-failure allowances. -/
def rowBudget (N : ℕ) (radius : ℝ) : ℝ := radius^2 / (N : ℝ)
def failureBudget (N vocab : ℕ) (radius : ℝ) : ℝ := radius^2 / ((N : ℝ) * Real.log vocab)

def failureCoefficient (radius growth : ℝ) : ℝ := radius^2 / (growth + 1)

/-- One public target-independent query cap for the original KL sampler. -/
def queryEnvelope (N : ℕ) (radius ζ growth : ℝ) : ℝ :=
  1088 * UpperRates.screenConstant * UpperRates.repetitionConstant (failureCoefficient radius growth) 2 *
    ((16 : ℝ) ^ (1 / ζ) + 1) * UpperRates.balancedScale N (benchmarkSignal N radius) ζ *
    UpperRates.logWeight N ^ 2

def queryCap (N : ℕ) (radius ζ growth : ℝ) : ℕ := ⌈queryEnvelope N radius ζ growth⌉₊

/-- Literal vocabulary growth yields the inverse-polynomial allocation
needed by the exact repetition ceiling; no logarithmic rate is assumed. -/
theorem failureBudget_eventually (vocabulary : ℕ → ℕ) (radius growth : ℝ) (error : ℕ → ℝ)
    (hr : 0 < radius) (hr1 : radius ≤ 1) (hg : 0 < growth)
    (he : Tendsto error atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, (vocabulary N : ℝ) = (N : ℝ)^(growth + error N)) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (vocabulary N) ∧ 0 < failureBudget N (vocabulary N) radius ∧
      failureBudget N (vocabulary N) radius ≤ 1 ∧
      failureCoefficient radius growth / (N : ℝ)^(2 : ℝ) ≤ failureBudget N (vocabulary N) radius := by
  have hlo := he.eventually_const_lt (show -growth/2 < 0 by linarith)
  have hhi := he.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hv, hlo, hhi, hlog.eventually_ge_atTop (2/growth),
    eventually_ge_atTop (1 : ℕ)] with N hvN hloN hhiN hlN hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hln : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hn1
  have hleq : Real.log (vocabulary N) = (growth + error N) * Real.log (N : ℝ) := by
    rw [hvN, Real.log_rpow hn]
  have hlg : 1 ≤ Real.log (vocabulary N) := by
    have hh := (div_le_iff₀ hg).mp hlN
    rw [hleq]
    nlinarith
  have hlu : Real.log (vocabulary N) ≤ (growth + 1) * (N : ℝ) := by
    have hlnu := Real.log_le_sub_one_of_pos hn
    rw [hleq]
    have hg1 : 0 ≤ growth + 1 := by linarith
    nlinarith
  have hden : 0 < (N : ℝ) * Real.log (vocabulary N) := by positivity
  have hden1 : 1 ≤ (N : ℝ) * Real.log (vocabulary N) := one_le_mul_of_one_le_of_one_le hn1 hlg
  have hbig : 0 < (growth + 1) * (N : ℝ)^2 := by positivity
  have hdenle : (N : ℝ) * Real.log (vocabulary N) ≤ (growth + 1) * (N : ℝ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlu hn.le]
  refine ⟨hlg, by unfold failureBudget; positivity, ?_, ?_⟩
  · unfold failureBudget
    apply (div_le_one hden).mpr
    nlinarith
  · unfold failureCoefficient failureBudget
    rw [Real.rpow_two]
    calc
      _ = radius^2 / ((growth + 1) * (N : ℝ)^2) := by rw [div_div]
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg radius) hden hdenle

/-- The exact two KL error contributions both equal the squared public
radius. This concerns the actual seed-averaged forward KL loss. -/
theorem calibrated_error (N vocab : ℕ) (radius : ℝ) (hN : 0 < N) (hl : 0 < Real.log vocab) :
    (N : ℝ) * rowBudget N radius + (N : ℝ) * Real.log vocab * failureBudget N vocab radius =
      2 * radius^2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold rowBudget failureBudget
  field_simp
  <;> ring

theorem queryEnvelope_nonneg (N : ℕ) (radius ζ growth : ℝ) : 0 ≤ queryEnvelope N radius ζ growth := by
  have hs : 0 ≤ benchmarkSignal N radius := by unfold benchmarkSignal; positivity
  have hp : 0 ≤ UpperRates.balancedScale N (benchmarkSignal N radius) ζ := by
    unfold UpperRates.balancedScale
    positivity
  unfold queryEnvelope
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num) UpperRates.screenConstant_pos.le)
    (UpperRates.repetitionConstant_pos _ 2 (by norm_num)).le) (by positivity)) hp) (sq_nonneg _)

theorem queryCap_le (N : ℕ) (radius ζ growth : ℝ) :
    (queryCap N radius ζ growth : ℝ) ≤ queryEnvelope N radius ζ growth + 1 :=
  (Nat.ceil_lt_add_one (queryEnvelope_nonneg N radius ζ growth)).le

/-- Both logarithmic query factors and the final integer ceiling remain
strictly sublinear at the concrete benchmark signal. -/
theorem queryCap_isLittleO (radius ζ growth : ℝ) (hr : 0 < radius) (hζ : 1 < ζ) :
    (fun N : ℕ ↦ (queryCap N radius ζ growth : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have he : (fun N : ℕ ↦ queryEnvelope N radius ζ growth) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
    have hh := (UpperRates.benchmark_balanced_logWeight_sq_isLittleO radius ζ hr hζ).const_mul_left
      (1088 * UpperRates.screenConstant * UpperRates.repetitionConstant (failureCoefficient radius growth) 2 *
        ((16 : ℝ)^(1/ζ)+1))
    apply hh.congr_left
    intro N
    unfold queryEnvelope
    ring
  have h1 : (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
    simpa only [Function.comp_def, id_eq] using
      (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop)
  have hb : (fun N : ℕ ↦ (queryCap N radius ζ growth : ℝ)) =O[atTop]
      (fun N : ℕ ↦ queryEnvelope N radius ζ growth + 1) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    exact Eventually.of_forall (fun N ↦ by simpa using queryCap_le N radius ζ growth)
  exact hb.trans_isLittleO (he.add h1)

section Finite
variable {N : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]

/-- The original public dyadic sampler with the exact KL failure allocation. -/
def parameters (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (radius ζ : ℝ) (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius) :
    PackedSampler.Parameters N V :=
  ThresholdGrid.parameters N V
    (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    radius (failureBudget N (Fintype.card V) radius) 1 1 1 (benchmarkSignal N radius / 2)
    hN (by omega) (by norm_num) (MainUpperTheorem.standardFloor_le_one radius hN hr hr1 hm)
    (MainUpperTheorem.grid_nonempty radius hN hr hr1 hm)

/-- Every accurate oracle produces banks within the same public balanced
query cap. The cap applies to every seed and every possible commit outcome. -/
theorem parameters_withinOracleBudgets (M : ForestModel N V) (O : FrozenOracle N V)
    (ranking : MarginalRanking M) (radius ζ growth : ℝ)
    (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1) (hζ : 1 < ζ)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hx : 1 ≤ UpperRates.balancedCutoffReal N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius)
    (hg : 0 < growth)
    (hη : 0 < failureBudget N (Fintype.card V) radius)
    (hη1 : failureBudget N (Fintype.card V) radius ≤ 1)
    (hlower : failureCoefficient radius growth / (N : ℝ)^(2 : ℝ) ≤ failureBudget N (Fintype.card V) radius)
    (hRF : FiniteRankFrequency M ranking ζ 1) (hO : O.ForwardKLAccurate M (rowBudget N radius)) :
    (PackedSampler.sampler
      (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)))
      (parameters N V radius ζ hN hr hr1 hD hm)).WithinOracleBudgets O
        (queryCap N radius ζ growth) (MainUpperTheorem.roundCap N radius ζ) := by
  have hAcc := hO.accurate hr.le hr1 le_rfl
  let η := failureBudget N (Fintype.card V) radius
  let D := UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ
  let signal := benchmarkSignal N radius
  let ε := radius / Real.sqrt N
  have hs := benchmarkSignal_bounds N radius (by omega) hr hr1
  let hf1 := MainUpperTheorem.standardFloor_le_one radius hN hr hr1 hm
  let hgrid := MainUpperTheorem.grid_nonempty radius hN hr hr1 hm
  let t := ThresholdGrid.selected (ThresholdGrid.standardFloor N V radius 1) 1 1 (signal / 2) hgrid
  have ht := ThresholdGrid.standard_selected_spec radius 1 1 1 (signal / 2) (by norm_num) hf1 hgrid
  let hc := ht.2.2.2.1
  have hcolumns : (PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hc) : ℝ) ≤
      (16 / signal) ^ (1 / ζ) + 1 := by
    have hgb : (ThresholdGrid.feasible (UpperRates.benchmarkFloor (Fintype.card V) ε)
        1 1 (signal / 2)).Nonempty := by
      simpa only [ThresholdGrid.standardFloor, UpperRates.benchmarkFloor, one_div, ε] using hgrid
    have hcb : (Fintype.card V : ℝ)⁻¹ <
        ThresholdGrid.selected (UpperRates.benchmarkFloor (Fintype.card V) ε) 1 1 (signal / 2) hgb - ε := by
      simpa only [t, ThresholdGrid.standardFloor, UpperRates.benchmarkFloor, one_div, ε] using hc
    have hh := UpperRates.benchmark_columns_le M O ranking ζ ε signal (by linarith) hRF
      hs.1 hs.2.1 hm hgb hcb (fun y j ↦ hAcc.tv_bound hN y j)
    simpa only [t, ThresholdGrid.standardFloor, UpperRates.benchmarkFloor, one_div, ε] using hh
  have hq := UpperRates.queryCount_le_balanced_logWeight N
    (PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hc)) signal ζ η (failureCoefficient radius growth) 2
    hN hD hs.1 (by linarith [hs.2.1]) (by linarith) hx hη hη1
    (by unfold failureCoefficient; positivity) (by norm_num) hlower hcolumns
  have hqNat : UpperRates.queryCount N D D
      (PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hc)) η ≤ queryCap N radius ζ growth := by
    have hbound := hq.trans (Nat.le_ceil (queryEnvelope N radius ζ growth))
    exact_mod_cast hbound
  intro blocks
  apply Program.WithinBudgets.withinOracleBudgets
  have hprogram := UpperRates.selected_program_within_queryCount O D t radius η hN (by omega) hc blocks
  apply Program.withinBudgets_mono _ hprogram hqNat le_rfl


/-- Forward-KL row accuracy gives the exact output KL bound for the actual
public grid sampler and its original finite seed law. -/
theorem parameters_seedKLRisk_le (M : ForestModel N V) (O : FrozenOracle N V) (radius ζ : ℝ)
    (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius)
    (hl : 0 < Real.log (Fintype.card V))
    (hRT : M.TailResponseRegular 1 1) (hUEN : M.EdgeNondegenerate (benchmarkSignal N radius))
    (hO : O.ForwardKLAccurate M (rowBudget N radius)) :
    let P := parameters N V radius ζ hN hr hr1 hD hm
    (PackedSampler.sampler
      (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P).seedKLRisk
      (PackedSampler.seedLaw
        (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P).toMeasure
      M O ≤ 2 * radius^2 := by
  dsimp only
  have hs := benchmarkSignal_bounds N radius (by omega) hr hr1
  have hmarg : 4 * (radius / Real.sqrt N) + benchmarkSignal N radius / 2 < benchmarkSignal N radius := by
    have hh := le_max_left (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹
    linarith
  have ht := ThresholdGrid.standard_selected_spec radius 1 1 1 (benchmarkSignal N radius / 2)
    (by norm_num) (MainUpperTheorem.standardFloor_le_one radius hN hr hr1 hm)
    (MainUpperTheorem.grid_nonempty radius hN hr hr1 hm)
  have hη : 0 < failureBudget N (Fintype.card V) radius := by unfold failureBudget; positivity
  have hb := PackedSampler.sampler_seedKLRisk_le
    (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)))
    (parameters N V radius ζ hN hr hr1 hD hm) M O
    1 1 (benchmarkSignal N radius / 2) (benchmarkSignal N radius) radius (rowBudget N radius)
    (failureBudget N (Fintype.card V) radius)
    hN hD rfl rfl rfl (div_nonneg hs.1.le (by norm_num)) ht.1.le ht.2.1 hRT hUEN ht.2.2.1 hmarg
    hη hr.le hr1 hO le_rfl
    (show 8 * (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ + 1) ≤
      Fintype.card (Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) by
      rw [Fintype.card_eq_nat_card, Nat.card_fin]
      exact le_rfl)
    (Nat.le_ceil _)
  exact hb.trans_eq (calibrated_error N (Fintype.card V) radius hN hl)

/-- A single public KL sampler precedes the target, ranking, and frozen
oracle quantifiers; all losses and hard caps are for that actual sampler. -/
def UniformGuarantee (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (radius ζ growth : ℝ) (P : PackedSampler.Parameters N V) : Prop :=
  let A := PackedSampler.sampler
    (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P
  let μ := (PackedSampler.seedLaw
    (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P).toMeasure
  ∀ (M : ForestModel N V) (ranking : MarginalRanking M),
    FiniteRankFrequency M ranking ζ 1 → M.TailResponseRegular 1 1 →
    M.EdgeNondegenerate (benchmarkSignal N radius) →
    ∀ (O : FrozenOracle N V), O.ForwardKLAccurate M (rowBudget N radius) →
      A.KLRiskMeasurableAt μ M O ∧ A.seedKLRisk μ M O ≤ 2 * radius^2 ∧
        A.WithinOracleBudgets O (queryCap N radius ζ growth) (MainUpperTheorem.roundCap N radius ζ)

/-- The finite assembly has no surrogate rate or safety hypotheses: the
remaining assumptions concern only the explicit public feasibility margins. -/
theorem finite_uniformGuarantee (radius ζ growth : ℝ)
    (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1) (hζ : 1 < ζ) (hg : 0 < growth)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hx : 1 ≤ UpperRates.balancedCutoffReal N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius)
    (hl : 0 < Real.log (Fintype.card V))
    (hη : 0 < failureBudget N (Fintype.card V) radius)
    (hη1 : failureBudget N (Fintype.card V) radius ≤ 1)
    (hlower : failureCoefficient radius growth / (N : ℝ)^(2 : ℝ) ≤ failureBudget N (Fintype.card V) radius) :
    UniformGuarantee N V radius ζ growth (parameters N V radius ζ hN hr hr1 hD hm) := by
  intro M ranking hRF hRT hUEN O hO
  refine ⟨(measurable_of_finite _).aestronglyMeasurable,
    parameters_seedKLRisk_le M O radius ζ hN hr hr1 hD hm hl hRT hUEN hO, ?_⟩
  exact parameters_withinOracleBudgets M O ranking radius ζ growth hN hr hr1 hζ hD hx hm hg
    hη hη1 hlower hRF hO

end Finite

/-- The original balanced dyadic sampler attains the main fixed-radius KL
upper guarantee with literal vocabulary growth. The failure allocation is
exactly `radius²/(N log V)`, and its repetition rate is derived here. -/
theorem balanced_grid_kl_upper_eventually (V : ℕ → Type*)
    [∀ N, Fintype (V N)] [∀ N, DecidableEq (V N)] [∀ N, LinearOrder (V N)] [∀ N, Nonempty (V N)]
    (radius ζ growth : ℝ) (error : ℕ → ℝ)
    (hr : 0 < radius) (hr1 : radius ≤ 1) (hζ : 1 < ζ) (hg : (1/3 : ℝ) < growth)
    (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (Fintype.card (V N) : ℝ) = (N : ℝ)^(growth + error N)) :
    ∀ᶠ N : ℕ in atTop,
      ∃ (hN : 0 < N) (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
        (hm : 16 * max (radius / Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N radius),
      UniformGuarantee N (V N) radius ζ growth (parameters N (V N) radius ζ hN hr hr1 hD hm) ∧
        (queryCap N radius ζ growth : ℝ) ≤ queryEnvelope N radius ζ growth + 1 ∧
        (MainUpperTheorem.roundCap N radius ζ : ℝ) ≤ MainUpperTheorem.roundEnvelope N radius ζ := by
  have hfloor := UpperFeasibilityGrowth.benchmark_floor_eventually
    (fun N ↦ Fintype.card (V N)) radius growth error hr hg herror hvocab
  have hcut := UpperFeasibilityGrowth.benchmark_balancedCutoff_eventually radius ζ hr hζ
  have hfailure := failureBudget_eventually (fun N ↦ Fintype.card (V N)) radius growth error
    hr hr1 (by linarith) herror hvocab
  filter_upwards [hfloor, hcut, hfailure, eventually_ge_atTop (10 : ℕ)] with N hmargin hcutN hfailureN hN
  have hn : 0 < N := by omega
  have hm : 16 * max (radius / Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N radius := by
    simpa only [one_div] using hmargin
  refine ⟨hn, hcutN.2.1, hm,
    finite_uniformGuarantee radius ζ growth hn hr hr1 hζ (by linarith) hcutN.2.1 hcutN.1 hm
      (by linarith [hfailureN.1]) hfailureN.2.1 hfailureN.2.2.1 hfailureN.2.2.2,
    queryCap_le N radius ζ growth, ?_⟩
  exact UpperRates.hardRoundCap_le_balanced_logWeight N (benchmarkSignal N radius) ζ hn
    hcutN.2.1 (by omega) (benchmarkSignal_bounds N radius (by omega) hr hr1).1 hcutN.1

/-- The common single-accuracy substitution used in the main theorem gives
at most the requested output KL error, with the same public row radius. -/
theorem halfRadius_error_le (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    2 * (ε / 2)^2 ≤ ε := by nlinarith


/-- The main theorem's single requested accuracy, using the same public
radius `epsilon/2` in its class and its original grid-selected sampler. -/
def UniformTargetGuarantee (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (ε ζ growth : ℝ) (P : PackedSampler.Parameters N V) : Prop :=
  let radius := ε / 2
  let A := PackedSampler.sampler
    (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P
  let μ := (PackedSampler.seedLaw
    (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P).toMeasure
  ∀ (M : ForestModel N V) (ranking : MarginalRanking M),
    FiniteRankFrequency M ranking ζ 1 → M.TailResponseRegular 1 1 →
    M.EdgeNondegenerate (benchmarkSignal N radius) →
    ∀ (O : FrozenOracle N V), O.ForwardKLAccurate M (rowBudget N radius) →
      A.KLRiskMeasurableAt μ M O ∧ A.seedKLRisk μ M O ≤ ε ∧
        A.WithinOracleBudgets O (queryCap N radius ζ growth) (MainUpperTheorem.roundCap N radius ζ)

/-- The same actual sampler, oracle class, seed law, and hard resource caps
satisfy the requested output KL tolerance after the public substitution. -/
theorem UniformGuarantee.halfRadius_target {N : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (ε ζ growth : ℝ) (P : PackedSampler.Parameters N V) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h : UniformGuarantee N V (ε / 2) ζ growth P) : UniformTargetGuarantee N V ε ζ growth P := by
  intro M ranking hRF hRT hUEN O hO
  obtain ⟨hmeas, hrisk, hbudget⟩ := h M ranking hRF hRT hUEN O hO
  exact ⟨hmeas, hrisk.trans (halfRadius_error_le ε hε hε1), hbudget⟩

/-- The actual fixed single-accuracy main KL theorem, with all eventual
finite-domain, grid, rank-frequency, failure-allocation, and resource bridges
discharged from the literal vocabulary-growth assumption. -/
theorem balanced_grid_kl_target_error_eventually (V : ℕ → Type*)
    [∀ N, Fintype (V N)] [∀ N, DecidableEq (V N)] [∀ N, LinearOrder (V N)] [∀ N, Nonempty (V N)]
    (ε ζ growth : ℝ) (error : ℕ → ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 1 < ζ) (hg : (1/3 : ℝ) < growth)
    (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (Fintype.card (V N) : ℝ) = (N : ℝ)^(growth + error N)) :
    ∀ᶠ N : ℕ in atTop,
      ∃ (hN : 0 < N) (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N (ε/2)) ζ)
        (hm : 16 * max ((ε/2) / Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N (ε/2)),
      UniformTargetGuarantee N (V N) ε ζ growth
        (parameters N (V N) (ε/2) ζ hN (by positivity) (by linarith) hD hm) ∧
        (queryCap N (ε/2) ζ growth : ℝ) ≤ queryEnvelope N (ε/2) ζ growth + 1 ∧
        (MainUpperTheorem.roundCap N (ε/2) ζ : ℝ) ≤ MainUpperTheorem.roundEnvelope N (ε/2) ζ := by
  filter_upwards [balanced_grid_kl_upper_eventually V (ε/2) ζ growth error
    (by positivity) (by linarith) hζ hg herror hvocab] with N hN
  obtain ⟨hN, hD, hm, hguarantee, hQ, hR⟩ := hN
  exact ⟨hN, hD, hm, hguarantee.halfRadius_target ε ζ growth _ hε.le hε1, hQ, hR⟩

end
end ForestSampling.MainKLUpperTheorem
