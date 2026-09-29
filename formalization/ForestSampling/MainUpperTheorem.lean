import ForestSampling.GridUpperTheorem
import ForestSampling.UpperFeasibilityGrowth
import ForestSampling.OracleBudgets

set_option autoImplicit false
open Filter Topology

namespace ForestSampling.MainUpperTheorem

noncomputable section

/-- A single public query allowance, independent of the target and the
frozen oracle, for the actual balanced grid-selected sampler. -/
def queryEnvelope (N : ℕ) (radius ζ : ℝ) : ℝ :=
  1088 * UpperRates.screenConstant * UpperRates.repetitionConstant radius 0 *
    ((16 : ℝ) ^ (1 / ζ) + 1) *
    UpperRates.balancedScale N (benchmarkSignal N radius) ζ * UpperRates.logWeight N ^ 2

def queryCap (N : ℕ) (radius ζ : ℝ) : ℕ := ⌈queryEnvelope N radius ζ⌉₊

def roundCap (N : ℕ) (radius ζ : ℝ) : ℕ :=
  ForestIteration.hardRoundCap N (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)

def roundEnvelope (N : ℕ) (radius ζ : ℝ) : ℝ :=
  UpperRates.roundConstant * UpperRates.balancedScale N (benchmarkSignal N radius) ζ *
    UpperRates.logWeight N


/-- The public real query bound is nonnegative even at degenerate lengths. -/
theorem queryEnvelope_nonneg (N : ℕ) (radius ζ : ℝ) : 0 ≤ queryEnvelope N radius ζ := by
  have hs : 0 ≤ benchmarkSignal N radius := by unfold benchmarkSignal; positivity
  have hp : 0 ≤ UpperRates.balancedScale N (benchmarkSignal N radius) ζ := by
    unfold UpperRates.balancedScale
    positivity
  unfold queryEnvelope
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num) UpperRates.screenConstant_pos.le)
    (UpperRates.repetitionConstant_pos radius 0 (by norm_num)).le) (by positivity)) hp) (sq_nonneg _)

/-- Rounding the single public query cap adds less than one query to the
explicit real envelope. -/
theorem queryCap_le (N : ℕ) (radius ζ : ℝ) :
    (queryCap N radius ζ : ℝ) ≤ queryEnvelope N radius ζ + 1 :=
  (Nat.ceil_lt_add_one (queryEnvelope_nonneg N radius ζ)).le

/-- The single public integer query cap is strictly sublinear, including
both logarithmic factors and the final natural ceiling. -/
theorem queryCap_isLittleO (radius ζ : ℝ) (hr : 0 < radius) (hζ : 1 < ζ) :
    (fun N : ℕ ↦ (queryCap N radius ζ : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have he : (fun N : ℕ ↦ queryEnvelope N radius ζ) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
    have hh := (UpperRates.benchmark_balanced_logWeight_sq_isLittleO radius ζ hr hζ).const_mul_left
      (1088 * UpperRates.screenConstant * UpperRates.repetitionConstant radius 0 * ((16 : ℝ)^(1/ζ)+1))
    apply hh.congr_left
    intro N
    unfold queryEnvelope
    ring
  have h1 : (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
    simpa only [Function.comp_def, id_eq] using
      (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop)
  have hb : (fun N : ℕ ↦ (queryCap N radius ζ : ℝ)) =O[atTop]
      (fun N : ℕ ↦ queryEnvelope N radius ζ + 1) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    exact Eventually.of_forall (fun N ↦ by simpa using queryCap_le N radius ζ)
  exact hb.trans_isLittleO (he.add h1)

/-- The original hard-round cap is strictly sublinear under the exact
rounded public balancing rule. Its finite cutoff conditions are proved
eventually rather than assumed as asymptotic rate hypotheses. -/
theorem roundCap_isLittleO (radius ζ : ℝ) (hr : 0 < radius) (hζ : 1 < ζ) :
    (fun N : ℕ ↦ (roundCap N radius ζ : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have hk : 0 ≤ UpperRates.roundConstant := by
    have h9 : 0 < Real.log (9/8 : ℝ) := Real.log_pos (by norm_num)
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold UpperRates.roundConstant
    positivity
  have hh := (UpperRates.benchmark_balanced_logWeight_sq_isLittleO radius ζ hr hζ).const_mul_left
    UpperRates.roundConstant
  have hb : (fun N : ℕ ↦ (roundCap N radius ζ : ℝ)) =O[atTop]
      (fun N : ℕ ↦ UpperRates.roundConstant *
        (UpperRates.balancedScale N (benchmarkSignal N radius) ζ * UpperRates.logWeight N ^ 2)) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [UpperFeasibilityGrowth.benchmark_balancedCutoff_eventually radius ζ hr hζ,
      eventually_ge_atTop (1 : ℕ)] with N hD hN
    have hn : 0 < N := by omega
    have hs : 0 < benchmarkSignal N radius := by unfold benchmarkSignal; positivity
    have hscale : 0 ≤ UpperRates.balancedScale N (benchmarkSignal N radius) ζ := by
      unfold UpperRates.balancedScale
      positivity
    have hw := (UpperRates.logWeight_bounds N hn).1
    have hw2 : UpperRates.logWeight N ≤ UpperRates.logWeight N ^ 2 := by nlinarith
    have hround := UpperRates.hardRoundCap_le_balanced_logWeight N (benchmarkSignal N radius) ζ
      hn hD.2.1 (by omega) hs hD.1
    have hmul := mul_le_mul_of_nonneg_left hw2 (mul_nonneg hk hscale)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    change (ForestIteration.hardRoundCap N _ : ℝ) ≤ _
    nlinarith
  exact hb.trans_isLittleO hh

section Finite

variable {N : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]

/-- The finite benchmark margin implies the original public grid's upper
floor restriction, without changing the grid or the signal calibration. -/
theorem standardFloor_le_one (radius : ℝ) (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius) :
    ThresholdGrid.standardFloor N V radius 1 ≤ 1 := by
  have hb := UpperRates.benchmarkFloor_bounds (Fintype.card V) (radius / Real.sqrt N)
    (benchmarkSignal N radius) Fintype.card_pos hm
  have hs := (benchmarkSignal_bounds N radius (by omega) hr hr1).2.1
  simpa only [ThresholdGrid.standardFloor, UpperRates.benchmarkFloor, one_div] using
    (show UpperRates.benchmarkFloor (Fintype.card V) (radius / Real.sqrt N) ≤ 1 by linarith [hb.2])

/-- The actual public finite grid is nonempty at half of the concrete
benchmark signal, using the proved row and vocabulary feasibility margin. -/
theorem grid_nonempty (radius : ℝ) (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius) :
    (ThresholdGrid.feasible (ThresholdGrid.standardFloor N V radius 1) 1 1
      (benchmarkSignal N radius / 2)).Nonempty := by
  have hs := benchmarkSignal_bounds N radius (by omega) hr hr1
  simpa only [ThresholdGrid.standardFloor, UpperRates.benchmarkFloor, one_div] using
    UpperRates.benchmark_feasible (Fintype.card V) (radius / Real.sqrt N)
      (benchmarkSignal N radius) Fintype.card_pos hs.1 hs.2.1 hm

/-- All sampler parameters are fixed from public length, vocabulary,
accuracy, and exponent before the first all-mask oracle observation. -/
def parameters (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (radius ζ : ℝ) (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius) :
    PackedSampler.Parameters N V :=
  ThresholdGrid.parameters N V
    (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    radius radius 1 1 1 (benchmarkSignal N radius / 2) hN (by omega) (by norm_num)
    (standardFloor_le_one radius hN hr hr1 hm) (grid_nonempty radius hN hr hr1 hm)

/-- Every accurate oracle produces banks within the same public balanced
query cap. The cap applies to every seed and every possible commit outcome. -/
theorem parameters_withinOracleBudgets (M : ForestModel N V) (O : FrozenOracle N V)
    (ranking : MarginalRanking M) (radius ζ : ℝ)
    (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1) (hζ : 1 < ζ)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hx : 1 ≤ UpperRates.balancedCutoffReal N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius)
    (hRF : FiniteRankFrequency M ranking ζ 1) (hO : O.Accurate M radius) :
    (PackedSampler.sampler
      (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)))
      (parameters N V radius ζ hN hr hr1 hD hm)).WithinOracleBudgets O
        (queryCap N radius ζ) (roundCap N radius ζ) := by
  let D := UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ
  let signal := benchmarkSignal N radius
  let ε := radius / Real.sqrt N
  have hs := benchmarkSignal_bounds N radius (by omega) hr hr1
  let hf1 := standardFloor_le_one radius hN hr hr1 hm
  let hg := grid_nonempty radius hN hr hr1 hm
  let t := ThresholdGrid.selected (ThresholdGrid.standardFloor N V radius 1) 1 1 (signal / 2) hg
  have ht := ThresholdGrid.standard_selected_spec radius 1 1 1 (signal / 2) (by norm_num) hf1 hg
  let hc := ht.2.2.2.1
  have hcolumns : (PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hc) : ℝ) ≤
      (16 / signal) ^ (1 / ζ) + 1 := by
    have hgb : (ThresholdGrid.feasible (UpperRates.benchmarkFloor (Fintype.card V) ε)
        1 1 (signal / 2)).Nonempty := by
      simpa only [ThresholdGrid.standardFloor, UpperRates.benchmarkFloor, one_div, ε] using hg
    have hcb : (Fintype.card V : ℝ)⁻¹ <
        ThresholdGrid.selected (UpperRates.benchmarkFloor (Fintype.card V) ε) 1 1 (signal / 2) hgb - ε := by
      simpa only [t, ThresholdGrid.standardFloor, UpperRates.benchmarkFloor, one_div, ε] using hc
    have hh := UpperRates.benchmark_columns_le M O ranking ζ ε signal (by linarith) hRF
      hs.1 hs.2.1 hm hgb hcb (fun y j ↦ hO.tv_bound hN y j)
    simpa only [t, ThresholdGrid.standardFloor, UpperRates.benchmarkFloor, one_div, ε] using hh
  have hq := UpperRates.queryCount_le_balanced_logWeight N
    (PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hc)) signal ζ radius radius 0
    hN hD hs.1 (by linarith [hs.2.1]) (by linarith) hx hr hr1 hr (by norm_num)
    (by simp) hcolumns
  have hqNat : UpperRates.queryCount N D D
      (PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hc)) radius ≤ queryCap N radius ζ := by
    have hbound := hq.trans (Nat.le_ceil (queryEnvelope N radius ζ))
    exact_mod_cast hbound
  intro blocks
  apply Program.WithinBudgets.withinOracleBudgets
  have hprogram := UpperRates.selected_program_within_queryCount O D t radius radius hN (by omega) hc blocks
  apply Program.withinBudgets_mono _ hprogram hqNat le_rfl

/-- The same public sampler has the actual robust TV guarantee uniformly
over the full target and frozen Hellinger-oracle class. -/
theorem parameters_robustRisk_le (M : ForestModel N V) (radius ζ : ℝ)
    (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius)
    (hRT : M.TailResponseRegular 1 1) (hUEN : M.EdgeNondegenerate (benchmarkSignal N radius)) :
    let P := parameters N V radius ζ hN hr hr1 hD hm
    let A := PackedSampler.sampler
      (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P
    let μ := (PackedSampler.seedLaw
      (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P).toMeasure
    A.RiskMeasurable μ M radius ∧ A.robustRisk μ M radius ≤ 2 * radius := by
  dsimp only
  have hs := benchmarkSignal_bounds N radius (by omega) hr hr1
  have hmarg : 4 * (radius / Real.sqrt N) + benchmarkSignal N radius / 2 < benchmarkSignal N radius := by
    have hh := le_max_left (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹
    linarith
  have ht := ThresholdGrid.standard_selected_spec radius 1 1 1 (benchmarkSignal N radius / 2)
    (by norm_num) (standardFloor_le_one radius hN hr hr1 hm) (grid_nonempty radius hN hr hr1 hm)
  constructor
  · intro O
    exact (measurable_of_finite _).aestronglyMeasurable
  · let : Nonempty (FrozenOracle.Class M radius) :=
      ⟨⟨FrozenOracle.exact M, FrozenOracle.exact_accurate M hN hr.le hr1⟩⟩
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨O, rfl⟩
    have hb := PackedSampler.sampler_seedRisk_le
      (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)))
      (parameters N V radius ζ hN hr hr1 hD hm) M O.1
      1 1 (benchmarkSignal N radius / 2) (benchmarkSignal N radius) radius radius
      hN hD rfl rfl rfl (div_nonneg hs.1.le (by norm_num)) ht.1.le ht.2.1 hRT hUEN
      ht.2.2.1 hmarg hr O.2
      (show 8 * (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ + 1) ≤
        Fintype.card (Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) by
        rw [Fintype.card_eq_nat_card, Nat.card_fin]
        exact le_rfl)
      (Nat.le_ceil _)
    simpa only [two_mul] using hb


/-- The single public sampler is quantified before every target and frozen
oracle. It has measurable robust loss and common hard resource caps. -/
def UniformGuarantee (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (radius ζ : ℝ) (P : PackedSampler.Parameters N V) : Prop :=
  let A := PackedSampler.sampler
    (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P
  let μ := (PackedSampler.seedLaw
    (Color := Fin (PackedSampler.colorCount (UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ))) P).toMeasure
  ∀ (M : ForestModel N V) (ranking : MarginalRanking M),
    FiniteRankFrequency M ranking ζ 1 → M.TailResponseRegular 1 1 →
    M.EdgeNondegenerate (benchmarkSignal N radius) →
    A.RiskMeasurable μ M radius ∧ A.robustRisk μ M radius ≤ 2 * radius ∧
      ∀ (O : FrozenOracle N V), O.Accurate M radius →
        A.WithinOracleBudgets O (queryCap N radius ζ) (roundCap N radius ζ)

/-- The actual balanced grid parameter object satisfies the full finite
uniform target/oracle theorem once its explicit public margins hold. -/
theorem finite_uniformGuarantee (radius ζ : ℝ)
    (hN : 0 < N) (hr : 0 < radius) (hr1 : radius ≤ 1) (hζ : 1 < ζ)
    (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
    (hx : 1 ≤ UpperRates.balancedCutoffReal N (benchmarkSignal N radius) ζ)
    (hm : 16 * max (radius / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N radius) :
    UniformGuarantee N V radius ζ (parameters N V radius ζ hN hr hr1 hD hm) := by
  intro M ranking hRF hRT hUEN
  have hrisk := parameters_robustRisk_le M radius ζ hN hr hr1 hD hm hRT hUEN
  exact ⟨hrisk.1, hrisk.2, fun O hO ↦
    parameters_withinOracleBudgets M O ranking radius ζ hN hr hr1 hζ hD hx hm hRF hO⟩

end Finite

/-- The main fixed-accuracy TV upper theorem for literal polynomial
vocabulary growth. The sampler is the original publicly selected dyadic
sampler, its cutoff is the actual natural ceiling, and the uniform query
and round caps have explicit logarithmic envelopes. Together with the two
`*_isLittleO` theorems, both actual hard caps are `o(N)`. -/
theorem balanced_grid_upper_eventually (V : ℕ → Type*)
    [∀ N, Fintype (V N)] [∀ N, DecidableEq (V N)] [∀ N, LinearOrder (V N)] [∀ N, Nonempty (V N)]
    (radius ζ growth : ℝ) (error : ℕ → ℝ)
    (hr : 0 < radius) (hr1 : radius ≤ 1) (hζ : 1 < ζ) (hg : (1/3 : ℝ) < growth)
    (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (Fintype.card (V N) : ℝ) = (N : ℝ)^(growth + error N)) :
    ∀ᶠ N : ℕ in atTop,
      ∃ (hN : 0 < N) (hD : 9 ≤ UpperRates.balancedCutoff N (benchmarkSignal N radius) ζ)
        (hm : 16 * max (radius / Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N radius),
      UniformGuarantee N (V N) radius ζ (parameters N (V N) radius ζ hN hr hr1 hD hm) ∧
        (queryCap N radius ζ : ℝ) ≤ queryEnvelope N radius ζ + 1 ∧
        (roundCap N radius ζ : ℝ) ≤ roundEnvelope N radius ζ := by
  have hfloor := UpperFeasibilityGrowth.benchmark_floor_eventually
    (fun N ↦ Fintype.card (V N)) radius growth error hr hg herror hvocab
  have hcut := UpperFeasibilityGrowth.benchmark_balancedCutoff_eventually radius ζ hr hζ
  filter_upwards [hfloor, hcut, eventually_ge_atTop (10 : ℕ)] with N hmargin hcutN hN
  have hn : 0 < N := by omega
  have hm : 16 * max (radius / Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N radius := by
    simpa only [one_div] using hmargin
  refine ⟨hn, hcutN.2.1, hm, finite_uniformGuarantee radius ζ hn hr hr1 hζ hcutN.2.1 hcutN.1 hm,
    queryCap_le N radius ζ, ?_⟩
  exact UpperRates.hardRoundCap_le_balanced_logWeight N (benchmarkSignal N radius) ζ hn
    hcutN.2.1 (by omega) (benchmarkSignal_bounds N radius (by omega) hr hr1).1 hcutN.1

end
end ForestSampling.MainUpperTheorem
