import ForestSampling.MainUpperTheorem
import ForestSampling.MainKLUpperTheorem
import ForestSampling.PackedDepth

set_option autoImplicit false
open Filter Topology

namespace ForestSampling.GeneralUpperCurve
noncomputable section

/-- A single public envelope for every prescribed cutoff, with two explicit
logarithmic factors and a public lower bound on the failure allocation. -/
def queryEnvelope (N D : ℕ) (ρ ζ c a : ℝ) : ℝ :=
  272 * UpperRates.screenConstant * UpperRates.repetitionConstant c a *
    ((16 / benchmarkSignal N ρ)^(1/ζ)+1) * (D : ℝ)^2 * UpperRates.logWeight N^2

def queryCap (N D : ℕ) (ρ ζ c a : ℝ) : ℕ := ⌈queryEnvelope N D ρ ζ c a⌉₊

def depthCap (N D : ℕ) : ℕ :=
  1 + ForestIteration.hardRoundCap N D + (ForestIteration.phaseCap N D+1)

/-- Generic-cutoff public parameters use exactly the original selected
finite grid and leave the failure allocation visible. -/
def parameters (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (D : ℕ) (ρ η : ℝ) (hN : 0 < N) (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hD : 9 ≤ D)
    (hm : 16 * max (ρ / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N ρ) :
    PackedSampler.Parameters N V :=
  ThresholdGrid.parameters N V D D ρ η 1 1 1 (benchmarkSignal N ρ/2) hN (by omega) (by norm_num)
    (MainUpperTheorem.standardFloor_le_one ρ hN hr hr1 hm)
    (MainUpperTheorem.grid_nonempty ρ hN hr hr1 hm)

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]

/-- Actual observed banks and all paths satisfy one public query cap for
every cutoff; the public cap never depends on the target or oracle. -/
theorem parameters_withinOracleBudgets (M : ForestModel N V) (O : FrozenOracle N V)
    (ranking : MarginalRanking M) (D : ℕ) (ρ ζ η c a : ℝ)
    (hN : 0 < N) (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (hD : 9 ≤ D)
    (hη : 0 < η) (hη1 : η ≤ 1) (hc : 0 < c) (ha : 0 ≤ a)
    (hlower : c/(N : ℝ)^a ≤ η)
    (hm : 16 * max (ρ/Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N ρ)
    (hRF : FiniteRankFrequency M ranking ζ 1) (hO : O.Accurate M ρ) :
    (PackedSampler.sampler (Color := Fin (PackedSampler.colorCount D))
      (parameters N V D ρ η hN hr hr1 hD hm)).WithinOracleBudgets O
        (queryCap N D ρ ζ c a) (ForestIteration.hardRoundCap N D) := by
  let signal := benchmarkSignal N ρ
  let ε := ρ/Real.sqrt N
  have hs := benchmarkSignal_bounds N ρ (by omega) hr hr1
  let hf1 := MainUpperTheorem.standardFloor_le_one ρ hN hr hr1 hm
  let hg := MainUpperTheorem.grid_nonempty ρ hN hr hr1 hm
  let t := ThresholdGrid.selected (ThresholdGrid.standardFloor N V ρ 1) 1 1 (signal/2) hg
  have ht := ThresholdGrid.standard_selected_spec ρ 1 1 1 (signal/2) (by norm_num) hf1 hg
  let hcomp := ht.2.2.2.1
  have hcolumns : (PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hcomp) : ℝ) ≤
      (16/signal)^(1/ζ)+1 := by
    have hgb : (ThresholdGrid.feasible (UpperRates.benchmarkFloor (Fintype.card V) ε)
        1 1 (signal/2)).Nonempty := by
      simpa only [ThresholdGrid.standardFloor, UpperRates.benchmarkFloor, one_div, ε] using hg
    have hcb : (Fintype.card V : ℝ)⁻¹ <
        ThresholdGrid.selected (UpperRates.benchmarkFloor (Fintype.card V) ε) 1 1 (signal/2) hgb - ε := by
      simpa only [t, ThresholdGrid.standardFloor, UpperRates.benchmarkFloor, one_div, ε] using hcomp
    have hh := UpperRates.benchmark_columns_le M O ranking ζ ε signal (by linarith) hRF
      hs.1 hs.2.1 hm hgb hcb (fun y j ↦ hO.tv_bound hN y j)
    simpa only [t, ThresholdGrid.standardFloor, UpperRates.benchmarkFloor, one_div, ε] using hh
  have hq := UpperRates.queryCount_le_logWeight N D
    (PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hcomp)) η _ c a
    hN hD hη hη1 hc ha hlower hcolumns
  have hqNat : UpperRates.queryCount N D D
      (PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hcomp)) η ≤ queryCap N D ρ ζ c a := by
    have hb := hq.trans (Nat.le_ceil (queryEnvelope N D ρ ζ c a))
    exact_mod_cast hb
  intro blocks
  apply Program.WithinBudgets.withinOracleBudgets
  exact Program.withinBudgets_mono _
    (UpperRates.selected_program_within_queryCount O D t ρ η hN (by omega) hcomp blocks) hqNat le_rfl

/-- The generic-cutoff sampler's robust TV bound and measurable losses
are derived for its actual seed law and complete frozen-oracle class. -/
theorem parameters_robustRisk_le (M : ForestModel N V) (D : ℕ) (ρ η : ℝ)
    (hN : 0 < N) (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hD : 9 ≤ D) (hη : 0 < η)
    (hm : 16 * max (ρ/Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N ρ)
    (hRT : M.TailResponseRegular 1 1) (hUEN : M.EdgeNondegenerate (benchmarkSignal N ρ)) :
    let P := parameters N V D ρ η hN hr hr1 hD hm
    let A := PackedSampler.sampler (Color := Fin (PackedSampler.colorCount D)) P
    let μ := (PackedSampler.seedLaw (Color := Fin (PackedSampler.colorCount D)) P).toMeasure
    A.RiskMeasurable μ M ρ ∧ A.robustRisk μ M ρ ≤ ρ+η := by
  have hs := benchmarkSignal_bounds N ρ (by omega) hr hr1
  have hmargin : 4*(ρ/Real.sqrt N)+benchmarkSignal N ρ/2 < benchmarkSignal N ρ := by
    have hh := le_max_left (ρ/Real.sqrt N) (Fintype.card V : ℝ)⁻¹
    linarith
  exact ThresholdGrid.grid_robustRisk_le M D D ρ η 1 1 1 (benchmarkSignal N ρ/2) (benchmarkSignal N ρ)
    hN hD (by omega) (by norm_num)
    (MainUpperTheorem.standardFloor_le_one ρ hN hr hr1 hm)
    (MainUpperTheorem.grid_nonempty ρ hN hr hr1 hm)
    (div_nonneg hs.1.le (by norm_num)) hη hr.le hr1 hRT hUEN hmargin

/-- The very same generic-cutoff program has its calibrated forward-KL
bound; only the public allocation and row-accuracy predicate differ. -/
theorem parameters_seedKLRisk_le (M : ForestModel N V) (O : FrozenOracle N V) (D : ℕ) (ρ κ η : ℝ)
    (hN : 0 < N) (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hD : 9 ≤ D) (hη : 0 < η)
    (hm : 16 * max (ρ/Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N ρ)
    (hRT : M.TailResponseRegular 1 1) (hUEN : M.EdgeNondegenerate (benchmarkSignal N ρ))
    (hO : O.ForwardKLAccurate M κ) (hκ : κ ≤ ρ^2/N) :
    let P := parameters N V D ρ η hN hr hr1 hD hm
    (PackedSampler.sampler (Color := Fin (PackedSampler.colorCount D)) P).seedKLRisk
      (PackedSampler.seedLaw (Color := Fin (PackedSampler.colorCount D)) P).toMeasure M O ≤
      (N : ℝ)*κ+(N : ℝ)*Real.log (Fintype.card V)*η := by
  have hs := benchmarkSignal_bounds N ρ (by omega) hr hr1
  have hmargin : 4*(ρ/Real.sqrt N)+benchmarkSignal N ρ/2 < benchmarkSignal N ρ := by
    have hh := le_max_left (ρ/Real.sqrt N) (Fintype.card V : ℝ)⁻¹
    linarith
  exact ThresholdGrid.grid_seedKLRisk_le M O D D ρ κ η 1 1 1 (benchmarkSignal N ρ/2) (benchmarkSignal N ρ)
    hN hD (by omega) (by norm_num)
    (MainUpperTheorem.standardFloor_le_one ρ hN hr hr1 hm)
    (MainUpperTheorem.grid_nonempty ρ hN hr hr1 hm)
    (div_nonneg hs.1.le (by norm_num)) hη hr.le hr1 hRT hUEN hmargin hO hκ

/-- The total sequential depth is certified by genuine fixed-input query
groups and includes the distinguished preprocessing stage. -/
theorem parameters_withinOracleDepth (D : ℕ) (ρ η : ℝ)
    (hN : 0 < N) (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hD : 9 ≤ D)
    (hm : 16 * max (ρ/Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N ρ) :
    (PackedSampler.sampler (Color := Fin (PackedSampler.colorCount D))
      (parameters N V D ρ η hN hr hr1 hD hm)).WithinOracleDepth (depthCap N D) :=
  PackedSampler.manuscript_sampler_withinOracleDepth D D _ ρ η hN (by omega) _


/-- Integer query rounding costs at most one additional public query. -/
theorem queryCap_le (N D : ℕ) (ρ ζ c a : ℝ) (ha : 0 ≤ a) :
    (queryCap N D ρ ζ c a : ℝ) ≤ queryEnvelope N D ρ ζ c a + 1 := by
  apply (Nat.ceil_lt_add_one _).le
  have hs : 0 ≤ benchmarkSignal N ρ := by unfold benchmarkSignal; positivity
  have hk := UpperRates.screenConstant_pos
  have hr := UpperRates.repetitionConstant_pos c a ha
  unfold queryEnvelope
  positivity

/-- The actual grouped depth has the same uniform cutoff tradeoff as
commit rounds, including both preprocessing and every screen group. -/
theorem depthCap_le (N D : ℕ) (hN : 0 < N) (hD : 9 ≤ D) (hDN : D ≤ N) :
    (depthCap N D : ℝ) ≤
      (UpperRates.roundConstant + UpperRates.screenConstant + 1) *
        ((N : ℝ)/D) * UpperRates.logWeight N := by
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hratio : 1 ≤ (N : ℝ)/D := (one_le_div hd).mpr (by exact_mod_cast hDN)
  have hw := (UpperRates.logWeight_bounds N hN).1
  have hs := (UpperRates.screenCap_le_envelope N D hN hD).trans
    (UpperRates.screenEnvelope_le_logWeight N hN)
  have hr := UpperRates.hardRoundCap_le_logWeight N D hN hD hDN
  have hp : 1 ≤ ((N : ℝ)/D)*UpperRates.logWeight N := one_le_mul_of_one_le_of_one_le hratio hw
  have hm := mul_le_mul_of_nonneg_right hratio
    (mul_nonneg UpperRates.screenConstant_pos.le (by linarith : 0 ≤ UpperRates.logWeight N))
  unfold depthCap
  push_cast at hs ⊢
  nlinarith

/-- Explicit generic-cutoff query scaling before logarithms are suppressed. -/
theorem queryEnvelope_le_signal_power (N D : ℕ) (ρ ζ c a : ℝ)
    (hN : 0 < N) (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (ha : 0 ≤ a) :
    queryEnvelope N D ρ ζ c a ≤
      (272 * UpperRates.screenConstant * UpperRates.repetitionConstant c a *
        ((16 : ℝ)^(1/ζ)+1)) * (benchmarkSignal N ρ)^(-1/ζ) *
          (D : ℝ)^2 * UpperRates.logWeight N^2 := by
  have hs := benchmarkSignal_bounds N ρ (by omega) hr hr1
  have hb := UpperRates.columnEnvelope_le_signal_power (benchmarkSignal N ρ) ζ hs.1
    (by linarith [hs.2.1]) (by linarith)
  have hk : 0 ≤ 272 * UpperRates.screenConstant * UpperRates.repetitionConstant c a *
      (D : ℝ)^2 * UpperRates.logWeight N^2 := by
    have h1 := UpperRates.screenConstant_pos
    have h2 := UpperRates.repetitionConstant_pos c a ha
    positivity
  have hh := mul_le_mul_of_nonneg_left hb hk
  unfold queryEnvelope
  nlinarith only [hh]

/-- This uniform guarantee fixes the public program before the target,
its ranking, or its frozen oracle is selected. -/
def UniformTVGuarantee (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (D : ℕ) (ρ ζ : ℝ) (P : PackedSampler.Parameters N V) : Prop :=
  let A := PackedSampler.sampler (Color := Fin (PackedSampler.colorCount D)) P
  let μ := (PackedSampler.seedLaw (Color := Fin (PackedSampler.colorCount D)) P).toMeasure
  A.WithinOracleDepth (depthCap N D) ∧
  ∀ (M : ForestModel N V) (ranking : MarginalRanking M),
    FiniteRankFrequency M ranking ζ 1 → M.TailResponseRegular 1 1 →
    M.EdgeNondegenerate (benchmarkSignal N ρ) →
      A.RiskMeasurable μ M ρ ∧ A.robustRisk μ M ρ ≤ 3*ρ/2 ∧
      ∀ (O : FrozenOracle N V), O.Accurate M ρ →
        A.WithinOracleBudgets O (queryCap N D ρ ζ (ρ/2) 0) (ForestIteration.hardRoundCap N D)

theorem finite_uniformTVGuarantee (D : ℕ) (ρ ζ : ℝ)
    (hN : 0 < N) (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (hD : 9 ≤ D)
    (hm : 16 * max (ρ/Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N ρ) :
    UniformTVGuarantee N V D ρ ζ (parameters N V D ρ (ρ/2) hN hr hr1 hD hm) := by
  refine ⟨parameters_withinOracleDepth D ρ (ρ/2) hN hr hr1 hD hm, ?_⟩
  intro M ranking hRF hRT hUEN
  have hh := parameters_robustRisk_le M D ρ (ρ/2) hN hr hr1 hD (by positivity) hm hRT hUEN
  refine ⟨hh.1, hh.2.trans_eq (by ring), ?_⟩
  intro O hO
  exact parameters_withinOracleBudgets M O ranking D ρ ζ (ρ/2) (ρ/2) 0
    hN hr hr1 hζ hD (by positivity) (by linarith) (by positivity) (by norm_num)
    (by simp) hm hRF hO

/-- Literal public vocabulary growth establishes the same finite margin
for every prescribed cutoff, with exactly the appendix's TV allocation. -/
theorem tv_curve_eventually (V : ℕ → Type*)
    [∀ N, Fintype (V N)] [∀ N, DecidableEq (V N)] [∀ N, LinearOrder (V N)] [∀ N, Nonempty (V N)]
    (ρ ζ growth : ℝ) (error : ℕ → ℝ)
    (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (hg : (1/3 : ℝ) < growth)
    (he : Tendsto error atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, (Fintype.card (V N) : ℝ) = (N : ℝ)^(growth+error N)) :
    ∀ᶠ N : ℕ in atTop, ∃ (hN : 0 < N)
      (hm : 16 * max (ρ/Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N ρ),
      ∀ (D : ℕ) (hD : 9 ≤ D), D ≤ N-1 →
        UniformTVGuarantee N (V N) D ρ ζ (parameters N (V N) D ρ (ρ/2) hN hr hr1 hD hm) ∧
        (queryCap N D ρ ζ (ρ/2) 0 : ℝ) ≤ queryEnvelope N D ρ ζ (ρ/2) 0+1 ∧
        (ForestIteration.hardRoundCap N D : ℝ) ≤
          UpperRates.roundConstant*((N : ℝ)/D)*UpperRates.logWeight N ∧
        (depthCap N D : ℝ) ≤ (UpperRates.roundConstant+UpperRates.screenConstant+1)*
          ((N : ℝ)/D)*UpperRates.logWeight N := by
  have hh := UpperFeasibilityGrowth.benchmark_floor_eventually
    (fun N ↦ Fintype.card (V N)) ρ growth error hr hg he hv
  filter_upwards [hh, eventually_ge_atTop (1 : ℕ)] with N hm hN
  have hn : 0 < N := by omega
  have hm' : 16 * max (ρ/Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N ρ := by
    simpa only [one_div] using hm
  refine ⟨hn, hm', ?_⟩
  intro D hD hDN
  exact ⟨finite_uniformTVGuarantee D ρ ζ hn hr hr1 hζ hD hm', queryCap_le N D ρ ζ (ρ/2) 0 (by norm_num),
    UpperRates.hardRoundCap_le_logWeight N D hn hD (by omega), depthCap_le N D hn hD (by omega)⟩


/-- The corresponding forward-KL guarantee uses the same public cutoff
and the exact calibrated inverse-polynomial failure allocation. -/
def UniformKLGuarantee (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
    (D : ℕ) (ρ ζ growth : ℝ) (P : PackedSampler.Parameters N V) : Prop :=
  let A := PackedSampler.sampler (Color := Fin (PackedSampler.colorCount D)) P
  let μ := (PackedSampler.seedLaw (Color := Fin (PackedSampler.colorCount D)) P).toMeasure
  A.WithinOracleDepth (depthCap N D) ∧
  ∀ (M : ForestModel N V) (ranking : MarginalRanking M),
    FiniteRankFrequency M ranking ζ 1 → M.TailResponseRegular 1 1 →
    M.EdgeNondegenerate (benchmarkSignal N ρ) →
    ∀ (O : FrozenOracle N V), O.ForwardKLAccurate M (MainKLUpperTheorem.rowBudget N ρ) →
      A.KLRiskMeasurableAt μ M O ∧ A.seedKLRisk μ M O ≤ 2*ρ^2 ∧
      A.WithinOracleBudgets O
        (queryCap N D ρ ζ (MainKLUpperTheorem.failureCoefficient ρ growth) 2)
        (ForestIteration.hardRoundCap N D)

theorem finite_uniformKLGuarantee (D : ℕ) (ρ ζ growth : ℝ)
    (hN : 0 < N) (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (hg : 0 < growth) (hD : 9 ≤ D)
    (hm : 16 * max (ρ/Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ benchmarkSignal N ρ)
    (hl : 0 < Real.log (Fintype.card V))
    (hη : 0 < MainKLUpperTheorem.failureBudget N (Fintype.card V) ρ)
    (hη1 : MainKLUpperTheorem.failureBudget N (Fintype.card V) ρ ≤ 1)
    (hlower : MainKLUpperTheorem.failureCoefficient ρ growth/(N : ℝ)^(2 : ℝ) ≤
      MainKLUpperTheorem.failureBudget N (Fintype.card V) ρ) :
    UniformKLGuarantee N V D ρ ζ growth
      (parameters N V D ρ (MainKLUpperTheorem.failureBudget N (Fintype.card V) ρ) hN hr hr1 hD hm) := by
  refine ⟨parameters_withinOracleDepth D ρ _ hN hr hr1 hD hm, ?_⟩
  intro M ranking hRF hRT hUEN O hO
  refine ⟨(measurable_of_finite _).aestronglyMeasurable, ?_, ?_⟩
  · exact (parameters_seedKLRisk_le M O D ρ (MainKLUpperTheorem.rowBudget N ρ) _
      hN hr hr1 hD hη hm hRT hUEN hO le_rfl).trans_eq
      (MainKLUpperTheorem.calibrated_error N (Fintype.card V) ρ hN hl)
  · exact parameters_withinOracleBudgets M O ranking D ρ ζ _
      (MainKLUpperTheorem.failureCoefficient ρ growth) 2 hN hr hr1 hζ hD hη hη1
      (by unfold MainKLUpperTheorem.failureCoefficient; positivity) (by norm_num)
      hlower hm hRF (hO.accurate hr.le hr1 le_rfl)

/-- Full public cutoff curve for KL, including the actual seed loss and
all-path query, round, and grouped-depth budgets. -/
theorem kl_curve_eventually (V : ℕ → Type*)
    [∀ N, Fintype (V N)] [∀ N, DecidableEq (V N)] [∀ N, LinearOrder (V N)] [∀ N, Nonempty (V N)]
    (ρ ζ growth : ℝ) (error : ℕ → ℝ)
    (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hζ : 1 < ζ) (hg : (1/3 : ℝ) < growth)
    (he : Tendsto error atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, (Fintype.card (V N) : ℝ) = (N : ℝ)^(growth+error N)) :
    ∀ᶠ N : ℕ in atTop, ∃ (hN : 0 < N)
      (hm : 16 * max (ρ/Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N ρ),
      ∀ (D : ℕ) (hD : 9 ≤ D), D ≤ N-1 →
        UniformKLGuarantee N (V N) D ρ ζ growth
          (parameters N (V N) D ρ (MainKLUpperTheorem.failureBudget N (Fintype.card (V N)) ρ)
            hN hr hr1 hD hm) ∧
        (queryCap N D ρ ζ (MainKLUpperTheorem.failureCoefficient ρ growth) 2 : ℝ) ≤
          queryEnvelope N D ρ ζ (MainKLUpperTheorem.failureCoefficient ρ growth) 2+1 ∧
        (ForestIteration.hardRoundCap N D : ℝ) ≤
          UpperRates.roundConstant*((N : ℝ)/D)*UpperRates.logWeight N ∧
        (depthCap N D : ℝ) ≤ (UpperRates.roundConstant+UpperRates.screenConstant+1)*
          ((N : ℝ)/D)*UpperRates.logWeight N := by
  have hh := UpperFeasibilityGrowth.benchmark_floor_eventually
    (fun N ↦ Fintype.card (V N)) ρ growth error hr hg he hv
  have hf := MainKLUpperTheorem.failureBudget_eventually
    (fun N ↦ Fintype.card (V N)) ρ growth error hr hr1 (by linarith) he hv
  filter_upwards [hh, hf, eventually_ge_atTop (1 : ℕ)] with N hm hfN hN
  have hn : 0 < N := by omega
  have hm' : 16 * max (ρ/Real.sqrt N) (Fintype.card (V N) : ℝ)⁻¹ ≤ benchmarkSignal N ρ := by
    simpa only [one_div] using hm
  refine ⟨hn, hm', ?_⟩
  intro D hD hDN
  exact ⟨finite_uniformKLGuarantee D ρ ζ growth hn hr hr1 hζ (by linarith) hD hm'
    (by linarith [hfN.1]) hfN.2.1 hfN.2.2.1 hfN.2.2.2,
    queryCap_le N D ρ ζ (MainKLUpperTheorem.failureCoefficient ρ growth) 2 (by norm_num),
    UpperRates.hardRoundCap_le_logWeight N D hn hD (by omega), depthCap_le N D hn hD (by omega)⟩

end
end ForestSampling.GeneralUpperCurve
