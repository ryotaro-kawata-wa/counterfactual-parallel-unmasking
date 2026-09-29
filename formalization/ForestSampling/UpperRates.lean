import ForestSampling.PackedParameters
import ForestSampling.ThresholdGrid
import ForestSampling.LowerAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.UpperRates

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual standard floor in the shared unit-response/unit-frequency
specialization. It depends only on public vocabulary size and row error. -/
def benchmarkFloor (vocabSize : ℕ) (ε : ℝ) : ℝ :=
  4 * max ε (vocabSize : ℝ)⁻¹

/-- The finite benchmark margin supplies a positive grid floor below one
quarter of the signal. -/
theorem benchmarkFloor_bounds (vocabSize : ℕ) (ε signal : ℝ) (hv : 0 < vocabSize)
    (hmargin : 16 * max ε (vocabSize : ℝ)⁻¹ ≤ signal) :
    0 < benchmarkFloor vocabSize ε ∧ benchmarkFloor vocabSize ε ≤ signal / 4 := by
  have hi : 0 < (vocabSize : ℝ)⁻¹ := by positivity
  have hm := le_max_right ε (vocabSize : ℝ)⁻¹
  unfold benchmarkFloor
  constructor <;> linarith

/-- The actual clipped dyadic grid has a feasible point at half-signal tail
allowance; this is a proof about the public finite selection procedure. -/
theorem benchmark_feasible (vocabSize : ℕ) (ε signal : ℝ) (hv : 0 < vocabSize)
    (hsignal : 0 < signal) (hsignal1 : signal ≤ 1 / 2)
    (hmargin : 16 * max ε (vocabSize : ℝ)⁻¹ ≤ signal) :
    (ThresholdGrid.feasible (benchmarkFloor vocabSize ε) 1 1 (signal / 2)).Nonempty := by
  have hf := benchmarkFloor_bounds vocabSize ε signal hv hmargin
  exact ⟨_, ThresholdGrid.unit_response_witness _ _ hf.1 (by positivity)
    (by linarith) (by linarith [hf.2])⟩

/-- Maximal dyadic selection has the exact benchmark bracket, satisfies
the standard bank floor, and preserves a strict signal margin. -/
theorem benchmark_selected_spec (vocabSize : ℕ) (ε signal : ℝ) (hv : 0 < vocabSize)
    (hsignal : 0 < signal) (hsignal1 : signal ≤ 1 / 2)
    (hmargin : 16 * max ε (vocabSize : ℝ)⁻¹ ≤ signal)
    (hf : (ThresholdGrid.feasible (benchmarkFloor vocabSize ε) 1 1 (signal / 2)).Nonempty) :
    let t := ThresholdGrid.selected (benchmarkFloor vocabSize ε) 1 1 (signal / 2) hf
    signal / 4 ≤ t ∧ t ≤ signal / 2 ∧ benchmarkFloor vocabSize ε ≤ t ∧
      4 * ε + signal / 2 ≤ 3 * signal / 4 ∧ 3 * signal / 4 < signal := by
  have hfloor := benchmarkFloor_bounds vocabSize ε signal hv hmargin
  have hs := ThresholdGrid.selected_spec _ 1 1 (signal / 2) hfloor.1 (by linarith [hfloor.2]) hf
  obtain ⟨hf', hlow⟩ := ThresholdGrid.unit_response_selected_ge_half _ (signal / 2) hfloor.1
    (by positivity) (by linarith) (by linarith [hfloor.2])
  have ht : ThresholdGrid.selected (benchmarkFloor vocabSize ε) 1 1 (signal / 2) hf ≤ signal / 2 := by
    have hm : min 1 (ThresholdGrid.selected (benchmarkFloor vocabSize ε) 1 1 (signal / 2) hf) ≤ signal / 2 := by
      simpa only [Real.rpow_one, one_mul] using hs.2.2
    exact (min_le_iff.mp hm).resolve_left (by linarith)
  have he := le_max_left ε (vocabSize : ℝ)⁻¹
  refine ⟨?_, ht, hs.1, ?_, ?_⟩ <;> linarith

/-- A public logarithmic envelope for the exact phase cap, uniform over
all integer cutoffs at least nine. -/
def phaseEnvelope (N : ℕ) : ℝ := 1 + Real.log (2 * (N : ℝ)) / Real.log (9 / 8 : ℝ)

def screenEnvelope (N : ℕ) : ℝ := phaseEnvelope N + 1

def depthEnvelope (N : ℕ) : ℝ := Real.logb 2 (N + 1 : ℕ) + 1

/-- Uniform phase count is derived from the actual numerator, denominator,
and ceiling; no phase-rate assumption is used. -/
theorem phaseCap_le_envelope (N D : ℕ) (hN : 0 < N) (hD : 9 ≤ D) :
    (ForestIteration.phaseCap N D : ℝ) ≤ phaseEnvelope N := by
  have hNp : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hb : 0 < Real.log (9 / 8 : ℝ) := Real.log_pos (by norm_num)
  have hbase : Real.log (9 / 8 : ℝ) ≤ Real.log ((D : ℝ) / 8) := by
    apply Real.log_le_log (by norm_num)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hD) (by norm_num)
  have hden := hb.trans_le hbase
  have hlogN : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
  have hnum : max (Real.log (2 * (N : ℝ) / (D + 1))) 0 ≤ Real.log (2 * (N : ℝ)) := by
    apply max_le _ hlogN
    apply Real.log_le_log (by positivity)
    exact div_le_self (by positivity) (by exact_mod_cast Nat.le_add_left 1 D)
  have hratio : 0 ≤ max (Real.log (2 * (N : ℝ) / (D + 1))) 0 / Real.log ((D : ℝ) / 8) :=
    div_nonneg (le_max_right _ _) hden.le
  have hc := (Nat.ceil_lt_add_one hratio).le
  change (ForestIteration.phaseCap N D : ℝ) ≤ _ at hc
  have hbound : max (Real.log (2 * (N : ℝ) / (D + 1))) 0 / Real.log ((D : ℝ) / 8) ≤
      Real.log (2 * (N : ℝ)) / Real.log (9 / 8 : ℝ) := by
    exact (div_le_div_of_nonneg_right hnum hden.le).trans
      (div_le_div_of_nonneg_left hlogN hb hbase)
  unfold phaseEnvelope
  linarith

/-- At least two units in the screen envelope make its logarithmic
repetition envelope nonnegative for every failure budget at most one. -/
theorem two_le_screenEnvelope (N : ℕ) (hN : 0 < N) : 2 ≤ screenEnvelope N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
  have hb : 0 ≤ Real.log (9 / 8 : ℝ) := Real.log_nonneg (by norm_num)
  unfold screenEnvelope phaseEnvelope
  linarith [div_nonneg hl hb]

/-- The exact number of reached or unreached screen slots obeys the same
uniform logarithmic envelope. -/
theorem screenCap_le_envelope (N D : ℕ) (hN : 0 < N) (hD : 9 ≤ D) :
    (ForestIteration.phaseCap N D + 1 : ℕ) ≤ screenEnvelope N := by
  have h := phaseCap_le_envelope N D hN hD
  unfold screenEnvelope
  push_cast
  linarith

/-- The centroid depth ceiling has its explicit binary-logarithmic bound. -/
theorem centroidDepth_le_envelope (N : ℕ) :
    (ForestIteration.centroidDepth N : ℝ) ≤ depthEnvelope N :=
  (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.le_add_left 1 N))).le

/-- The real logarithmic envelope for the actual repetition allocation. -/
def repetitionEnvelope (N : ℕ) (η : ℝ) : ℝ :=
  8 * Real.log (screenEnvelope N * (N : ℝ) ^ 2 / η) + 1

/-- The number of actual independently sampled colorings is bounded using
the proved screen cap and the actual finite failure budget. -/
theorem repetitions_le_envelope (N D : ℕ) (η : ℝ) (hN : 0 < N) (hD : 9 ≤ D)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    (PackedSampler.coloringRepetitions N D η : ℝ) ≤ repetitionEnvelope N η := by
  have hNp : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hslots : (1 : ℝ) ≤ (ForestIteration.phaseCap N D + 1 : ℕ) := by
    exact_mod_cast Nat.le_add_left 1 (ForestIteration.phaseCap N D)
  have harg : 1 ≤ (ForestIteration.phaseCap N D + 1 : ℕ) * (N : ℝ) ^ 2 / η := by
    apply (le_div_iff₀ hη).mpr
    have hprod : (1 : ℝ) ≤ (ForestIteration.phaseCap N D + 1 : ℕ) * (N : ℝ) ^ 2 := by
      exact one_le_mul_of_one_le_of_one_le hslots (one_le_pow₀ hNp)
    linarith
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 8 * Real.log
    ((ForestIteration.phaseCap N D + 1 : ℕ) * (N : ℝ)^2 / η) by
      exact mul_nonneg (by norm_num) (Real.log_nonneg harg))).le
  change (PackedSampler.coloringRepetitions N D η : ℝ) ≤ _ at hc
  have hlog : Real.log ((ForestIteration.phaseCap N D + 1 : ℕ) * (N : ℝ)^2 / η) ≤
      Real.log (screenEnvelope N * (N : ℝ)^2 / η) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (screenCap_le_envelope N D hN hD) (sq_nonneg _)) hη.le
  unfold repetitionEnvelope
  linarith

/-- Public colors and equal chunk count contribute at most `272*D^2`. -/
theorem color_factor_le (D : ℕ) (hD : 1 ≤ D) :
    PackedSampler.colorCount D * (PackedSampler.colorCount D + D) ≤ 272 * D ^ 2 := by
  have hC : PackedSampler.colorCount D ≤ 16 * D := by unfold PackedSampler.colorCount; omega
  calc
    _ ≤ (16 * D) * (17 * D) := Nat.mul_le_mul hC (by omega)
    _ = _ := by ring

/-- A real envelope for the public round cap after using `D <= N`. -/
def roundEnvelope (N : ℕ) : ℝ := 4 * phaseEnvelope N + depthEnvelope N + 3

/-- The actual hard-round ceiling is bounded directly by its phase and
centroid expressions, including the two reserved rounds. -/
theorem hardRoundCap_le_explicit (N D : ℕ) (hN : 0 < N) (hD : 9 ≤ D) :
    (ForestIteration.hardRoundCap N D : ℝ) ≤
      4 * (N : ℝ) * phaseEnvelope N / D + depthEnvelope N + 3 := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hc := (Nat.ceil_lt_add_one (show 0 ≤
    4 * (N : ℝ) * ForestIteration.phaseCap N D / D by positivity)).le
  have hd := centroidDepth_le_envelope N
  have hp : 4 * (N : ℝ) * ForestIteration.phaseCap N D / D ≤
      4 * (N : ℝ) * phaseEnvelope N / D := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (phaseCap_le_envelope N D hN hD) (by positivity)) hDp.le
  unfold ForestIteration.hardRoundCap
  push_cast
  linarith

/-- In the manuscript's cutoff domain, the entire finite round allowance
has an explicit `(N/D) * O(log N)` bound. -/
theorem hardRoundCap_le_envelope (N D : ℕ) (hN : 0 < N) (hD : 9 ≤ D) (hDN : D ≤ N) :
    (ForestIteration.hardRoundCap N D : ℝ) ≤ (N : ℝ) / D * roundEnvelope N := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hquot : (1 : ℝ) ≤ (N : ℝ) / D := (le_div_iff₀ hDp).mpr (by simpa using (show (D : ℝ) ≤ N by exact_mod_cast hDN))
  have hd : 0 ≤ depthEnvelope N + 3 := by
    have hh := centroidDepth_le_envelope N
    have hn : (0 : ℝ) ≤ ForestIteration.centroidDepth N := by positivity
    linarith
  have hm := mul_le_mul_of_nonneg_right hquot hd
  have hr := hardRoundCap_le_explicit N D hN hD
  unfold roundEnvelope
  calc
    (ForestIteration.hardRoundCap N D : ℝ) ≤
        4 * (N : ℝ) * phaseEnvelope N / D + depthEnvelope N + 3 := hr
    _ ≤ (N : ℝ) / D * (4 * phaseEnvelope N + depthEnvelope N + 3) := by
      nlinarith [show 4 * (N : ℝ) * phaseEnvelope N / D = (N : ℝ) / D * (4 * phaseEnvelope N) by ring]

/-- The exact finite query allowance, with its actual source-column count. -/
def queryCount (N D L columns : ℕ) (η : ℝ) : ℕ :=
  columns * (ForestIteration.phaseCap N D + 1) * PackedSampler.coloringRepetitions N D η *
    PackedSampler.colorCount D * (PackedSampler.colorCount D + L)

/-- Every factor in the actual equal-cutoff/chunk query allowance is
controlled by a proved finite envelope. -/
theorem queryCount_le_envelope (N D columns : ℕ) (η b : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D) (hη : 0 < η) (hη1 : η ≤ 1) (hb : (columns : ℝ) ≤ b) :
    (queryCount N D D columns η : ℝ) ≤
      272 * b * screenEnvelope N * repetitionEnvelope N η * (D : ℝ)^2 := by
  have hs := screenCap_le_envelope N D hN hD
  have ht := repetitions_le_envelope N D η hN hD hη hη1
  have hc : ((PackedSampler.colorCount D * (PackedSampler.colorCount D + D) : ℕ) : ℝ) ≤
      272 * (D : ℝ)^2 := by exact_mod_cast color_factor_le D (by omega)
  have hb0 : 0 ≤ b := (Nat.cast_nonneg columns).trans hb
  have hs0 : 0 ≤ screenEnvelope N := by linarith [two_le_screenEnvelope N hN]
  have ht0 : 0 ≤ repetitionEnvelope N η := (Nat.cast_nonneg _).trans ht
  unfold queryCount
  push_cast at *
  calc
    (columns : ℝ) * (ForestIteration.phaseCap N D + 1) * PackedSampler.coloringRepetitions N D η *
        PackedSampler.colorCount D * (PackedSampler.colorCount D + D) =
      ((columns : ℝ) * (ForestIteration.phaseCap N D + 1) * PackedSampler.coloringRepetitions N D η) *
        (PackedSampler.colorCount D * (PackedSampler.colorCount D + D)) := by ring
    _ ≤ (b * screenEnvelope N * repetitionEnvelope N η) * (272 * (D : ℝ)^2) := by
      apply mul_le_mul _ hc (by positivity) (by positivity)
      exact mul_le_mul (mul_le_mul hb hs (by positivity) hb0) ht (by positivity)
        (mul_nonneg hb0 hs0)
    _ = _ := by ring

/-- The unrounded public cutoff that balances discovery and commit costs. -/
def balancedCutoffReal (N : ℕ) (signal ζ : ℝ) : ℝ :=
  ((N : ℝ) * signal ^ (1 / ζ)) ^ (1 / 3 : ℝ)

def balancedCutoff (N : ℕ) (signal ζ : ℝ) : ℕ := ⌈balancedCutoffReal N signal ζ⌉₊

def balancedScale (N : ℕ) (signal ζ : ℝ) : ℝ :=
  (N : ℝ) ^ (2 / 3 : ℝ) * signal ^ (-1 / (3 * ζ))

/-- Splitting the real power makes the cutoff's two public factors explicit. -/
theorem balancedCutoffReal_eq (N : ℕ) (signal ζ : ℝ) (hs : 0 ≤ signal) :
    balancedCutoffReal N signal ζ =
      (N : ℝ) ^ (1 / 3 : ℝ) * signal ^ (1 / (3 * ζ)) := by
  unfold balancedCutoffReal
  rw [Real.mul_rpow (Nat.cast_nonneg N) (Real.rpow_nonneg hs _), ← Real.rpow_mul hs]
  congr 1
  congr 1
  ring

/-- The two exact unrounded resource expressions have the same real-power
scale, before any asymptotic or ceiling estimate. -/
theorem balancedScale_identities (N : ℕ) (signal ζ : ℝ) (hN : 0 < N) (hs : 0 < signal) :
    (N : ℝ) / balancedCutoffReal N signal ζ = balancedScale N signal ζ ∧
      signal ^ (-1 / ζ) * balancedCutoffReal N signal ζ ^ 2 = balancedScale N signal ζ := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [balancedCutoffReal_eq N signal ζ hs.le]
  constructor
  · unfold balancedScale
    rw [div_mul_eq_div_div]
    have hNpow : (N : ℝ) / (N : ℝ) ^ (1 / 3 : ℝ) = (N : ℝ) ^ (2 / 3 : ℝ) := by
      rw [show (2 / 3 : ℝ) = 1 - 1 / 3 by norm_num, Real.rpow_sub hNp, Real.rpow_one]
    rw [hNpow, div_eq_mul_inv, ← Real.rpow_neg hs.le]
    congr 1
    congr 1
    ring
  · unfold balancedScale
    rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg N), ← Real.rpow_mul_natCast hs.le]
    calc
      signal ^ (-1 / ζ) * ((N : ℝ) ^ ((1 / 3 : ℝ) * 2) * signal ^ ((1 / (3 * ζ)) * 2)) =
          (N : ℝ) ^ (2 / 3 : ℝ) * (signal ^ (-1 / ζ) * signal ^ (2 / (3 * ζ))) := by
        rw [show (1 / 3 : ℝ) * 2 = 2 / 3 by norm_num,
          show (1 / (3 * ζ)) * 2 = 2 / (3 * ζ) by ring]
        ring
      _ = (N : ℝ) ^ (2 / 3 : ℝ) * signal ^ (-1 / (3 * ζ)) := by
        rw [← Real.rpow_add hs]
        congr 1
        congr 1
        ring

/-- Once the unrounded cutoff is at least one, natural-ceiling rounding
changes it by at most a factor two. -/
theorem balancedCutoff_bounds (N : ℕ) (signal ζ : ℝ)
    (hx : 1 ≤ balancedCutoffReal N signal ζ) :
    balancedCutoffReal N signal ζ ≤ (balancedCutoff N signal ζ : ℝ) ∧
      (balancedCutoff N signal ζ : ℝ) ≤ 2 * balancedCutoffReal N signal ζ := by
  constructor
  · exact Nat.le_ceil _
  · have hc := (Nat.ceil_lt_add_one (show 0 ≤ balancedCutoffReal N signal ζ by linarith)).le
    change (balancedCutoff N signal ζ : ℝ) ≤ _ at hc
    linarith

/-- Rounding the cutoff keeps both query and round scales within explicit
constants of the common balanced scale. -/
theorem balanced_resource_scales (N : ℕ) (signal ζ : ℝ) (hN : 0 < N) (hs : 0 < signal)
    (hx : 1 ≤ balancedCutoffReal N signal ζ) :
    (N : ℝ) / balancedCutoff N signal ζ ≤ balancedScale N signal ζ ∧
      signal ^ (-1 / ζ) * (balancedCutoff N signal ζ : ℝ)^2 ≤ 4 * balancedScale N signal ζ := by
  have hb := balancedCutoff_bounds N signal ζ hx
  have hp : 0 < balancedCutoffReal N signal ζ := by linarith
  have hi := balancedScale_identities N signal ζ hN hs
  constructor
  · rw [← hi.1]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) hp hb.1
  · rw [← hi.2]
    have hsq : (balancedCutoff N signal ζ : ℝ)^2 ≤ 4 * balancedCutoffReal N signal ζ ^ 2 := by
      nlinarith [sq_nonneg ((balancedCutoff N signal ζ : ℝ) - 2 * balancedCutoffReal N signal ζ)]
    have hm := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hs.le (-1 / ζ))
    nlinarith

/-- The harmless tail column can be absorbed into the same inverse-signal
power uniformly on signals at most one. -/
theorem columnEnvelope_le_signal_power (signal ζ : ℝ) (hs : 0 < signal) (hs1 : signal ≤ 1)
    (hζ : 0 < ζ) :
    (16 / signal) ^ (1 / ζ) + 1 ≤ ((16 : ℝ) ^ (1 / ζ) + 1) * signal ^ (-1 / ζ) := by
  have he : 0 ≤ 1 / ζ := by positivity
  have hsp : 0 < signal ^ (1 / ζ) := Real.rpow_pos_of_pos hs _
  have hsle : signal ^ (1 / ζ) ≤ 1 := by simpa using Real.rpow_le_rpow hs.le hs1 he
  have hinv : 1 ≤ signal ^ (-1 / ζ) := by
    rw [show -1 / ζ = -(1 / ζ) by ring, Real.rpow_neg hs.le]
    exact (one_le_inv₀ hsp).mpr hsle
  have heq : (16 / signal) ^ (1 / ζ) = (16 : ℝ) ^ (1 / ζ) * signal ^ (-1 / ζ) := by
    rw [Real.div_rpow (by norm_num) hs.le, div_eq_mul_inv,
      show -1 / ζ = -(1 / ζ) by ring, Real.rpow_neg hs.le]
  rw [heq]
  nlinarith


/-- A positive logarithmic weight that also covers the smallest lengths. -/
def logWeight (N : ℕ) : ℝ := 1 + Real.log (N + 1 : ℕ)

def screenConstant : ℝ := 2 + 2 / Real.log (9 / 8 : ℝ)

def roundConstant : ℝ :=
  4 * (1 + 2 / Real.log (9 / 8 : ℝ)) + (1 + 1 / Real.log 2) + 3

/-- This explicit coefficient handles every failure allowance bounded
below by a fixed inverse power, including constant TV allocations. -/
def repetitionConstant (c a : ℝ) : ℝ :=
  8 * (|Real.log (2 * screenConstant)| + |Real.log c| + a + 3) + 1

theorem logWeight_bounds (N : ℕ) (hN : 0 < N) :
    1 ≤ logWeight N ∧ logWeight N ≤ 2 * (N : ℝ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ (N + 1 : ℕ) by exact_mod_cast Nat.le_add_left 1 N)
  have hu := Real.log_le_sub_one_of_pos hp
  unfold logWeight
  push_cast at *
  constructor <;> linarith

theorem log_two_mul_le (N : ℕ) (hN : 0 < N) :
    Real.log (2 * (N : ℝ)) ≤ 2 * Real.log (N + 1 : ℕ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Real.log_le_log (show 0 < 2 * (N : ℝ) by positivity)
    (show 2 * (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ)^2 by push_cast; nlinarith [sq_nonneg (N : ℝ)])
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem phaseEnvelope_le_logWeight (N : ℕ) (hN : 0 < N) :
    phaseEnvelope N ≤ (1 + 2 / Real.log (9 / 8 : ℝ)) * logWeight N := by
  have hb : 0 < Real.log (9 / 8 : ℝ) := Real.log_pos (by norm_num)
  have hl := div_le_div_of_nonneg_right (log_two_mul_le N hN) hb.le
  have hw := (logWeight_bounds N hN).1
  unfold phaseEnvelope logWeight at *
  have hb' : 0 ≤ 2 / Real.log (9 / 8 : ℝ) := by positivity
  nlinarith [show 2 * Real.log (N + 1 : ℕ) / Real.log (9 / 8 : ℝ) =
    (2 / Real.log (9 / 8 : ℝ)) * Real.log (N + 1 : ℕ) by ring]

theorem screenEnvelope_le_logWeight (N : ℕ) (hN : 0 < N) :
    screenEnvelope N ≤ screenConstant * logWeight N := by
  have hp := phaseEnvelope_le_logWeight N hN
  have hw := (logWeight_bounds N hN).1
  unfold screenEnvelope screenConstant
  nlinarith

theorem roundEnvelope_le_logWeight (N : ℕ) (hN : 0 < N) :
    roundEnvelope N ≤ roundConstant * logWeight N := by
  have hp := phaseEnvelope_le_logWeight N hN
  have hw := (logWeight_bounds N hN).1
  have hb : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : depthEnvelope N ≤ (1 + 1 / Real.log 2) * logWeight N := by
    unfold depthEnvelope Real.logb logWeight
    have hb' : 0 ≤ 1 / Real.log 2 := by positivity
    have hl : 0 ≤ Real.log (N + 1 : ℕ) := by unfold logWeight at hw; linarith
    nlinarith [show Real.log (N + 1 : ℕ) / Real.log 2 =
      (1 / Real.log 2) * Real.log (N + 1 : ℕ) by ring]
  unfold roundEnvelope roundConstant
  nlinarith

theorem screenConstant_pos : 0 < screenConstant := by
  have hb : 0 < Real.log (9 / 8 : ℝ) := Real.log_pos (by norm_num)
  unfold screenConstant
  positivity

theorem repetitionConstant_pos (c a : ℝ) (ha : 0 ≤ a) : 0 < repetitionConstant c a := by
  unfold repetitionConstant
  positivity

/-- The actual logarithmic repetition expression has a uniform explicit
logarithmic bound whenever its failure allocation is inverse-polynomial. -/
theorem repetitionEnvelope_le_logWeight (N : ℕ) (η c a : ℝ)
    (hN : 0 < N) (hη : 0 < η) (hc : 0 < c) (ha : 0 ≤ a)
    (hlower : c / (N : ℝ)^a ≤ η) :
    repetitionEnvelope N η ≤ repetitionConstant c a * logWeight N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := two_le_screenEnvelope N hN
  have hsp : 0 < screenEnvelope N := by linarith
  have hkp := screenConstant_pos
  have hw := logWeight_bounds N hN
  have hscreen : screenEnvelope N ≤ 2 * screenConstant * (N : ℝ) := by
    calc
      _ ≤ screenConstant * logWeight N := screenEnvelope_le_logWeight N hN
      _ ≤ screenConstant * (2 * (N : ℝ)) := mul_le_mul_of_nonneg_left hw.2 hkp.le
      _ = _ := by ring
  have hls : Real.log (screenEnvelope N) ≤ Real.log (2 * screenConstant) + Real.log N := by
    have h := Real.log_le_log hsp hscreen
    rwa [Real.log_mul (by positivity) hn.ne'] at h
  have hleta : Real.log c - a * Real.log N ≤ Real.log η := by
    have h := Real.log_le_log (show 0 < c / (N : ℝ)^a by positivity) hlower
    rwa [Real.log_div hc.ne' (Real.rpow_pos_of_pos hn _).ne', Real.log_rpow hn] at h
  have heq : Real.log (screenEnvelope N * (N : ℝ)^2 / η) =
      Real.log (screenEnvelope N) + 2 * Real.log N - Real.log η := by
    rw [Real.log_div (by positivity) hη.ne', Real.log_mul hsp.ne' (by positivity), Real.log_pow]
    norm_num
  have hlog : Real.log (N : ℝ) ≤ logWeight N := by
    have h := Real.log_le_log hn (show (N : ℝ) ≤ (N + 1 : ℕ) by push_cast; linarith)
    unfold logWeight
    linarith
  have hA : 0 ≤ |Real.log (2 * screenConstant)| + |Real.log c| := by positivity
  have ha3 : 0 ≤ a + 3 := by linarith
  have haweight := mul_le_mul_of_nonneg_left hlog ha3
  have hcweight := mul_le_mul_of_nonneg_left hw.1 hA
  have habs1 := le_abs_self (Real.log (2 * screenConstant))
  have habs2 := neg_le_abs (Real.log c)
  unfold repetitionEnvelope repetitionConstant
  rw [heq]
  nlinarith

/-- All exact public round factors are now bounded by an explicit
constant times `(N/D) log(N+1)`. -/
theorem hardRoundCap_le_logWeight (N D : ℕ) (hN : 0 < N) (hD : 9 ≤ D) (hDN : D ≤ N) :
    (ForestIteration.hardRoundCap N D : ℝ) ≤
      roundConstant * ((N : ℝ) / D) * logWeight N := by
  calc
    _ ≤ (N : ℝ) / D * roundEnvelope N := hardRoundCap_le_envelope N D hN hD hDN
    _ ≤ (N : ℝ) / D * (roundConstant * logWeight N) :=
      mul_le_mul_of_nonneg_left (roundEnvelope_le_logWeight N hN) (by positivity)
    _ = _ := by ring

/-- All exact public query factors are now bounded by two logarithms;
the only remaining model factor is the actual proved column bound. -/
theorem queryCount_le_logWeight (N D columns : ℕ) (η b c a : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D) (hη : 0 < η) (hη1 : η ≤ 1)
    (hc : 0 < c) (ha : 0 ≤ a) (hlower : c / (N : ℝ)^a ≤ η)
    (hb : (columns : ℝ) ≤ b) :
    (queryCount N D D columns η : ℝ) ≤
      272 * screenConstant * repetitionConstant c a * b * (D : ℝ)^2 * logWeight N ^ 2 := by
  have hb0 : 0 ≤ b := (Nat.cast_nonneg columns).trans hb
  have hs0 : 0 ≤ screenEnvelope N := by linarith [two_le_screenEnvelope N hN]
  have ht0 : 0 ≤ repetitionEnvelope N η := (Nat.cast_nonneg _).trans
    (repetitions_le_envelope N D η hN hD hη hη1)
  have hst := mul_le_mul (screenEnvelope_le_logWeight N hN)
    (repetitionEnvelope_le_logWeight N η c a hN hη hc ha hlower) ht0
    (mul_nonneg screenConstant_pos.le (by linarith [(logWeight_bounds N hN).1]))
  have hm := mul_le_mul_of_nonneg_left hst (show 0 ≤ 272 * b * (D : ℝ)^2 by positivity)
  have hq := queryCount_le_envelope N D columns η b hN hD hη hη1 hb
  calc
    _ ≤ 272 * b * screenEnvelope N * repetitionEnvelope N η * (D : ℝ)^2 := hq
    _ = (272 * b * (D : ℝ)^2) * (screenEnvelope N * repetitionEnvelope N η) := by ring
    _ ≤ (272 * b * (D : ℝ)^2) *
        ((screenConstant * logWeight N) * (repetitionConstant c a * logWeight N)) := hm
    _ = _ := by ring

/-- At the rounded balancing cutoff, the full column envelope contributes
only the common scale, with an explicit factor four from rounding. -/
theorem balanced_column_scale (N : ℕ) (signal ζ : ℝ) (hN : 0 < N)
    (hs : 0 < signal) (hs1 : signal ≤ 1) (hζ : 0 < ζ)
    (hx : 1 ≤ balancedCutoffReal N signal ζ) :
    ((16 / signal) ^ (1 / ζ) + 1) * (balancedCutoff N signal ζ : ℝ)^2 ≤
      4 * ((16 : ℝ) ^ (1 / ζ) + 1) * balancedScale N signal ζ := by
  have hb := mul_le_mul_of_nonneg_right (columnEnvelope_le_signal_power signal ζ hs hs1 hζ)
    (sq_nonneg (balancedCutoff N signal ζ : ℝ))
  have hs' := mul_le_mul_of_nonneg_left (balanced_resource_scales N signal ζ hN hs hx).2
    (show 0 ≤ (16 : ℝ) ^ (1 / ζ) + 1 by positivity)
  nlinarith

/-- The concrete benchmark signal gives exactly the main upper exponent,
including the separate public accuracy-radius dependence. -/
theorem balancedScale_benchmark (N : ℕ) (radius ζ : ℝ) (hN : 0 < N) (hr : 0 < radius) :
    balancedScale N (benchmarkSignal N radius) ζ =
      (2 : ℝ) ^ (1 / (3 * ζ)) * (N : ℝ) ^ (2 / 3 + 1 / (9 * ζ)) /
        radius ^ (2 / (9 * ζ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold balancedScale
  rw [benchmarkSignal_query_power N radius (3 * ζ) (by omega) hr]
  rw [show 3 * (3 * ζ) = 9 * ζ by ring, Real.div_rpow hn.le (sq_nonneg radius)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  rw [Real.rpow_add hn]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (1 / (9 * ζ)) = 2 / (9 * ζ) by ring]
  ring

/-- The balanced benchmark exponent is strictly sublinear throughout the
paper's rank-frequency range. -/
theorem balanced_exponent_lt_one (ζ : ℝ) (hζ : 1 < ζ) :
    0 < (2 / 3 : ℝ) + 1 / (9 * ζ) ∧ (2 / 3 : ℝ) + 1 / (9 * ζ) < 1 := by
  have hp : 0 < 9 * ζ := by linarith
  have hu : 1 / (9 * ζ) < 1 / 9 := by
    apply (div_lt_iff₀ hp).mpr
    nlinarith
  constructor <;> linarith [one_div_pos.mpr hp]


/-- The rounded balancing cutoff controls the exact public query count
with an explicit squared-logarithmic multiplier. -/
theorem queryCount_le_balanced_logWeight (N columns : ℕ) (signal ζ η c a : ℝ)
    (hN : 0 < N) (hD : 9 ≤ balancedCutoff N signal ζ)
    (hs : 0 < signal) (hs1 : signal ≤ 1) (hζ : 0 < ζ)
    (hx : 1 ≤ balancedCutoffReal N signal ζ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hc : 0 < c) (ha : 0 ≤ a)
    (hlower : c / (N : ℝ)^a ≤ η)
    (hb : (columns : ℝ) ≤ (16 / signal) ^ (1 / ζ) + 1) :
    (queryCount N (balancedCutoff N signal ζ) (balancedCutoff N signal ζ) columns η : ℝ) ≤
      1088 * screenConstant * repetitionConstant c a * ((16 : ℝ) ^ (1 / ζ) + 1) *
        balancedScale N signal ζ * logWeight N ^ 2 := by
  have hq := queryCount_le_logWeight N (balancedCutoff N signal ζ) columns η
    ((16 / signal) ^ (1 / ζ) + 1) c a hN hD hη hη1 hc ha hlower hb
  have hm := mul_le_mul_of_nonneg_left (balanced_column_scale N signal ζ hN hs hs1 hζ hx)
    (show 0 ≤ 272 * screenConstant * repetitionConstant c a * logWeight N ^ 2 by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) screenConstant_pos.le)
        (repetitionConstant_pos c a ha).le) (sq_nonneg _))
  calc
    _ ≤ 272 * screenConstant * repetitionConstant c a * ((16 / signal) ^ (1 / ζ) + 1) *
        (balancedCutoff N signal ζ : ℝ)^2 * logWeight N ^ 2 := hq
    _ = (272 * screenConstant * repetitionConstant c a * logWeight N ^ 2) *
        (((16 / signal) ^ (1 / ζ) + 1) * (balancedCutoff N signal ζ : ℝ)^2) := by ring
    _ ≤ (272 * screenConstant * repetitionConstant c a * logWeight N ^ 2) *
        (4 * ((16 : ℝ) ^ (1 / ζ) + 1) * balancedScale N signal ζ) := hm
    _ = _ := by ring

/-- The same actual cutoff controls the entire hard-round allowance with
one logarithm and the identical balanced scale. -/
theorem hardRoundCap_le_balanced_logWeight (N : ℕ) (signal ζ : ℝ)
    (hN : 0 < N) (hD : 9 ≤ balancedCutoff N signal ζ)
    (hDN : balancedCutoff N signal ζ ≤ N) (hs : 0 < signal)
    (hx : 1 ≤ balancedCutoffReal N signal ζ) :
    (ForestIteration.hardRoundCap N (balancedCutoff N signal ζ) : ℝ) ≤
      roundConstant * balancedScale N signal ζ * logWeight N := by
  have hkp : 0 ≤ roundConstant := by
    have hb : 0 < Real.log (9 / 8 : ℝ) := Real.log_pos (by norm_num)
    have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold roundConstant
    positivity
  have hweight : 0 ≤ roundConstant * logWeight N :=
    mul_nonneg hkp (show 0 ≤ logWeight N by linarith [(logWeight_bounds N hN).1])
  have hm := mul_le_mul_of_nonneg_left (balanced_resource_scales N signal ζ hN hs hx).1 hweight
  have hr := hardRoundCap_le_logWeight N (balancedCutoff N signal ζ) hN hD hDN
  nlinarith [show roundConstant * ((N : ℝ) / balancedCutoff N signal ζ) * logWeight N =
    (roundConstant * logWeight N) * ((N : ℝ) / balancedCutoff N signal ζ) by ring]


/-- Squared logarithmic factors do not change strict sublinearity. This
statement concerns the actual positive logarithmic envelope on naturals. -/
theorem power_logWeight_sq_isLittleO (p : ℝ) (hp : p < 1) :
    (fun N : ℕ ↦ (N : ℝ)^p * logWeight N ^ 2) =o[Filter.atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have hcast : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : (fun N : ℕ ↦ Real.log (N : ℝ)^2) =o[Filter.atTop]
      (fun N : ℕ ↦ (N : ℝ)^(1 - p)) := by
    simpa only [Function.comp_def, Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show 0 < 1 - p by linarith)).comp_tendsto hcast
  have hprod := (Asymptotics.isBigO_refl (fun N : ℕ ↦ (N : ℝ)^p) Filter.atTop).mul_isLittleO hlog
  have hprod' : (fun N : ℕ ↦ (N : ℝ)^p * Real.log (N : ℝ)^2) =o[Filter.atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
    apply hprod.congr' (Filter.Eventually.of_forall (fun _ ↦ rfl))
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← Real.rpow_add hn, show p + (1 - p) = 1 by ring, Real.rpow_one]
  have hweight : (fun N : ℕ ↦ (N : ℝ)^p * logWeight N ^ 2) =O[Filter.atTop]
      (fun N : ℕ ↦ (N : ℝ)^p * Real.log (N : ℝ)^2) := by
    apply Asymptotics.IsBigO.of_bound 9
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ),
      (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1] with N hN hlogN
    change 1 ≤ Real.log (N : ℝ) at hlogN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hl : Real.log (N + 1 : ℕ) ≤ 2 * Real.log (N : ℝ) := by
      have h := Real.log_le_log (show (0 : ℝ) < (N + 1 : ℕ) by positivity)
        (show ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ)^2 by push_cast; nlinarith)
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have hw : 0 ≤ logWeight N := by linarith [(logWeight_bounds N (by omega)).1]
    have hw' : logWeight N ≤ 3 * Real.log (N : ℝ) := by unfold logWeight; linarith
    have hsq : logWeight N ^ 2 ≤ 9 * Real.log (N : ℝ)^2 := by nlinarith
    have hp0 : 0 ≤ (N : ℝ)^p := Real.rpow_nonneg hn.le _
    rw [Real.norm_of_nonneg (mul_nonneg hp0 (sq_nonneg _)),
      Real.norm_of_nonneg (mul_nonneg hp0 (sq_nonneg _))]
    nlinarith [mul_le_mul_of_nonneg_left hsq hp0]
  exact hweight.trans_isLittleO hprod'

/-- The concrete benchmark balanced scale remains sublinear after both
public logarithmic query factors, at every fixed positive accuracy radius. -/
theorem benchmark_balanced_logWeight_sq_isLittleO (radius ζ : ℝ) (hr : 0 < radius) (hζ : 1 < ζ) :
    (fun N : ℕ ↦ balancedScale N (benchmarkSignal N radius) ζ * logWeight N ^ 2)
      =o[Filter.atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have h := (power_logWeight_sq_isLittleO ((2 / 3 : ℝ) + 1 / (9 * ζ))
    (balanced_exponent_lt_one ζ hζ).2).const_mul_left
      ((2 : ℝ) ^ (1 / (3 * ζ)) / radius ^ (2 / (9 * ζ)))
  apply h.congr' _ (Filter.Eventually.of_forall (fun _ ↦ rfl))
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
  rw [balancedScale_benchmark N radius ζ (by omega) hr]
  ring

section Banks

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]

/-- The true RF certificate bounds the actual public screen columns. The
threshold and its floor witness may be any concrete feasible selection. -/
theorem columns_le_rank_bound (M : ForestModel N V) (O : FrozenOracle N V)
    (ranking : MarginalRanking M) (ζ t ε : ℝ) (hζ : 0 < ζ)
    (hRF : FiniteRankFrequency M ranking ζ 1)
    (hfloor : benchmarkFloor (Fintype.card V) ε ≤ t)
    (hcomplement : (Fintype.card V : ℝ)⁻¹ < t - ε)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε) :
    (PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hcomplement) : ℝ) ≤
      (4 / t) ^ (1 / ζ) + 1 := by
  have hf : 4 * max ε (1 / (Fintype.card V : ℝ)) ≤ t := by simpa [benchmarkFloor, one_div] using hfloor
  have hb := Screening.bankMax_le_rank_bound M O ranking ζ 1 t ε hζ (by norm_num) hRF hf hrows
  have hc : PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hcomplement) ≤
      ⌊(4 / t) ^ (1 / ζ)⌋₊ + 1 := by
    unfold PackedSampler.screenColumns
    split
    · omega
    · simpa only [mul_one] using Nat.add_le_add_right hb 1
  have hp : 0 ≤ (4 / t) ^ (1 / ζ) := Real.rpow_nonneg (by
    have ht : 0 < t := (show 0 < benchmarkFloor (Fintype.card V) ε by
      unfold benchmarkFloor; have hv : 0 < (Fintype.card V : ℝ)⁻¹ := by positivity
      linarith [le_max_right ε (Fintype.card V : ℝ)⁻¹]).trans_le hfloor
    positivity) _
  have hfloorR := Nat.floor_le hp
  have hcast : (PackedSampler.screenColumns (Screening.Banks.ofOracle O t ε hcomplement) : ℝ) ≤
      (⌊(4 / t) ^ (1 / ζ)⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  linarith

/-- Applying the proven RF bound at the actual dyadically selected
threshold yields the exact finite benchmark source-column envelope. -/
theorem benchmark_columns_le (M : ForestModel N V) (O : FrozenOracle N V)
    (ranking : MarginalRanking M) (ζ ε signal : ℝ) (hζ : 0 < ζ)
    (hRF : FiniteRankFrequency M ranking ζ 1)
    (hsignal : 0 < signal) (hsignal1 : signal ≤ 1 / 2)
    (hmargin : 16 * max ε (Fintype.card V : ℝ)⁻¹ ≤ signal)
    (hf : (ThresholdGrid.feasible (benchmarkFloor (Fintype.card V) ε) 1 1 (signal / 2)).Nonempty)
    (hcomplement : (Fintype.card V : ℝ)⁻¹ <
      ThresholdGrid.selected (benchmarkFloor (Fintype.card V) ε) 1 1 (signal / 2) hf - ε)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε) :
    (PackedSampler.screenColumns (Screening.Banks.ofOracle O
      (ThresholdGrid.selected (benchmarkFloor (Fintype.card V) ε) 1 1 (signal / 2) hf)
      ε hcomplement) : ℝ) ≤ (16 / signal) ^ (1 / ζ) + 1 := by
  let t := ThresholdGrid.selected (benchmarkFloor (Fintype.card V) ε) 1 1 (signal / 2) hf
  have hs := benchmark_selected_spec (Fintype.card V) ε signal Fintype.card_pos
    hsignal hsignal1 hmargin hf
  have ht : 0 < t := (by positivity : 0 < signal / 4).trans_le hs.1
  have hc := columns_le_rank_bound M O ranking ζ t ε hζ hRF hs.2.2.1 hcomplement hrows
  have hbase : 4 / t ≤ 16 / signal := by
    apply (div_le_div_iff₀ ht hsignal).mpr
    linarith [hs.1]
  have hp : (4 / t) ^ (1 / ζ) ≤ (16 / signal) ^ (1 / ζ) :=
    Real.rpow_le_rpow (by positivity) hbase (by positivity : 0 ≤ 1 / ζ)
  linarith

/-- The exact finite query allowance of the selected-threshold program is
bounded with all column, phase, repetition, and coloring factors eliminated. -/
theorem benchmark_queryCount_le (M : ForestModel N V) (O : FrozenOracle N V)
    (ranking : MarginalRanking M) (ζ ε signal η : ℝ) (D : ℕ)
    (hN : 0 < N) (hD : 9 ≤ D) (hζ : 0 < ζ)
    (hRF : FiniteRankFrequency M ranking ζ 1)
    (hsignal : 0 < signal) (hsignal1 : signal ≤ 1 / 2)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hmargin : 16 * max ε (Fintype.card V : ℝ)⁻¹ ≤ signal)
    (hf : (ThresholdGrid.feasible (benchmarkFloor (Fintype.card V) ε) 1 1 (signal / 2)).Nonempty)
    (hcomplement : (Fintype.card V : ℝ)⁻¹ <
      ThresholdGrid.selected (benchmarkFloor (Fintype.card V) ε) 1 1 (signal / 2) hf - ε)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε) :
    (queryCount N D D (PackedSampler.screenColumns (Screening.Banks.ofOracle O
      (ThresholdGrid.selected (benchmarkFloor (Fintype.card V) ε) 1 1 (signal / 2) hf)
      ε hcomplement)) η : ℝ) ≤
      272 * ((16 / signal) ^ (1 / ζ) + 1) * screenEnvelope N * repetitionEnvelope N η * (D : ℝ)^2 :=
  queryCount_le_envelope N D _ η _ hN hD hη hη1
    (benchmark_columns_le M O ranking ζ ε signal hζ hRF hsignal hsignal1 hmargin hf hcomplement hrows)

/-- These real inequalities apply to the concrete original program's
all-path resource allowance, using its actual all-mask preprocessing reply. -/
theorem selected_program_within_queryCount (O : FrozenOracle N V) (D : ℕ)
    (t ρ η : ℝ) (hN : 0 < N) (hD : 0 < D)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N)
    (blocks : PackedSampler.ColorBlocks (N := N) (Color := Fin (PackedSampler.colorCount D))
      (ForestIteration.phaseCap N D + 1) (PackedSampler.coloringRepetitions N D η)) :
    Program.WithinBudgets
      ((PackedSampler.sampler (Color := Fin (PackedSampler.colorCount D))
        (PackedSampler.manuscriptParameters N V D D t ρ η hN hD hfloor)).program blocks
          (O.readState (MaskedState.allMask N V)))
      (queryCount N D D (PackedSampler.screenColumns
        (Screening.Banks.ofOracle O t (ρ / Real.sqrt N) hfloor)) η)
      (ForestIteration.hardRoundCap N D) := by
  simpa only [queryCount, PackedSampler.initialBanks_oracle] using
    PackedSampler.manuscript_program_withinBudgets D D t ρ η hN hD hfloor blocks
      (O.readState (MaskedState.allMask N V))

end Banks
end
end ForestSampling.UpperRates
