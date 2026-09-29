import ForestSampling.RankedBanks
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

namespace ForestSampling.ThresholdGrid

/-- The public clipped dyadic grid uses exactly the manuscript's ceiling. -/
noncomputable def depth (floor : ℝ) : ℕ := ⌈Real.logb 2 (1 / floor)⌉₊

noncomputable def dyadic (m : ℕ) : ℝ := ((2 : ℝ) ^ m)⁻¹

noncomputable def grid (floor : ℝ) : Finset ℝ := by
  classical
  exact (Finset.range (depth floor + 1)).image (fun m ↦ max floor (dyadic m))

/-- Feasibility depends only on public response parameters and tolerances,
so the selected threshold is fixed before any oracle submission. -/
noncomputable def feasible (floor response exponent tolerance : ℝ) : Finset ℝ := by
  classical
  exact (grid floor).filter (fun t ↦ min 1 (response * t ^ exponent) ≤ tolerance)

noncomputable def selected (floor response exponent tolerance : ℝ)
    (h : (feasible floor response exponent tolerance).Nonempty) : ℝ :=
  (feasible floor response exponent tolerance).max' h

/-- Explicit dyadic rounding loses at most a factor two. -/
theorem dyadic_depth_bounds (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    a / 2 ≤ dyadic (depth a) ∧ dyadic (depth a) ≤ a := by
  have hinv : 0 < 1 / a := by positivity
  have hge : 1 ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha1)
  have hlog : 0 ≤ Real.logb 2 (1 / a) := Real.logb_nonneg (by norm_num) hge
  have hceil : (depth a : ℝ) ≤ Real.logb 2 (1 / a) + 1 :=
    (Nat.ceil_lt_add_one hlog).le
  have hlower : 1 / a ≤ (2 : ℝ) ^ depth a := by
    rw [← Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow (by norm_num) hinv).mp (Nat.le_ceil _)
  have hupper : (2 : ℝ) ^ depth a ≤ 2 / a := by
    rw [← Real.rpow_natCast]
    calc
      _ ≤ (2 : ℝ) ^ (Real.logb 2 (1 / a) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
      _ = 2 / a := by
        rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hinv]
        norm_num
        ring
  have hp : 0 < (2 : ℝ) ^ depth a := by positivity
  unfold dyadic
  constructor
  · rw [inv_eq_one_div, le_div_iff₀ hp]
    have hh := (le_div_iff₀ ha).mp hupper
    nlinarith
  · rw [inv_eq_one_div, div_le_iff₀ hp]
    have hh := (div_le_iff₀ ha).mp hlower
    nlinarith

theorem mem_grid_bounds (floor t : ℝ) (hf : 0 < floor) (hf1 : floor ≤ 1)
    (ht : t ∈ grid floor) : floor ≤ t ∧ t ≤ 1 := by
  classical
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp ht
  refine ⟨le_max_left _ _, max_le hf1 ?_⟩
  unfold dyadic
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- Clipping includes the exact floor, not merely a nearby dyadic number. -/
theorem floor_mem_grid (floor : ℝ) (hf : 0 < floor) (hf1 : floor ≤ 1) :
    floor ∈ grid floor := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨depth floor, Finset.mem_range.mpr (by omega), ?_⟩
  exact max_eq_left (dyadic_depth_bounds floor hf hf1).2

/-- Maximal feasible selection supplies the public lower/upper bounds and
response certificate used by the concrete screening construction. -/
theorem selected_spec (floor response exponent tolerance : ℝ)
    (hf : 0 < floor) (hf1 : floor ≤ 1)
    (h : (feasible floor response exponent tolerance).Nonempty) :
    floor ≤ selected floor response exponent tolerance h ∧
    selected floor response exponent tolerance h ≤ 1 ∧
    min 1 (response * (selected floor response exponent tolerance h) ^ exponent) ≤ tolerance := by
  have hm := Finset.max'_mem (feasible floor response exponent tolerance) h
  have hp := Finset.mem_filter.mp hm
  have hg := mem_grid_bounds floor _ hf hf1 hp.1
  exact ⟨hg.1, hg.2, hp.2⟩

/-- Every feasible candidate is bounded above by the actually selected
maximum; no continuous threshold optimization replaces the finite grid. -/
theorem le_selected (floor response exponent tolerance t : ℝ)
    (h : (feasible floor response exponent tolerance).Nonempty)
    (ht : t ∈ feasible floor response exponent tolerance) :
    t ≤ selected floor response exponent tolerance h :=
  Finset.le_max' _ _ ht

/-- In the unit response regime, the dyadic tolerance witness belongs to
the actual clipped grid and is feasible whenever floor≤tolerance/2. -/
theorem unit_response_witness (floor tolerance : ℝ) (hf : 0 < floor)
    (ht : 0 < tolerance) (ht1 : tolerance ≤ 1) (hfloor : floor ≤ tolerance / 2) :
    dyadic (depth tolerance) ∈ feasible floor 1 1 tolerance := by
  classical
  have hd := dyadic_depth_bounds tolerance ht ht1
  have hft : floor ≤ tolerance := by linarith
  have hdep : depth tolerance ≤ depth floor := by
    apply Nat.ceil_le_ceil
    apply (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mpr
    exact one_div_le_one_div_of_le hf hft
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_image.mpr
    refine ⟨depth tolerance, Finset.mem_range.mpr (by omega), ?_⟩
    exact max_eq_right (hfloor.trans hd.1)
  · simpa only [Real.rpow_one, one_mul] using (min_le_right (1 : ℝ) _).trans hd.2

/-- This finite quantitative lower bound on the chosen threshold is the
concrete dyadic step needed by the manuscript's asymptotic bank estimate. -/
theorem unit_response_selected_ge_half (floor tolerance : ℝ) (hf : 0 < floor)
    (ht : 0 < tolerance) (ht1 : tolerance ≤ 1) (hfloor : floor ≤ tolerance / 2) :
    ∃ h : (feasible floor 1 1 tolerance).Nonempty,
      tolerance / 2 ≤ selected floor 1 1 tolerance h := by
  have hm := unit_response_witness floor tolerance hf ht ht1 hfloor
  let h : (feasible floor 1 1 tolerance).Nonempty := ⟨_, hm⟩
  exact ⟨h, (dyadic_depth_bounds tolerance ht ht1).1.trans
    (le_selected floor 1 1 tolerance _ h hm)⟩

end ForestSampling.ThresholdGrid
