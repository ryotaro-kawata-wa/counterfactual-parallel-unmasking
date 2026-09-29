import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
open MeasureTheory Set Filter

namespace ForestSampling.EffectiveTCIntegral
noncomputable section

/-- The effective-TC functional of an actual masked pair-information curve.
The input curve is kept explicit so that its probabilistic origin can be
proved independently without assuming an external comparison inequality. -/
def effectiveTCOf (G : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), min 1 t * G t

/-- An exponential upper envelope ensures the effective-information
integrand is integrable on the positive half-line. -/
theorem integrable_weighted {G : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hm : AEStronglyMeasurable G (volume.restrict (Ioi (0 : ℝ))))
    (h0 : ∀ t : ℝ, 0 < t → 0 ≤ G t)
    (hu : ∀ t : ℝ, 0 < t → G t ≤ A * Real.exp (-t)) :
    IntegrableOn (fun t ↦ min 1 t * G t) (Ioi (0 : ℝ)) := by
  have he := (integrableOn_exp_neg_Ioi 0).const_mul A
  apply he.mono_nonneg
    (((continuous_const.min continuous_id).aestronglyMeasurable).mul hm)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (le_min (by norm_num) ht.le) (h0 t ht)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (mul_le_of_le_one_left (h0 t ht) (min_le_left 1 t)).trans (hu t ht)

/-- The integral upper bound follows directly from exp(-t), whose
positive-half-line integral is one. -/
theorem effectiveTCOf_le {G : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hm : AEStronglyMeasurable G (volume.restrict (Ioi (0 : ℝ))))
    (h0 : ∀ t : ℝ, 0 < t → 0 ≤ G t)
    (hu : ∀ t : ℝ, 0 < t → G t ≤ A * Real.exp (-t)) :
    effectiveTCOf G ≤ A := by
  have hh := setIntegral_mono_on (integrable_weighted hA hm h0 hu)
    ((integrableOn_exp_neg_Ioi 0).const_mul A) measurableSet_Ioi
    (fun t ht ↦ (mul_le_of_le_one_left (h0 t ht) (min_le_left 1 t)).trans (hu t ht))
  simpa only [effectiveTCOf, integral_const_mul, integral_exp_neg_Ioi_zero, mul_one] using hh

/-- Retaining only t in [1/2,1] gives a strictly positive universal
integral constant. No improper-integral identity is used for the lower bound. -/
theorem effectiveTCOf_ge {G : ℝ → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hm : AEStronglyMeasurable G (volume.restrict (Ioi (0 : ℝ))))
    (h0 : ∀ t : ℝ, 0 < t → 0 ≤ G t)
    (hu : ∀ t : ℝ, 0 < t → G t ≤ A * Real.exp (-t))
    (hl : ∀ t : ℝ, 0 < t → B * Real.exp (-4*t) ≤ G t) :
    B * Real.exp (-4) / 4 ≤ effectiveTCOf G := by
  have hi := integrable_weighted hA hm h0 hu
  have hsub : Icc (1/2 : ℝ) 1 ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le (by norm_num) ht.1
  have hrestrict := setIntegral_mono_set hi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (le_min (by norm_num) ht.le) (h0 t ht))
    (Filter.Eventually.of_forall hsub)
  have hconst : IntegrableOn (fun _ : ℝ ↦ B * Real.exp (-4) / 2) (Icc (1/2 : ℝ) 1) :=
    integrableOn_const (by simp)
  have hpart := setIntegral_mono_on hconst (hi.mono_set hsub) measurableSet_Icc
    (fun t ht ↦ by
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
      have hweight : (1/2 : ℝ) ≤ min 1 t := le_min (by norm_num) ht.1
      have he : Real.exp (-4) ≤ Real.exp (-4*t) := Real.exp_le_exp.mpr (by linarith [ht.2])
      have hbg := (mul_le_mul_of_nonneg_left he hB).trans (hl t ht0)
      have hh := mul_le_mul hweight hbg (mul_nonneg hB (Real.exp_pos _).le)
        (le_min (by norm_num) ht0.le)
      nlinarith only [hh])
  have hleft : (∫ t in Icc (1/2 : ℝ) 1, B * Real.exp (-4) / 2) = B * Real.exp (-4) / 4 := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num)]
    norm_num
    ring
  rw [hleft] at hpart
  exact hpart.trans hrestrict

/-- The lower coefficient supplied by any positive pair-dependence
constant remains strictly positive after integration. -/
theorem lower_constant_pos {B : ℝ} (hB : 0 < B) : 0 < B * Real.exp (-4) / 4 := by
  positivity

end
end ForestSampling.EffectiveTCIntegral
