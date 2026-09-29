import ForestSampling.HardMatching

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

/-- A likelihood ratio at most two gives a reverse chi-square/Hellinger
comparison. The constant uses `(sqrt a + sqrt b)^2 <= 2 * (a + b)`. -/
theorem chi_term_le_six_sq_sqrt_sub {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ 2 * b) :
    (a - b) ^ 2 / b ≤ 6 * (Real.sqrt a - Real.sqrt b) ^ 2 := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb.le
  have hbase : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ 6 * b := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]
  have hmul := mul_le_mul_of_nonneg_left hbase
    (sq_nonneg (Real.sqrt a - Real.sqrt b))
  have hid : (Real.sqrt a - Real.sqrt b) ^ 2 *
      (Real.sqrt a + Real.sqrt b) ^ 2 = (a - b) ^ 2 := by
    rw [← mul_pow]
    congr 1
    nlinarith
  rw [hid] at hmul
  apply (div_le_iff₀ hb).mpr
  nlinarith

/-- The lower comparison used for the hard family's one-edge loss. -/
theorem twelfth_chiSquare_le_sqHellinger {α : Type*} [Fintype α]
    (p q : FinDist α) (hq : q.StrictlyPositive)
    (hratio : ∀ x, p x ≤ 2 * q x) :
    chiSquare p q / 12 ≤ sqHellinger p q := by
  have hsum : chiSquare p q ≤
      6 * ∑ x, |Real.sqrt (p x) - Real.sqrt (q x)| ^ 2 := by
    unfold chiSquare
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    rw [sq_abs]
    exact chi_term_le_six_sq_sqrt_sub (p.nonneg x) (hq x) (hratio x)
  rw [sum_sq_sqrt_sub] at hsum
  linarith

end FinDist

namespace HardLocalParameters

variable {bankSize backgroundSize : ℕ}

/-- Every hard-edge likelihood ratio is at most two. -/
theorem interactionFactor_le_two (P : HardLocalParameters bankSize backgroundSize)
    (s t : Fin bankSize) (a b : HardVocabulary bankSize backgroundSize) :
    P.interactionFactor s t a b ≤ 2 := by
  have hθ := P.trigger_pos
  have hθhalf := P.trigger_le_half
  have hcoupling := P.coupling_pos
  have hcoupling_trigger := P.coupling_le_trigger
  have hθone := P.triggerMass_lt_one
  have h1θ : 0 ≤ 1 - P.triggerMass := by linarith
  have hprod : P.feature s a * P.feature t b ≤ (1 - P.triggerMass) ^ 2 := by
    by_cases ha : a = Sum.inl s <;> by_cases hb : b = Sum.inl t
    · simp [ha, hb, P.feature_at_trigger, pow_two]
    · rw [ha, P.feature_at_trigger, P.feature_off_trigger t hb]
      nlinarith
    · rw [P.feature_off_trigger s ha, hb, P.feature_at_trigger]
      nlinarith
    · rw [P.feature_off_trigger s ha, P.feature_off_trigger t hb]
      nlinarith
  have hsq : (1 - P.triggerMass) ^ 2 ≤ 1 - P.triggerMass := by
    nlinarith [sq_nonneg P.triggerMass]
  have hnum : P.edgeCoupling * (P.feature s a * P.feature t b) ≤
      P.triggerVariance := by
    calc
      _ ≤ P.edgeCoupling * (1 - P.triggerMass) ^ 2 :=
        mul_le_mul_of_nonneg_left hprod hcoupling.le
      _ ≤ P.triggerMass * (1 - P.triggerMass) :=
        mul_le_mul hcoupling_trigger hsq (sq_nonneg _) hθ.le
      _ = P.triggerVariance := rfl
  have hquot := (div_le_one P.triggerVariance_pos).mpr hnum
  unfold interactionFactor
  linarith

/-- The Pearson divergence of one hard edge from independent marginals
is exactly the squared coupling, for every pair of private triggers. -/
theorem edgeLaw_chiSquare_independent
    (P : HardLocalParameters bankSize backgroundSize) (s t : Fin bankSize) :
    FinDist.chiSquare (P.edgeLaw s t)
      (P.commonMarginal.prod P.commonMarginal) = P.edgeCoupling ^ 2 := by
  unfold FinDist.chiSquare
  rw [Fintype.sum_prod_type]
  have hv : P.triggerVariance ≠ 0 := ne_of_gt P.triggerVariance_pos
  have hterm : ∀ a b,
      (P.edgeLaw s t (a, b) - (P.commonMarginal.prod P.commonMarginal) (a, b)) ^ 2 /
        (P.commonMarginal.prod P.commonMarginal) (a, b) =
      (P.edgeCoupling ^ 2 / P.triggerVariance ^ 2) *
        ((P.commonMarginal a * P.feature s a ^ 2) *
          (P.commonMarginal b * P.feature t b ^ 2)) := by
    intro a b
    have ha : P.commonMarginal a ≠ 0 := ne_of_gt (P.commonMarginal_strictlyPositive a)
    have hb : P.commonMarginal b ≠ 0 := ne_of_gt (P.commonMarginal_strictlyPositive b)
    rw [P.edgeLaw_apply]
    simp only [FinDist.prod_apply, interactionFactor]
    field_simp
    ring
  simp_rw [hterm]
  simp_rw [← Finset.mul_sum]
  rw [P.weighted_feature_sq_sum]
  simp_rw [← Finset.sum_mul]
  rw [P.weighted_feature_sq_sum]
  field_simp

/-- Exact endpoint response for any two source values. -/
theorem endpointKernel_tv_eq_feature_difference
    (P : HardLocalParameters bankSize backgroundSize) (s t : Fin bankSize)
    (a a' : HardVocabulary bankSize backgroundSize) :
    FinDist.tv (P.endpointKernel s t a) (P.endpointKernel s t a') =
      P.edgeCoupling * |P.feature s a - P.feature s a'| := by
  have hv : P.triggerVariance ≠ 0 := ne_of_gt P.triggerVariance_pos
  have hterm : ∀ b, |P.endpointKernel s t a b - P.endpointKernel s t a' b| =
      (P.edgeCoupling * |P.feature s a - P.feature s a'| / P.triggerVariance) *
        (P.commonMarginal b * |P.feature t b|) := by
    intro b
    have heq : P.endpointKernel s t a b - P.endpointKernel s t a' b =
        (P.edgeCoupling * (P.feature s a - P.feature s a') / P.triggerVariance) *
          (P.commonMarginal b * P.feature t b) := by
      simp only [endpointKernel_apply, interactionFactor]
      ring
    rw [heq, abs_mul, abs_div, abs_mul, abs_mul,
      abs_of_pos P.coupling_pos, abs_of_pos P.triggerVariance_pos,
      abs_of_nonneg (P.commonMarginal.nonneg b)]
  unfold FinDist.tv
  simp_rw [hterm]
  rw [← Finset.mul_sum, P.weighted_abs_feature_sum]
  field_simp

/-- No source pair produces response larger than the edge coupling. -/
theorem endpointKernel_tv_le_coupling
    (P : HardLocalParameters bankSize backgroundSize) (s t : Fin bankSize)
    (a a' : HardVocabulary bankSize backgroundSize) :
    FinDist.tv (P.endpointKernel s t a) (P.endpointKernel s t a') ≤ P.edgeCoupling := by
  rw [P.endpointKernel_tv_eq_feature_difference]
  have hf : |P.feature s a - P.feature s a'| ≤ 1 := by
    by_cases ha : a = Sum.inl s <;> by_cases ha' : a' = Sum.inl s
    · simp [ha, ha']
    · rw [ha, P.feature_at_trigger, P.feature_off_trigger s ha']
      norm_num
    · rw [P.feature_off_trigger s ha, ha', P.feature_at_trigger]
      have heq : -P.triggerMass - (1 - P.triggerMass) = (-1 : ℝ) := by ring
      rw [heq]
      norm_num
    · rw [P.feature_off_trigger s ha, P.feature_off_trigger s ha']
      norm_num
  simpa using mul_le_mul_of_nonneg_left hf P.coupling_pos.le

/-- A trigger/nontrigger source pair attains the maximal endpoint response. -/
theorem endpointKernel_tv_coupling_attained
    (P : HardLocalParameters bankSize backgroundSize) (s t : Fin bankSize) :
    ∃ a a', FinDist.tv (P.endpointKernel s t a) (P.endpointKernel s t a') =
      P.edgeCoupling := by
  refine ⟨Sum.inl s, Sum.inr ⟨0, P.background_nonempty⟩, ?_⟩
  rw [P.endpointKernel_tv_eq_feature_difference, P.feature_at_trigger,
    P.feature_off_trigger s (by simp)]
  norm_num

/-- Any function of the centered trigger feature has the same two-point
expectation, independently of the private trigger label. -/
theorem weighted_feature_function_sum
    (P : HardLocalParameters bankSize backgroundSize) (t : Fin bankSize)
    (f : ℝ → ℝ) :
    (∑ a, P.commonMarginal a * f (P.feature t a)) =
      P.triggerMass * f (1 - P.triggerMass) +
        (1 - P.triggerMass) * f (-P.triggerMass) := by
  have hpoint : ∀ a, P.commonMarginal a * f (P.feature t a) =
      P.commonMarginal a * f (-P.triggerMass) +
      (f (1 - P.triggerMass) - f (-P.triggerMass)) *
        (if a = Sum.inl t then P.commonMarginal a else 0) := by
    intro a
    by_cases ha : a = Sum.inl t
    · subst a
      rw [P.feature_at_trigger, if_pos rfl]
      ring
    · rw [P.feature_off_trigger t ha, if_neg ha]
      ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    P.commonMarginal.sum_mass, Fintype.sum_ite_eq']
  simp only [commonMarginal_apply, commonMass_trigger]
  ring

/-- Closed form of the edge affinity in terms of the two scalar parameters.
Its trigger-independence is needed when multiplying losses over edges. -/
theorem edgeLaw_affinity_formula
    (P : HardLocalParameters bankSize backgroundSize) (s t : Fin bankSize) :
    FinDist.affinity (P.edgeLaw s t) (P.commonMarginal.prod P.commonMarginal) =
      P.triggerMass *
        (P.triggerMass * Real.sqrt (1 + P.edgeCoupling *
          ((1 - P.triggerMass) * (1 - P.triggerMass)) / P.triggerVariance) +
         (1 - P.triggerMass) * Real.sqrt (1 + P.edgeCoupling *
          ((1 - P.triggerMass) * (-P.triggerMass)) / P.triggerVariance)) +
      (1 - P.triggerMass) *
        (P.triggerMass * Real.sqrt (1 + P.edgeCoupling *
          ((-P.triggerMass) * (1 - P.triggerMass)) / P.triggerVariance) +
         (1 - P.triggerMass) * Real.sqrt (1 + P.edgeCoupling *
          ((-P.triggerMass) * (-P.triggerMass)) / P.triggerVariance)) := by
  unfold FinDist.affinity
  rw [Fintype.sum_prod_type]
  have hterm : ∀ a b,
      Real.sqrt (P.edgeLaw s t (a, b) *
        (P.commonMarginal.prod P.commonMarginal) (a, b)) =
      P.commonMarginal a * (P.commonMarginal b *
        Real.sqrt (P.interactionFactor s t a b)) := by
    intro a b
    rw [P.edgeLaw_apply, FinDist.prod_apply]
    have heq : P.commonMarginal a * P.commonMarginal b *
        P.interactionFactor s t a b * (P.commonMarginal a * P.commonMarginal b) =
        (P.commonMarginal a * P.commonMarginal b) ^ 2 *
          P.interactionFactor s t a b := by ring
    rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg (P.commonMarginal.nonneg a) (P.commonMarginal.nonneg b))]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  change (∑ a, P.commonMarginal a *
    (∑ b, P.commonMarginal b * Real.sqrt (1 + P.edgeCoupling *
      (P.feature s a * P.feature t b) / P.triggerVariance))) = _
  have hinner (a : HardVocabulary bankSize backgroundSize) :=
    P.weighted_feature_function_sum t (fun z ↦ Real.sqrt (1 + P.edgeCoupling *
      (P.feature s a * z) / P.triggerVariance))
  simp_rw [hinner]
  exact P.weighted_feature_function_sum s (fun z ↦
    P.triggerMass * Real.sqrt (1 + P.edgeCoupling * (z * (1 - P.triggerMass)) /
      P.triggerVariance) + (1 - P.triggerMass) *
    Real.sqrt (1 + P.edgeCoupling * (z * (-P.triggerMass)) / P.triggerVariance))

/-- The edge Hellinger loss is the same for every pair of private triggers. -/
theorem edgeLaw_sqHellinger_trigger_invariant
    (P : HardLocalParameters bankSize backgroundSize) (s t s' t' : Fin bankSize) :
    FinDist.sqHellinger (P.edgeLaw s t) (P.commonMarginal.prod P.commonMarginal) =
    FinDist.sqHellinger (P.edgeLaw s' t') (P.commonMarginal.prod P.commonMarginal) := by
  unfold FinDist.sqHellinger
  rw [P.edgeLaw_affinity_formula, P.edgeLaw_affinity_formula]

/-- Both finite constants in `app:eq:hard-edge-distance`, with no assumption
about the number of positions or an adaptive sampler. -/
theorem edgeLaw_sqHellinger_bounds
    (P : HardLocalParameters bankSize backgroundSize) (s t : Fin bankSize) :
    P.edgeCoupling ^ 2 / 12 ≤
      FinDist.sqHellinger (P.edgeLaw s t) (P.commonMarginal.prod P.commonMarginal) ∧
    FinDist.sqHellinger (P.edgeLaw s t) (P.commonMarginal.prod P.commonMarginal) ≤
      P.edgeCoupling ^ 2 / 2 := by
  have hpos : (P.commonMarginal.prod P.commonMarginal).StrictlyPositive := by
    intro x
    exact mul_pos (P.commonMarginal_strictlyPositive x.1)
      (P.commonMarginal_strictlyPositive x.2)
  have hratio : ∀ x, P.edgeLaw s t x ≤
      2 * (P.commonMarginal.prod P.commonMarginal) x := by
    rintro ⟨a, b⟩
    rw [P.edgeLaw_apply, FinDist.prod_apply]
    have hm := mul_le_mul_of_nonneg_left (P.interactionFactor_le_two s t a b)
      (mul_nonneg (P.commonMarginal.nonneg a) (P.commonMarginal.nonneg b))
    nlinarith
  constructor
  · simpa only [P.edgeLaw_chiSquare_independent] using
      FinDist.twelfth_chiSquare_le_sqHellinger (P.edgeLaw s t)
        (P.commonMarginal.prod P.commonMarginal) hpos hratio
  · simpa only [P.edgeLaw_chiSquare_independent] using
      FinDist.sqHellinger_le_half_chiSquare (P.edgeLaw s t)
        (P.commonMarginal.prod P.commonMarginal) hpos

end HardLocalParameters
end ForestSampling
