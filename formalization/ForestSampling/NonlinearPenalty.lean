import ForestSampling.HardMidpoint

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling

/-- A constant-probability collision event forces the corresponding nonlinear
mean penalty. This finite lemma exposes both the tail and pointwise inputs. -/
theorem nonlinear_penalty_of_tail {Ω : Type*} [Fintype Ω]
    (p : FinDist Ω) (penalty count : Ω → ℝ) (c t q : ℝ)
    (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hpenalty : ∀ w, 0 ≤ penalty w)
    (hpoint : ∀ w, 1 - Real.exp (-(c * count w)) ≤ penalty w)
    (htail : q ≤ p.eventMass (fun w ↦ t ≤ count w)) :
    q * (1 - Real.exp (-(c * t))) ≤ ∑ w, p w * penalty w := by
  classical
  have hb : 0 ≤ 1 - Real.exp (-(c * t)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hc ht)))
  have hlocal : ∀ w, (if t ≤ count w then 1 - Real.exp (-(c * t)) else 0) ≤ penalty w := by
    intro w
    by_cases hw : t ≤ count w
    · rw [if_pos hw]
      have he := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hw hc))
      linarith [hpoint w]
    · rw [if_neg hw]
      exact hpenalty w
  calc
    q * (1 - Real.exp (-(c * t))) ≤
        p.eventMass (fun w ↦ t ≤ count w) * (1 - Real.exp (-(c * t))) :=
      mul_le_mul_of_nonneg_right htail hb
    _ = ∑ w, p w * (if t ≤ count w then 1 - Real.exp (-(c * t)) else 0) := by
      unfold FinDist.eventMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w _
      split <;> simp_all
    _ ≤ ∑ w, p w * penalty w := by
      exact Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_left (hlocal w) (p.nonneg w)

namespace NonlinearMatchingParameters

variable {N : ℕ}

/-- The actual joint midpoint penalty is nonnegative on every path. -/
theorem midpointPenalty_nonneg (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (outcome : P.MidpointOutcome A w) : 0 ≤ P.midpointPenalty A w outcome := by
  let := P.vocabularyNonempty
  apply sub_nonneg.mpr
  exact Program.retainedAffinityWeight_le_one _ _ _ _ _

/-- Assemble the current explicit-family minimax bound from two actual
midpoint-process estimates: a local exponential penalty and a collision tail.
Neither estimate is postulated as an axiom, nor is this conditional assembly
claimed to prove the remaining adaptive survivor/collision argument. -/
theorem lowerValue_le_minimax_of_midpoint_estimates
    (P : NonlinearMatchingParameters N) (Q R : ℕ) (hR : 1 ≤ R)
    (count : ∀ A : InstanceFamily.BudgetedSampler P.hardFamily Q R,
      ∀ w : A.1.Seed, P.MidpointOutcome A.1.sampler w → ℕ)
    (hpoint : ∀ A w outcome,
      1 - Real.exp (-(P.edgeCoupling ^ 2 / 12 * (count A w outcome : ℝ))) ≤
        P.midpointPenalty A.1.sampler w outcome)
    (htail : ∀ A w,
      (1 / 4 : ℝ) ≤ (P.midpointJoint A.1.sampler w).eventMass
        (fun outcome ↦ (N : ℝ) / (8192 * (R : ℝ)) ≤ (count A w outcome : ℝ))) :
    P.lowerValue R ≤ InstanceFamily.minimax P.hardFamily Q R := by
  apply P.le_minimax_of_midpoint_penalty Q R hR
  intro A w
  have hh := nonlinear_penalty_of_tail (P.midpointJoint A.1.sampler w)
    (P.midpointPenalty A.1.sampler w) (fun outcome ↦ (count A w outcome : ℝ))
    (P.edgeCoupling ^ 2 / 12) ((N : ℝ) / (8192 * (R : ℝ))) (1 / 4)
    (by positivity) (by positivity) (P.midpointPenalty_nonneg A.1.sampler w)
    (hpoint A w) (htail A w)
  have heq : P.edgeCoupling ^ 2 / 12 * ((N : ℝ) / (8192 * (R : ℝ))) =
      (N : ℝ) * P.edgeCoupling ^ 2 / (98304 * (R : ℝ)) := by ring
  simpa only [lowerValue, heq] using hh

end NonlinearMatchingParameters
end ForestSampling
