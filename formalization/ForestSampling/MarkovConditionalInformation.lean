import ForestSampling.MarkovEntropy

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FiniteMarkovChain

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

noncomputable section

/-- Conditional adjacent-pair information written as the reference
expectation of actual row KL against the two-step transition. -/
def transitionConditionalInformation (π : FinDist V) (K : V → FinDist V) : ℝ :=
  ∑ a, π a * ∑ b, K a b * FinDist.klDivergence (K b) (twoStep K a)

omit [DecidableEq V] [Nonempty V] in
theorem meanKernelKL_eq_entropy_sub (π : FinDist V) (K : V → FinDist V)
    (hπ : π.StrictlyPositive) (hK : ∀ a, (K a).StrictlyPositive)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) :
    (∑ a, π a * FinDist.klDivergence (K a) π) =
      FinDist.entropy π - meanTransitionEntropy π K := by
  simp_rw [FinDist.klDivergence_eq_neg_entropy_sub _ π (hK _) hπ, mul_sub, mul_neg]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, stationary_sum π K hstationary]
  unfold meanTransitionEntropy FinDist.entropy
  ring

theorem transitionKL_eq_entropy_sub (K : V → FinDist V)
    (hK : ∀ a, (K a).StrictlyPositive) (a : V) :
    (∑ b, K a b * FinDist.klDivergence (K b) (twoStep K a)) =
      FinDist.entropy (twoStep K a) - ∑ b, K a b * FinDist.entropy (K b) := by
  simp_rw [FinDist.klDivergence_eq_neg_entropy_sub _ _ (hK _) (twoStep_positive K hK a),
    mul_sub, mul_neg]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hcross : (∑ b, K a b * ∑ c, K b c * Real.log (twoStep K a c)) =
      ∑ c, twoStep K a c * Real.log (twoStep K a c) := by
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, twoStep, FinDist.bind_apply]
  rw [hcross]
  unfold FinDist.entropy
  ring

/-- The second coefficient in the DTC identity is the actual conditional
information, and is therefore nonnegative without an entropy comparison
being assumed as a premise. -/
theorem transitionConditionalInformation_eq (π : FinDist V) (K : V → FinDist V)
    (hK : ∀ a, (K a).StrictlyPositive)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) :
    transitionConditionalInformation π K =
      meanTransitionEntropy π (twoStep K) - meanTransitionEntropy π K := by
  unfold transitionConditionalInformation
  simp_rw [transitionKL_eq_entropy_sub K hK, mul_sub]
  rw [Finset.sum_sub_distrib, stationary_sum π K hstationary]
  rfl

theorem transitionConditionalInformation_nonneg (π : FinDist V) (K : V → FinDist V)
    (hK : ∀ a, (K a).StrictlyPositive) : 0 ≤ transitionConditionalInformation π K := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg (π.nonneg a)
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg ((K a).nonneg b)
    (FinDist.klDivergence_nonneg _ _ (hK b) (twoStep_positive K hK a))

/-- Distinct transition rows force strictly positive conditional
information because every previous and next state has positive mass. -/
theorem transitionConditionalInformation_pos (π : FinDist V) (K : V → FinDist V)
    (hπ : π.StrictlyPositive) (hK : ∀ a, (K a).StrictlyPositive)
    (u v : V) (hne : K u ≠ K v) : 0 < transitionConditionalInformation π K := by
  have hex : ∃ b, K b ≠ twoStep K u := by
    by_cases hu : K u = twoStep K u
    · exact ⟨v, fun hv ↦ hne (hu.trans hv.symm)⟩
    · exact ⟨u, hu⟩
  obtain ⟨b, hb⟩ := hex
  apply Finset.sum_pos'
  · intro a _
    apply mul_nonneg (π.nonneg a)
    apply Finset.sum_nonneg
    intro c _
    exact mul_nonneg ((K a).nonneg c)
      (FinDist.klDivergence_nonneg _ _ (hK c) (twoStep_positive K hK a))
  · refine ⟨u, Finset.mem_univ _, mul_pos (hπ u) ?_⟩
    apply Finset.sum_pos'
    · intro c _
      exact mul_nonneg ((K u).nonneg c)
        (FinDist.klDivergence_nonneg _ _ (hK c) (twoStep_positive K hK u))
    · exact ⟨b, Finset.mem_univ _, mul_pos (hK u b)
        (FinDist.klDivergence_pos_of_ne _ _ (hK b) (twoStep_positive K hK u) hb)⟩

end
end FiniteMarkovChain
end ForestSampling
