import ForestSampling.FiniteMarkovInformation

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Finite entropy is unchanged by a bijective relabeling of outcomes. -/
theorem entropy_map_equiv [DecidableEq β] (p : FinDist α) (e : α ≃ β) :
    entropy (p.map e) = entropy p := by
  unfold entropy
  rw [← e.sum_comp]
  simp only [map_equiv_apply, Equiv.symm_apply_apply]

variable {γ : α → Type*} [∀ a, Fintype (γ a)]

/-- Exact entropy chain rule on a retained finite joint outcome. -/
theorem entropy_sigmaJoint (p : FinDist α) (k : (a : α) → FinDist (γ a))
    (hp : p.StrictlyPositive) (hk : ∀ a, (k a).StrictlyPositive) :
    entropy (sigmaJoint p k) = entropy p + ∑ a, p a * entropy (k a) := by
  unfold entropy
  rw [Fintype.sum_sigma]
  simp only [sigmaJoint_apply, Real.log_mul (hp _).ne' (hk _ _).ne']
  have hsum : (∑ a, ∑ b, p a * k a b * (Real.log (p a) + Real.log (k a b))) =
      (∑ a, p a * Real.log (p a)) + ∑ a, p a * ∑ b, k a b * Real.log (k a b) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    calc
      _ = (∑ b, k a b * (p a * Real.log (p a))) +
          ∑ b, p a * (k a b * Real.log (k a b)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [← Finset.sum_mul, (k a).sum_mass, one_mul]
  rw [hsum, neg_add_rev]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

@[simp] theorem entropy_dirac [DecidableEq α] (a : α) : entropy (dirac a) = 0 := by
  classical
  unfold entropy
  simp [dirac_apply]

end FinDist
end ForestSampling
