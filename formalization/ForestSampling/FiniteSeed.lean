import ForestSampling.FiniteProbability
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

variable {Ω : Type*} [Fintype Ω]

/-- Split an actual finite independent seed vector into its current block
and untouched tail. The continuation can be any function of both pieces. -/
theorem piProduct_expect_cons (p : FinDist Ω) (n : ℕ)
    (f : (Fin (n + 1) → Ω) → ℝ) :
    (∑ x, piProduct (fun _ : Fin (n + 1) ↦ p) x * f x) =
      ∑ a, p a * ∑ tail, piProduct (fun _ : Fin n ↦ p) tail * f (Fin.cons a tail) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Ω)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  simp only [Fin.consEquiv_apply, piProduct_apply, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ]
  change (p a * ∏ i, p (tail i)) * f (Fin.cons a tail) =
    p a * ((∏ i, p (tail i)) * f (Fin.cons a tail))
  ring

end FinDist
end ForestSampling
