import ForestSampling.CollisionBudget
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace CollisionBudget

/-- Finite Cauchy--Schwarz converts the actual active-batch excess into the
Laplace compensation budget. Empty survivor sets contribute zero. -/
theorem activity_lower_bound {ι : Type*} [Fintype ι]
    (N R : ℕ) (hN : 0 < N) (hR : 0 < R) (hcard : Fintype.card ι ≤ R)
    (n k : ι → ℕ) (hkn : ∀ i, k i ≤ n i) (hnN : ∀ i, n i ≤ N)
    (hexcess : (N : ℝ) / 8 ≤ ∑ i, ((k i - 1 : ℕ) : ℝ)) :
    (N : ℝ) / (64 * (R : ℝ)) ≤
      ∑ i, ((k i - 1 : ℕ) : ℝ)^2 / n i := by
  let x : ι → ℝ := fun i ↦ ((k i - 1 : ℕ) : ℝ)
  let A : ℝ := ∑ i, x i ^ 2 / n i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ ↦ by positivity
  have hpoint : ∀ i, x i ^ 2 ≤ (N : ℝ) * (x i ^ 2 / n i) := by
    intro i
    by_cases hn : n i = 0
    · have hk : k i = 0 := by have := hkn i; omega
      simp [x, hk]
    · have hnpos : (0 : ℝ) < n i := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      apply (mul_le_mul_iff_right₀ hnpos).mp
      have hcast : (n i : ℝ) ≤ N := by exact_mod_cast hnN i
      have hmul := mul_le_mul_of_nonneg_right hcast (sq_nonneg (x i))
      have heq : (n i : ℝ) * ((N : ℝ) * (x i ^ 2 / n i)) = N * x i ^ 2 := by
        field_simp
      rw [heq]
      exact hmul
  have hsum : (∑ i, x i ^ 2) ≤ (N : ℝ) * A := by
    calc
      _ ≤ ∑ i, (N : ℝ) * (x i ^ 2 / n i) := Finset.sum_le_sum fun i _ ↦ hpoint i
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hcauchy : (∑ i, x i)^2 ≤ (Fintype.card ι : ℝ) * ∑ i, x i^2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x))
  have hbudget : (∑ i, x i)^2 ≤ (R : ℝ) * ((N : ℝ) * A) := by
    calc
      _ ≤ (Fintype.card ι : ℝ) * ∑ i, x i^2 := hcauchy
      _ ≤ (R : ℝ) * ((N : ℝ) * A) :=
        mul_le_mul (by exact_mod_cast hcard) hsum
          (Finset.sum_nonneg fun i _ ↦ sq_nonneg _) (by positivity)
  have hx : (N : ℝ)/8 ≤ ∑ i, x i := hexcess
  have hsq : ((N : ℝ)/8)^2 ≤ (∑ i, x i)^2 :=
    pow_le_pow_left₀ (by positivity) hx 2
  have hnpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hrpos : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  change (N : ℝ)/(64*(R : ℝ)) ≤ A
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * (R : ℝ))).2
  have hmul : (N : ℝ) * (N : ℝ) ≤ (N : ℝ) * (A * (64 * (R : ℝ))) := by
    nlinarith [hsq.trans hbudget]
  exact (mul_le_mul_iff_right₀ hnpos).mp hmul

end CollisionBudget
end ForestSampling
