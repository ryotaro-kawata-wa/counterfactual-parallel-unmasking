import ForestSampling.PathPairSeparation
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false

namespace ForestSampling
namespace PathGraph

/-- The finite path vertices strictly between two distinguished endpoints. -/
def interior {N : ℕ} (i j : Position N) : Finset (Position N) :=
  Finset.univ.filter fun k ↦ (i.val < k.val ∧ k.val < j.val) ∨ (j.val < k.val ∧ k.val < i.val)

@[simp] theorem mem_interior {N : ℕ} (i j k : Position N) : k ∈ interior i j ↔
    (i.val < k.val ∧ k.val < j.val) ∨ (j.val < k.val ∧ k.val < i.val) := by
  simp [interior]

theorem interior_ne_left {N : ℕ} {i j k : Position N} (hk : k ∈ interior i j) : k ≠ i := by
  rw [mem_interior] at hk
  intro hh; subst k; omega

theorem interior_ne_right {N : ℕ} {i j k : Position N} (hk : k ∈ interior i j) : k ≠ j := by
  rw [mem_interior] at hk
  intro hh; subst k; omega

theorem interior_card {N : ℕ} (i j : Position N) :
    (interior i j).card = Nat.dist i.val j.val - 1 := by
  by_cases hij : i.val ≤ j.val
  · have he : interior i j = Finset.Ioo i j := by
      ext k
      simp only [mem_interior, Finset.mem_Ioo, Fin.lt_def]
      omega
    rw [he, Fin.card_Ioo, Nat.dist_eq_sub_of_le hij]
  · have hji : j.val ≤ i.val := by omega
    have he : interior i j = Finset.Ioo j i := by
      ext k
      simp only [mem_interior, Finset.mem_Ioo, Fin.lt_def]
      omega
    rw [he, Fin.card_Ioo, Nat.dist_eq_sub_of_le_right hji]

end PathGraph

namespace PathClass.Parameters
noncomputable section
variable {B : ℕ}

/-- The actual conditional pair information is bounded by one bit times
the event that every possible path separator remains masked. -/
theorem exactPair_mutualInformation_le_interiorMask (P : Parameters B) {n : ℕ}
    (y : MaskedState (n + 1) (Token B)) {i j : Position (n + 1)} (hij : i ≠ j)
    (hi : y i = none) (hj : y j = none) :
    (y.exactPair (P.target (n + 1)) (P.target_positive _) i j).mutualInformation ≤
      if ∀ k ∈ PathGraph.interior i j, y k = none then Real.log 2 else 0 := by
  classical
  by_cases hh : ∀ k ∈ PathGraph.interior i j, y k = none
  · rw [if_pos hh]
    exact P.exactPair_mutualInformation_le_log_two y hij hi hj
  · rw [if_neg hh]
    push Not at hh
    obtain ⟨k, hk, hky⟩ := hh
    rw [P.exactPair_mutualInformation_eq_zero_of_separator y i j k hi hj hky
      ((PathGraph.mem_interior i j k).mp hk)]

end
end PathClass.Parameters
end ForestSampling
