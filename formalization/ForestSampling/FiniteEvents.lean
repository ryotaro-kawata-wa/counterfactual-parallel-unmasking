import ForestSampling.FiniteProbability

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- Event inclusion implies probability monotonicity for finite laws. -/
theorem eventMass_mono (p : FinDist α) (E F : α → Prop)
    [DecidablePred E] [DecidablePred F] (h : ∀ x, E x → F x) :
    p.eventMass E ≤ p.eventMass F := by
  unfold eventMass
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x
  · simp [hx, h x hx]
  · simp only [if_neg hx]
    split <;> simp [p.nonneg]

/-- The union bound needs no independence between events. -/
theorem eventMass_exists_le_sum (p : FinDist α) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] :
    p.eventMass (fun x ↦ ∃ i, E i x) ≤ ∑ i, p.eventMass (E i) := by
  classical
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : ∃ i, E i x
  · obtain ⟨i, hi⟩ := hx
    rw [if_pos ⟨i, hi⟩]
    have hs := Finset.single_le_sum
      (f := fun j : ι ↦ if E j x then p x else 0)
      (fun j _ ↦ by split <;> simp [p.nonneg]) (Finset.mem_univ i)
    simpa only [if_pos hi] using hs
  · rw [if_neg hx]
    exact Finset.sum_nonneg fun i _ ↦ by split <;> simp [p.nonneg]

/-- A common upper bound for each event yields a cardinality union bound. -/
theorem eventMass_exists_le_card_mul (p : FinDist α) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (b : ℝ) (h : ∀ i, p.eventMass (E i) ≤ b) :
    p.eventMass (fun x ↦ ∃ i, E i x) ≤ (Fintype.card ι : ℝ) * b := by
  apply (eventMass_exists_le_sum p E).trans
  calc
    _ ≤ ∑ _i : ι, b := Finset.sum_le_sum fun i _ ↦ h i
    _ = _ := by simp

end FinDist
end ForestSampling
