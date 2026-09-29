import ForestSampling.FiniteEvents
import ForestSampling.MatchingCombinatorics

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

variable {α Color : Type*} [Fintype α] [Fintype Color] [Nonempty Color]
variable [DecidableEq α] [DecidableEq Color]

/-- Uniform independent colors on every position. -/
noncomputable def uniformColors : FinDist (α → Color) :=
  piProduct fun _ : α ↦ uniform Color

/-- A uniform coordinate agrees with an arbitrary independent readout with
probability exactly the inverse number of colors. -/
theorem uniform_prod_readout_eq {β : Type*} [Fintype β]
    (q : FinDist β) (f : β → Color) :
    ((uniform Color).prod q).eventMass (fun x ↦ x.1 = f x.2) =
      (Fintype.card Color : ℝ)⁻¹ := by
  classical
  unfold eventMass
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [prod_apply, uniform_apply]
  calc
    (∑ b, ∑ a, if a = f b then (Fintype.card Color : ℝ)⁻¹ * q b else 0) =
        ∑ b, (Fintype.card Color : ℝ)⁻¹ * q b := by simp
    _ = _ := by rw [← Finset.mul_sum, q.sum_mass, mul_one]

/-- Two distinct positions in the actual independent uniform coloring agree
with probability exactly the inverse color count. -/
theorem uniformColors_pair_eq (i j : α) (hij : i ≠ j) :
    (uniformColors (α := α) (Color := Color)).eventMass (fun x ↦ x i = x j) =
      (Fintype.card Color : ℝ)⁻¹ := by
  classical
  let split := Equiv.piSplitAt i (fun _ : α ↦ Color)
  have he := (piProduct fun _ : α ↦ uniform Color).map_equiv_eventMass split
    (fun x ↦ x.1 = x.2 ⟨j, hij.symm⟩)
  rw [piProduct_map_piSplitAt] at he
  calc
    _ = ((uniform Color).prod (piProduct fun _ : {k : α // k ≠ i} ↦ uniform Color)).eventMass
        (fun x ↦ x.1 = x.2 ⟨j, hij.symm⟩) := he.symm
    _ = _ := uniform_prod_readout_eq
      (piProduct fun _ : {k : α // k ≠ i} ↦ uniform Color)
      (fun x ↦ x ⟨j, hij.symm⟩)

/-- Any finite collection of forbidden equal-color pairs obeys the simple
union bound. The pair list may contain repetitions. -/
theorem uniformColors_forbidden_pairs_le {ι : Type*} [Fintype ι]
    (left right : ι → α) (hne : ∀ i, left i ≠ right i) :
    (uniformColors (α := α) (Color := Color)).eventMass
      (fun x ↦ ∃ i, x (left i) = x (right i)) ≤
      (Fintype.card ι : ℝ) / Fintype.card Color := by
  classical
  simpa only [div_eq_mul_inv] using
    eventMass_exists_le_card_mul (uniformColors (α := α) (Color := Color))
      (fun i x ↦ x (left i) = x (right i)) (Fintype.card Color : ℝ)⁻¹
      (fun i ↦ le_of_eq (uniformColors_pair_eq (left i) (right i) (hne i)))

end FinDist
end ForestSampling
