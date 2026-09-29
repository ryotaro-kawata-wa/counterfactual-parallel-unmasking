import ForestSampling.ColorProbability
import ForestSampling.ScreenProbability
import ForestSampling.ScreeningProbes

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace Screening

noncomputable section
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {V Color : Type*} [Fintype V] [DecidableEq V]
variable [Fintype Color] [Nonempty Color] [DecidableEq Color]

/-- Residual neighbors of a readout, as a finite index type for the color
union bound. This is an analysis-only object depending on the hidden graph. -/
abbrev ResidualNeighbors (M : ForestModel N V) (h : History N V)
    (j : ResidualVertex h) := {v : ResidualVertex h // M.graph.Adj j.val v.val}

/-- The forbidden-pair union bound for a fixed history and pair. These inputs
are fixed before drawing the current independent coloring. -/
theorem separating_failure_le (M : ForestModel N V) (h : History N V)
    (i j : ResidualVertex h) :
    (FinDist.uniformColors (α := Position N) (Color := Color)).eventMass
      (fun color ↦ ¬ Separating M h color i j) ≤
      (2 * Fintype.card (ResidualNeighbors M h j) : ℝ) / Fintype.card Color := by
  classical
  let Neigh := ResidualNeighbors M h j
  let Other := {v : Neigh // v.val.val ≠ i.val}
  let left : Neigh ⊕ Other → Position N := Sum.elim (fun v ↦ v.val.val) (fun v ↦ v.val.val.val)
  let right : Neigh ⊕ Other → Position N := Sum.elim (fun _ ↦ j.val) (fun _ ↦ i.val)
  have hne : ∀ k, left k ≠ right k := by
    intro k
    cases k with
    | inl v =>
        change v.val.val ≠ j.val
        exact (M.graph.ne_of_adj v.property).symm
    | inr v => exact v.property
  have hsub : ∀ color : Position N → Color, ¬ Separating M h color i j →
      ∃ k, color (left k) = color (right k) := by
    intro color hbad
    by_contra hnone
    apply hbad
    constructor
    · intro v hv heq
      exact hnone ⟨Sum.inl ⟨v, hv⟩, heq⟩
    · intro v hv hvi heq
      exact hnone ⟨Sum.inr ⟨⟨v, hv⟩, hvi⟩, heq⟩
  have hc : Fintype.card (Neigh ⊕ Other) ≤ 2 * Fintype.card Neigh := by
    rw [Fintype.card_sum]
    have ho : Fintype.card Other ≤ Fintype.card Neigh := Fintype.card_subtype_le _
    omega
  calc
    _ ≤ (FinDist.uniformColors (α := Position N) (Color := Color)).eventMass
        (fun color ↦ ∃ k, color (left k) = color (right k)) :=
      FinDist.eventMass_mono _ _ _ hsub
    _ ≤ (Fintype.card (Neigh ⊕ Other) : ℝ) / Fintype.card Color :=
      FinDist.uniformColors_forbidden_pairs_le left right hne
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc

/-- Eight times the cutoff plus one colors bounds every low-degree pair's
separation failure probability by one quarter. -/
theorem separating_failure_le_quarter (M : ForestModel N V) (h : History N V)
    (i j : ResidualVertex h) (D : ℕ)
    (hdeg : Fintype.card (ResidualNeighbors M h j) ≤ D)
    (hcolors : 8 * (D + 1) ≤ Fintype.card Color) :
    (FinDist.uniformColors (α := Position N) (Color := Color)).eventMass
      (fun color ↦ ¬ Separating M h color i j) ≤ (1 / 4 : ℝ) := by
  apply (separating_failure_le M h i j).trans
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card Color))).2
  have hd : (Fintype.card (ResidualNeighbors M h j) : ℝ) ≤ D := by exact_mod_cast hdeg
  have hc : (8 : ℝ) * (D + 1) ≤ Fintype.card Color := by exact_mod_cast hcolors
  linarith

/-- Actual fresh independent colors give the majority separation estimate
for one fixed low-degree pair, conditional on any already fixed history. -/
theorem majority_separation_failure_le_exp (M : ForestModel N V) (h : History N V)
    (i j : ResidualVertex h) (D T : ℕ)
    (hdeg : Fintype.card (ResidualNeighbors M h j) ≤ D)
    (hcolors : 8 * (D + 1) ≤ Fintype.card Color) :
    (FinDist.piProduct fun _ : Fin T ↦
      FinDist.uniformColors (α := Position N) (Color := Color)).eventMass
      (fun colors ↦ T ≤ 2 * FinDist.badCount
        (fun _ color ↦ ¬ Separating M h color i j) colors) ≤
      Real.exp (-(T : ℝ) / 8) := by
  classical
  simpa only [Fintype.card_fin] using
    FinDist.piProduct_majority_failure_le_exp
      (fun _ : Fin T ↦ FinDist.uniformColors (α := Position N) (Color := Color))
      (fun _ color ↦ ¬ Separating M h color i j)
      (fun _ ↦ separating_failure_le_quarter M h i j D hdeg hcolors)

/-- Simultaneous failure event for all low-degree ordered residual pairs.
The history and draft have already been fixed before this law is sampled. -/
def SomePairFails (M : ForestModel N V) (h : History N V) (D T : ℕ)
    (colors : Fin T → Position N → Color) : Prop :=
  ∃ i j : ResidualVertex h, Fintype.card (ResidualNeighbors M h j) ≤ D ∧
    T ≤ 2 * FinDist.badCount (fun _ color ↦ ¬ Separating M h color i j) colors

/-- One fresh screen has at most N² pair events, with no independence
assumption between different pairs. -/
theorem somePairFails_le (M : ForestModel N V) (h : History N V) (D T : ℕ)
    (hcolors : 8 * (D + 1) ≤ Fintype.card Color) :
    (FinDist.piProduct fun _ : Fin T ↦
      FinDist.uniformColors (α := Position N) (Color := Color)).eventMass
      (SomePairFails M h D T) ≤ (N : ℝ)^2 * Real.exp (-(T : ℝ) / 8) := by
  let law := FinDist.piProduct fun _ : Fin T ↦
    FinDist.uniformColors (α := Position N) (Color := Color)
  let E : (ResidualVertex h × ResidualVertex h) → (Fin T → Position N → Color) → Prop :=
    fun ij colors ↦ Fintype.card (ResidualNeighbors M h ij.2) ≤ D ∧
      T ≤ 2 * FinDist.badCount (fun _ color ↦ ¬ Separating M h color ij.1 ij.2) colors
  have hevent : law.eventMass (SomePairFails M h D T) =
      law.eventMass (fun colors ↦ ∃ ij, E ij colors) := by
    apply law.eventMass_congr
    intro colors
    constructor
    · rintro ⟨i, j, hij⟩
      exact ⟨(i,j), hij⟩
    · rintro ⟨⟨i,j⟩, hij⟩
      exact ⟨i,j,hij⟩
  have heach : ∀ ij, law.eventMass (E ij) ≤ Real.exp (-(T : ℝ)/8) := by
    rintro ⟨i,j⟩
    by_cases hd : Fintype.card (ResidualNeighbors M h j) ≤ D
    · apply (law.eventMass_mono (E (i,j))
        (fun colors ↦ T ≤ 2 * FinDist.badCount
          (fun _ color ↦ ¬ Separating M h color i j) colors) (fun _ hE ↦ hE.2)).trans
      exact majority_separation_failure_le_exp M h i j D T hd hcolors
    · have hz : law.eventMass (E (i,j)) = 0 := by simp [FinDist.eventMass, E, hd]
      rw [hz]
      exact (Real.exp_pos _).le
  have hcard : Fintype.card (ResidualVertex h) ≤ N := by
    exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin N)
  rw [hevent]
  apply (law.eventMass_exists_le_card_mul E _ heach).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [Fintype.card_prod, Nat.cast_mul, ← sq]
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcard) 2

/-- The manuscript's logarithmic repetition allocation makes the whole
current-screen failure probability at most η/S. -/
theorem somePairFails_le_budget (M : ForestModel N V) (h : History N V)
    (D T S : ℕ) (η : ℝ) (hN : 0 < N) (hS : 0 < S) (hη : 0 < η)
    (hcolors : 8 * (D + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((S : ℝ) * (N : ℝ)^2 / η) ≤ (T : ℝ)) :
    (FinDist.piProduct fun _ : Fin T ↦
      FinDist.uniformColors (α := Position N) (Color := Color)).eventMass
      (SomePairFails M h D T) ≤ η / S := by
  apply (somePairFails_le M h D T hcolors).trans
  have hb : 0 < (S : ℝ) * (N : ℝ)^2 := by positivity
  have ht := FinDist.exp_repetitions_le_budget ((S : ℝ)*(N : ℝ)^2) η hb hη T hT
  calc
    _ ≤ (N : ℝ)^2 * (η / ((S : ℝ)*(N : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg _)
    _ = η / S := by
      have hn : (N : ℝ) ≠ 0 := by positivity
      have hs : (S : ℝ) ≠ 0 := by positivity
      field_simp

end
end Screening
end ForestSampling
