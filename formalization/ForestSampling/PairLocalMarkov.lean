import ForestSampling.PathPairConditionals

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace MaskedState

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Positive local pair weights determine the actual conditional law once
their cross-product identity holds on every compatible outside assignment. -/
theorem exactPair_eq_ofPositiveWeights (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (y : MaskedState N V) {i j : Position N}
    (hij : i ≠ j) (hi : y i = none) (hj : y j = none)
    (w : V × V → ℝ) (hw : ∀ ab, 0 < w ab)
    (hcross : ∀ (z : CompleteBoundary N V i j) (ab cd : V × V),
      y.Agrees (CompleteBoundary.extension i j ab.1 ab.2 z) →
      p (CompleteBoundary.extension i j ab.1 ab.2 z) * w cd =
        p (CompleteBoundary.extension i j cd.1 cd.2 z) * w ab) :
    y.exactPair p hp i j = FinDist.ofPositiveWeights w hw := by
  classical
  apply FinDist.eq_ofPositiveWeights_of_cross_mul
  intro ab cd
  have hratio (ab : V × V) : y.exactPair p hp i j ab =
      p.eventMass (fun x ↦ y.Agrees x ∧ (x i, x j) = ab) / p.eventMass y.Agrees :=
    p.conditionalMap_apply_ratio y.Agrees (y.probability_pos p hp) (fun x ↦ (x i, x j)) ab
  rw [hratio, hratio, eventMass_agrees_pair _ y hij, eventMass_agrees_pair _ y hij,
    div_mul_eq_mul_div, div_mul_eq_mul_div]
  congr 1
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : y.Agrees (CompleteBoundary.extension i j ab.1 ab.2 z)
  · have hz' := (y.agrees_pair_extension_iff hi hj ab.1 ab.2 cd.1 cd.2 z).mp hz
    simp only [hz, hz', ite_true]
    exact hcross z ab cd hz
  · have hz' : ¬ y.Agrees (CompleteBoundary.extension i j cd.1 cd.2 z) :=
      fun hh ↦ hz ((y.agrees_pair_extension_iff hi hj ab.1 ab.2 cd.1 cd.2 z).mpr hh)
    simp [hz, hz']

end MaskedState

namespace PathClass.Parameters

variable {B : ℕ}
noncomputable section

/-- An interior path vertex has exactly its two incident interaction factors. -/
theorem localTypeWeight_two_neighbors (P : Parameters B) {n : ℕ}
    (l j r : Position (n + 1)) (hl : l.val + 1 = j.val) (hr : j.val + 1 = r.val)
    (x : Configuration (n + 1) (Token B)) (s : Bool) :
    P.localTypeWeight j x s =
      P.interaction (tokenType (x l)) s * P.interaction s (tokenType (x r)) := by
  classical
  let el : Fin n := ⟨l.val, by have hh := r.isLt; omega⟩
  let er : Fin n := ⟨j.val, by have hh := r.isLt; omega⟩
  have hel : el.castSucc = l := by apply Fin.ext; rfl
  have helj : el.succ = j := by apply Fin.ext; exact hl
  have her : er.castSucc = j := by apply Fin.ext; rfl
  have herr : er.succ = r := by apply Fin.ext; exact hr
  have hlj : l ≠ j := by intro h; have hh := congrArg Fin.val h; omega
  have hne : el ≠ er := by intro h; have hh := congrArg Fin.val h; change l.val = j.val at hh; omega
  unfold localTypeWeight
  rw [Finset.prod_eq_mul_of_mem el er (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · simp [incidentWeight, hel, helj, her, herr, hlj]
  · intro e _ ⟨he1, he2⟩
    have hleft : e.castSucc ≠ j := by
      intro hh; apply he2; apply Fin.ext
      exact congrArg (fun k : Fin (n + 1) ↦ k.val) hh
    have hright : e.succ ≠ j := by
      intro hh; apply he1; apply Fin.ext
      have hv := congrArg Fin.val hh
      simp only [Fin.val_succ] at hv
      change e.val = l.val
      omega
    simp [incidentWeight, hleft, hright]

def adjacentPairWeight (P : Parameters B) (left right : Bool) (ab : Token B × Token B) : ℝ :=
  P.marginal ab.1 * P.marginal ab.2 *
    P.interaction left (tokenType ab.1) * P.interaction (tokenType ab.1) (tokenType ab.2) *
      P.interaction (tokenType ab.2) right

theorem adjacentPairWeight_pos (P : Parameters B) (left right : Bool) (ab : Token B × Token B) :
    0 < P.adjacentPairWeight left right ab :=
  mul_pos (mul_pos (mul_pos (mul_pos (P.marginal_positive _) (P.marginal_positive _))
    (P.interaction_pos _ _)) (P.interaction_pos _ _)) (P.interaction_pos _ _)

/-- Revealing the two outside neighbors fixes the actual interior adjacent
pair law, irrespective of all farther observations and masks. -/
theorem exactPair_adjacent_of_neighbors (P : Parameters B) {n : ℕ}
    (y : MaskedState (n + 1) (Token B)) (l i j r : Position (n + 1))
    (hli : l.val + 1 = i.val) (hijv : i.val + 1 = j.val) (hjr : j.val + 1 = r.val)
    (hi : y i = none) (hj : y j = none) (left right : Token B)
    (hl : y l = some left) (hr : y r = some right) :
    y.exactPair (P.target (n + 1)) (P.target_positive _) i j =
      FinDist.ofPositiveWeights (P.adjacentPairWeight (tokenType left) (tokenType right))
        (P.adjacentPairWeight_pos _ _) := by
  have hij : i ≠ j := by intro h; have hh := congrArg Fin.val h; omega
  apply y.exactPair_eq_ofPositiveWeights _ (P.target_positive _) hij hi hj
  intro z ab cd hya
  have hy (a b : Token B) : y.Agrees (CompleteBoundary.extension i j a b z) :=
    (y.agrees_pair_extension_iff hi hj ab.1 ab.2 a b z).mp hya
  have hleft (a b : Token B) : CompleteBoundary.extension i j a b z l = left := hy a b l left hl
  have hright (a b : Token B) : CompleteBoundary.extension i j a b z r = right := hy a b r right hr
  have h1 := P.target_update_local_cross i (CompleteBoundary.extension i j ab.1 ab.2 z) ab.1 cd.1
  have h2 := P.target_update_local_cross j (CompleteBoundary.extension i j cd.1 ab.2 z) ab.2 cd.2
  simp only [CompleteBoundary.update_extension_source] at h1
  simp only [CompleteBoundary.update_extension_readout hij] at h2
  simp only [localWeight, P.localTypeWeight_two_neighbors l i j hli hijv] at h1
  rw [hleft] at h1
  simp only [CompleteBoundary.extension, hij.symm, dite_false, dite_true] at h1
  simp only [localWeight, P.localTypeWeight_two_neighbors i j r hijv hjr] at h2
  rw [hright] at h2
  simp only [CompleteBoundary.extension, dite_true] at h2
  apply mul_right_cancel₀ (P.interaction_pos (tokenType cd.1) (tokenType ab.2)).ne'
  calc
    _ = (P.target (n + 1) (CompleteBoundary.extension i j ab.1 ab.2 z) *
          (P.marginal cd.1 * (P.interaction (tokenType left) (tokenType cd.1) *
            P.interaction (tokenType cd.1) (tokenType ab.2)))) *
          (P.marginal cd.2 * (P.interaction (tokenType cd.1) (tokenType cd.2) *
            P.interaction (tokenType cd.2) (tokenType right))) := by unfold adjacentPairWeight; ring
    _ = (P.target (n + 1) (CompleteBoundary.extension i j cd.1 ab.2 z) *
          (P.marginal cd.2 * (P.interaction (tokenType cd.1) (tokenType cd.2) *
            P.interaction (tokenType cd.2) (tokenType right)))) *
          (P.marginal ab.1 * (P.interaction (tokenType left) (tokenType ab.1) *
            P.interaction (tokenType ab.1) (tokenType ab.2))) := by rw [h1]; ring
    _ = _ := by rw [h2]; unfold adjacentPairWeight; ring

end
end PathClass.Parameters
end ForestSampling
