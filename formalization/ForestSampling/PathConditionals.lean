import ForestSampling.PathClass
import ForestSampling.ScreeningProbes

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace PathClass
namespace Parameters

variable {B : ℕ}

noncomputable section

/-- The actual path density also has the symmetric node/edge form used
to calculate its complete-boundary conditional distributions. -/
theorem target_symmetric_density (P : Parameters B) (n : ℕ)
    (x : Configuration (n + 1) (Token B)) :
    P.target (n + 1) x = (∏ i, P.marginal (x i)) *
      ∏ e : Fin n, P.interaction (tokenType (x e.castSucc)) (tokenType (x e.succ)) := by
  rw [target_apply]
  simp only [kernel_apply, Finset.prod_mul_distrib, Fin.prod_univ_succ]
  ring

def incidentWeight (P : Parameters B) {n : ℕ} (j : Position (n + 1))
    (x : Configuration (n + 1) (Token B)) (s : Bool) (e : Fin n) : ℝ :=
  if e.castSucc = j then P.interaction s (tokenType (x e.succ))
  else if e.succ = j then P.interaction (tokenType (x e.castSucc)) s else 1

theorem incidentWeight_pos (P : Parameters B) {n : ℕ} (j : Position (n + 1))
    (x : Configuration (n + 1) (Token B)) (s : Bool) (e : Fin n) :
    0 < P.incidentWeight j x s e := by
  unfold incidentWeight
  split_ifs <;> first | exact P.interaction_pos _ _ | exact zero_lt_one

def localTypeWeight (P : Parameters B) {n : ℕ} (j : Position (n + 1))
    (x : Configuration (n + 1) (Token B)) (s : Bool) : ℝ :=
  ∏ e : Fin n, P.incidentWeight j x s e

theorem localTypeWeight_pos (P : Parameters B) {n : ℕ} (j : Position (n + 1))
    (x : Configuration (n + 1) (Token B)) (s : Bool) :
    0 < P.localTypeWeight j x s :=
  Finset.prod_pos (fun e _ ↦ P.incidentWeight_pos j x s e)

def localWeight (P : Parameters B) {n : ℕ} (j : Position (n + 1))
    (x : Configuration (n + 1) (Token B)) (a : Token B) : ℝ :=
  P.marginal a * P.localTypeWeight j x (tokenType a)

theorem localWeight_pos (P : Parameters B) {n : ℕ} (j : Position (n + 1))
    (x : Configuration (n + 1) (Token B)) (a : Token B) : 0 < P.localWeight j x a :=
  mul_pos (P.marginal_positive a) (P.localTypeWeight_pos j x (tokenType a))

private theorem nodeProduct_update (P : Parameters B) {n : ℕ} (j : Position (n + 1))
    (x : Configuration (n + 1) (Token B)) (a : Token B) :
    (∏ i, P.marginal (Function.update x j a i)) =
      P.marginal a * ∏ i ∈ Finset.univ.erase j, P.marginal (x i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

/-- Every nonincident edge factor cancels, and each incident factor is
retained exactly once. This identity concerns the actual target density. -/
theorem target_update_local_cross (P : Parameters B) {n : ℕ}
    (j : Position (n + 1)) (x : Configuration (n + 1) (Token B)) (a b : Token B) :
    P.target (n + 1) (Function.update x j a) * P.localWeight j x b =
      P.target (n + 1) (Function.update x j b) * P.localWeight j x a := by
  have hedge :
      (∏ e : Fin n, P.interaction (tokenType (Function.update x j a e.castSucc))
        (tokenType (Function.update x j a e.succ))) * P.localTypeWeight j x (tokenType b) =
      (∏ e : Fin n, P.interaction (tokenType (Function.update x j b e.castSucc))
        (tokenType (Function.update x j b e.succ))) * P.localTypeWeight j x (tokenType a) := by
    unfold localTypeWeight
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e _
    have hends : e.castSucc ≠ e.succ := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at hh
      omega
    by_cases hl : e.castSucc = j
    · have hr : e.succ ≠ j := fun hh ↦ hends (hl.trans hh.symm)
      simp [incidentWeight, hl, hr, mul_comm]
    · by_cases hr : e.succ = j
      · simp [incidentWeight, hl, hr, mul_comm]
      · simp [incidentWeight, hl, hr]
  rw [P.target_symmetric_density, P.target_symmetric_density,
    nodeProduct_update, nodeProduct_update]
  unfold localWeight
  calc
    _ = (P.marginal a * P.marginal b * ∏ i ∈ Finset.univ.erase j, P.marginal (x i)) *
        ((∏ e : Fin n, P.interaction (tokenType (Function.update x j a e.castSucc))
          (tokenType (Function.update x j a e.succ))) * P.localTypeWeight j x (tokenType b)) := by ring
    _ = _ := by rw [hedge]; ring

/-- Normalizing the actual updated target is exactly the normalized local
node/incident-edge weight, with all other factors cancelled by proof. -/
theorem updatedTarget_normalized (P : Parameters B) {n : ℕ} (j : Position (n + 1))
    (x : Configuration (n + 1) (Token B)) :
    FinDist.ofPositiveWeights (fun a ↦ P.target (n + 1) (Function.update x j a))
        (fun _ ↦ P.target_positive _ _) =
      FinDist.ofPositiveWeights (P.localWeight j x) (P.localWeight_pos j x) := by
  apply FinDist.eq_ofPositiveWeights_of_cross_mul
  intro a b
  simp only [FinDist.ofPositiveWeights_apply, div_mul_eq_mul_div]
  rw [P.target_update_local_cross]

/-- The actual complete-boundary row of the path model has the explicit
normalized local interaction formula used in the comparison appendix. -/
theorem boundaryRow_localWeight (P : Parameters B) {n : ℕ} {i j : Position (n + 1)}
    (hij : i ≠ j) (source : Token B) (z : CompleteBoundary (n + 1) (Token B) i j) :
    (P.model n).target.boundaryRow (P.model n).target_positive i j source z =
      FinDist.ofPositiveWeights
        (P.localWeight j (CompleteBoundary.extension i j source none z))
        (P.localWeight_pos j (CompleteBoundary.extension i j source none z)) := by
  rw [← MaskedState.exactRow_boundaryState (P.model n) hij source z]
  rw [(P.model n).exactRow_eq_of_neighbors_fixed _ j (by simp)
    (CompleteBoundary.extension i j source none z)]
  · exact P.updatedTarget_normalized _ _
  · intro v hv
    have hvj : v ≠ j := hv.ne.symm
    by_cases hvi : v = i
    · subst v
      exact ⟨source, by simp [MaskedState.boundaryState, hij],
        by simp [CompleteBoundary.extension]⟩
    · exact ⟨z ⟨v, hvi, hvj⟩, by simp [MaskedState.boundaryState, hvi, hvj],
        by simp [CompleteBoundary.extension, hvi, hvj]⟩

end
end Parameters
end PathClass
end ForestSampling
