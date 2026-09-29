import ForestSampling.PathConditionals
import ForestSampling.PathResponse
import ForestSampling.PathEdge
import ForestSampling.Screening

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace PathClass
namespace Parameters

variable {B : ℕ}

noncomputable section

theorem incidentWeight_at_source (P : Parameters B) {n : ℕ}
    {i j : Position (n + 1)} (hij : i ≠ j) (e : Fin n)
    (he : (e.castSucc = i ∧ e.succ = j) ∨ (e.castSucc = j ∧ e.succ = i))
    (a : Token B) (z : CompleteBoundary (n + 1) (Token B) i j) (s : Bool) :
    P.incidentWeight j (CompleteBoundary.extension i j a none z) s e =
      P.interaction (tokenType a) s := by
  rcases he with ⟨hei, hej⟩ | ⟨hej, hei⟩
  · simp [incidentWeight, hei, hej, hij, CompleteBoundary.extension]
  · simp only [incidentWeight, hej, ite_true, hei, CompleteBoundary.extension,
      dite_true]
    exact P.interaction_symmetric _ _

/-- All remaining local factors are independent of the revealed source
token once its unique incident edge has been removed. -/
theorem incidentWeight_source_invariant (P : Parameters B) {n : ℕ}
    {i j : Position (n + 1)} (e : Fin n)
    (he : (e.castSucc = i ∧ e.succ = j) ∨ (e.castSucc = j ∧ e.succ = i))
    (a b : Token B) (z : CompleteBoundary (n + 1) (Token B) i j) (s : Bool)
    (k : Fin n) (hk : k ≠ e) :
    P.incidentWeight j (CompleteBoundary.extension i j a none z) s k =
      P.incidentWeight j (CompleteBoundary.extension i j b none z) s k := by
  have hends : k.castSucc ≠ k.succ := by
    intro hh
    have hh' := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_succ] at hh'
    omega
  by_cases hl : k.castSucc = j
  · have hki : k.succ ≠ i := fun hh ↦
      hk (PathGraph.edge_index_unique he (Or.inr ⟨hl, hh⟩))
    have hkj : k.succ ≠ j := fun hh ↦ hends (hl.trans hh.symm)
    simp [incidentWeight, hl, CompleteBoundary.extension, hki, hkj]
  · by_cases hr : k.succ = j
    · have hki : k.castSucc ≠ i := fun hh ↦
        hk (PathGraph.edge_index_unique he (Or.inl ⟨hh, hr⟩))
      simp [incidentWeight, hl, hr, CompleteBoundary.extension, hki]
    · simp [incidentWeight, hl, hr]

def remainingWeight (P : Parameters B) {n : ℕ} {i j : Position (n + 1)}
    (e : Fin n) (z : CompleteBoundary (n + 1) (Token B) i j) (s : Bool) : ℝ :=
  ∏ k ∈ Finset.univ.erase e,
    P.incidentWeight j (CompleteBoundary.extension i j none none z) s k

theorem remainingWeight_pos (P : Parameters B) {n : ℕ} {i j : Position (n + 1)}
    (e : Fin n) (z : CompleteBoundary (n + 1) (Token B) i j) (s : Bool) :
    0 < P.remainingWeight e z s :=
  Finset.prod_pos (fun k _ ↦ P.incidentWeight_pos _ _ _ k)

theorem localTypeWeight_source_factor (P : Parameters B) {n : ℕ}
    {i j : Position (n + 1)} (hij : i ≠ j) (e : Fin n)
    (he : (e.castSucc = i ∧ e.succ = j) ∨ (e.castSucc = j ∧ e.succ = i))
    (a : Token B) (z : CompleteBoundary (n + 1) (Token B) i j) (s : Bool) :
    P.localTypeWeight j (CompleteBoundary.extension i j a none z) s =
      P.interaction (tokenType a) s * P.remainingWeight e z s := by
  unfold localTypeWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e),
    P.incidentWeight_at_source hij e he a z s]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  exact P.incidentWeight_source_invariant e he a none z s k (Finset.mem_erase.mp hk).1

theorem scaledInteractionOdds (P : Parameters B) (s : Bool) :
    (1 - P.p) * P.interaction s false / (P.p * P.interaction s true) =
      if s then 1 else P.scaledOdds := by
  have hp : 0 < 1 - P.p := by linarith [P.p_lt_half]
  cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true, interaction,
    typeJointMass, typeMass, scaledOdds]
  all_goals field_simp [P.p_pos.ne', hp.ne']

def remainingOdds (P : Parameters B) {n : ℕ} {i j : Position (n + 1)}
    (e : Fin n) (z : CompleteBoundary (n + 1) (Token B) i j) : ℝ :=
  P.remainingWeight e z false / P.remainingWeight e z true

theorem remainingOdds_pos (P : Parameters B) {n : ℕ} {i j : Position (n + 1)}
    (e : Fin n) (z : CompleteBoundary (n + 1) (Token B) i j) :
    0 < P.remainingOdds e z :=
  div_pos (P.remainingWeight_pos e z false) (P.remainingWeight_pos e z true)

/-- Actual complete-boundary rows are the explicit response rows. The
other-neighbor odds are fixed independently of the source token. -/
theorem boundaryRow_eq_responseRow (P : Parameters B) {n : ℕ}
    {i j : Position (n + 1)} (hij : i ≠ j) (e : Fin n)
    (he : (e.castSucc = i ∧ e.succ = j) ∨ (e.castSucc = j ∧ e.succ = i))
    (a : Token B) (z : CompleteBoundary (n + 1) (Token B) i j) :
    (P.model n).target.boundaryRow (P.model n).target_positive i j a z =
      P.responseRow (P.remainingOdds e z) (P.remainingOdds_pos e z).le a := by
  rw [P.boundaryRow_localWeight hij]
  change FinDist.ofPositiveWeights (fun b ↦ P.marginal b *
    P.localTypeWeight j (CompleteBoundary.extension i j a none z) (tokenType b)) _ = _
  rw [P.normalized_type_weights _ (P.localTypeWeight_pos _ _)]
  have hr : (1 - P.p) * P.localTypeWeight j (CompleteBoundary.extension i j a none z) false /
      (P.p * P.localTypeWeight j (CompleteBoundary.extension i j a none z) true) =
      (if tokenType a then 1 else P.scaledOdds) * P.remainingOdds e z := by
    rw [P.localTypeWeight_source_factor hij e he, P.localTypeWeight_source_factor hij e he]
    rw [← P.scaledInteractionOdds]
    unfold remainingOdds
    field_simp
  have hcongr (r s : ℝ) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s) (hh : r = s) :
      P.oddsRow r hr0 = P.oddsRow s hs0 := by subst s; rfl
  unfold responseRow
  split_ifs with htype
  · exact hcongr _ _ _ _ (by simpa [htype] using hr)
  · exact hcongr _ _ _ _ (by simpa [htype] using hr)

/-- The actual path model satisfies RT with constant and exponent one,
including nonedges and every complete boundary assignment. -/
theorem model_tailResponseRegular (P : Parameters B) (n : ℕ) :
    (P.model n).TailResponseRegular 1 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro i j hij t ht _ z a b ha hb
  by_cases hadj : (P.model n).graph.Adj i j
  · obtain ⟨e, he⟩ := PathGraph.exists_edge_index hadj
    rw [P.boundaryRow_eq_responseRow hij e he a z,
      P.boundaryRow_eq_responseRow hij e he b z]
    simp only [ForestModel.mem_tailSet_iff, model_marginal] at ha hb
    simpa using P.responseRow_tail_bound _ (P.remainingOdds_pos e z).le t ht a b ha hb
  · rw [Screening.boundaryRow_eq_of_not_adj (P.model n) hij hadj z a b, FinDist.tv_self]
    simpa using ht

end
end Parameters
end PathClass
end ForestSampling
