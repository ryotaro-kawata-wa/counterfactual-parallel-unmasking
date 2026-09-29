import ForestSampling.PathBoundaryResponse

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace PathClass
namespace Parameters

variable {B : ℕ}

noncomputable section

theorem interactionOdds (P : Parameters B) (s : Bool) :
    P.interaction s false / P.interaction s true =
      if s then P.otherOddsB else P.otherOddsA := by
  have hp : 0 < 1 - P.p := by linarith [P.p_lt_half]
  cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true, interaction,
    typeJointMass, typeMass, otherOddsA, otherOddsB]
  all_goals field_simp [P.p_pos.ne', hp.ne']

theorem incidentOdds_choices (P : Parameters B) {n : ℕ} (j : Position (n + 1))
    (x : Configuration (n + 1) (Token B)) (k : Fin n)
    (hk : k.castSucc = j ∨ k.succ = j) :
    P.incidentWeight j x false k / P.incidentWeight j x true k = P.otherOddsA ∨
      P.incidentWeight j x false k / P.incidentWeight j x true k = P.otherOddsB := by
  by_cases hl : k.castSucc = j
  · simp only [incidentWeight, hl, ite_true]
    rw [P.interaction_symmetric false, P.interaction_symmetric true, P.interactionOdds]
    cases tokenType (x k.succ) <;> simp
  · have hr : k.succ = j := hk.resolve_left hl
    simp only [incidentWeight, hl, ite_false, hr, ite_true]
    rw [P.interactionOdds]
    cases tokenType (x k.castSucc) <;> simp

/-- Nonincident edges contribute exactly one to the odds ratio, so only
the actual remaining incident edges survive in the product. -/
theorem remainingOdds_eq_product (P : Parameters B) {n : ℕ} {i j : Position (n + 1)}
    (e : Fin n) (z : CompleteBoundary (n + 1) (Token B) i j) :
    P.remainingOdds e z = ∏ k ∈ PathGraph.otherIncidentEdges j e,
      P.incidentWeight j (CompleteBoundary.extension i j none none z) false k /
        P.incidentWeight j (CompleteBoundary.extension i j none none z) true k := by
  unfold remainingOdds remainingWeight
  rw [← Finset.prod_div_distrib]
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro k hk hnot
  have hn : ¬ (k.castSucc = j ∨ k.succ = j) := by
    intro hh
    exact hnot (Finset.mem_filter.mpr ⟨hk, hh⟩)
  simp [incidentWeight, (not_or.mp hn).1, (not_or.mp hn).2]

/-- The path's second neighbor produces exactly one of the three odds
values used in the manuscript's positive uniform signal constant. -/
theorem remainingOdds_choices (P : Parameters B) {n : ℕ} {i j : Position (n + 1)}
    (e : Fin n) (he : e.castSucc = j ∨ e.succ = j)
    (z : CompleteBoundary (n + 1) (Token B) i j) :
    P.remainingOdds e z = 1 ∨ P.remainingOdds e z = P.otherOddsA ∨
      P.remainingOdds e z = P.otherOddsB := by
  rw [P.remainingOdds_eq_product]
  by_cases hempty : PathGraph.otherIncidentEdges j e = ∅
  · simp [hempty]
  · have hcard := PathGraph.otherIncidentEdges_card_le_one j e he
    have hpos : 0 < (PathGraph.otherIncidentEdges j e).card := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hempty)
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp (show (PathGraph.otherIncidentEdges j e).card = 1 by omega)
    have hkmem : k ∈ PathGraph.otherIncidentEdges j e := by rw [hk]; simp
    have hincident : k.castSucc = j ∨ k.succ = j := (Finset.mem_filter.mp hkmem).2
    rw [hk, Finset.prod_singleton]
    exact Or.inr (P.incidentOdds_choices j _ k hincident)

theorem edgeSignal_le_one (P : Parameters B) : P.edgeSignal ≤ 1 := by
  exact (P.edgeSignal_le_response 1 (Or.inl rfl)).trans
    ((P.response_le_one_sub_p 1 (by norm_num)).trans (by linarith [P.p_pos]))

/-- Uniform two-sided edge nondegeneracy of the actual full-vocabulary
path model, with the same positive signal for all lengths and backgrounds. -/
theorem model_edgeNondegenerate (P : Parameters B) (n : ℕ) :
    (P.model n).EdgeNondegenerate P.edgeSignal := by
  refine ⟨P.edgeSignal_pos, P.edgeSignal_le_one, ?_⟩
  intro i j hadj z
  obtain ⟨e, he⟩ := PathGraph.exists_edge_index hadj
  have heincident : e.castSucc = j ∨ e.succ = j := by
    rcases he with ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inr h
    · exact Or.inl h
  have hlocal := P.responseRow_signal_bound (P.remainingOdds e z)
    (P.remainingOdds_pos e z).le (P.remainingOdds_choices e heincident z)
  rw [← P.boundaryRow_eq_responseRow hadj.ne e he none z,
    ← P.boundaryRow_eq_responseRow hadj.ne e he (some none) z] at hlocal
  exact hlocal.trans ((P.model n).pair_response_le_directedResponse hadj.ne z none (some none))

end
end Parameters
end PathClass
end ForestSampling
