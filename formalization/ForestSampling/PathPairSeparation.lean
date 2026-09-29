import ForestSampling.PathPairConditionals
import ForestSampling.MaskedPairIndependence

set_option autoImplicit false

namespace ForestSampling.PathClass.Parameters
noncomputable section
variable {B : ℕ}

/-- Any observed vertex strictly between two masked path positions
separates their actual conditional pair distribution. -/
theorem exactPair_mutualInformation_eq_zero_of_separator (P : Parameters B) {n : ℕ}
    (y : MaskedState (n + 1) (Token B)) (i j k : Position (n + 1))
    (hi : y i = none) (hj : y j = none) (hk : y k ≠ none)
    (hbetween : (i.val < k.val ∧ k.val < j.val) ∨ (j.val < k.val ∧ k.val < i.val)) :
    (y.exactPair (P.target (n + 1)) (P.target_positive _) i j).mutualInformation = 0 := by
  classical
  let label : ResidualVertex y.toHistory → Bool := fun v ↦ decide (v.val.val < k.val)
  have hsep : ∀ u v : ResidualVertex y.toHistory,
      (P.model n).graph.Adj u.val v.val → label u = label v := by
    intro u v huv
    have hu : u.val ≠ k := by
      intro hh
      have hum := (y.mem_toHistory_uncommitted u.val).mp u.property
      exact hk (hh ▸ hum)
    have hv : v.val ≠ k := by
      intro hh
      have hvm := (y.mem_toHistory_uncommitted v.val).mp v.property
      exact hk (hh ▸ hvm)
    have huk : u.val.val ≠ k.val := fun hh ↦ hu (Fin.ext hh)
    have hvk : v.val.val ≠ k.val := fun hh ↦ hv (Fin.ext hh)
    change (SimpleGraph.pathGraph (n + 1)).Adj u.val v.val at huv
    rw [SimpleGraph.pathGraph_adj] at huv
    have hh : u.val.val < k.val ↔ v.val.val < k.val := by rcases huv with h | h <;> omega
    simp only [label, hh]
  apply y.exactPair_mutualInformation_eq_zero_of_separated_labels (P.model n) label hsep i j hi hj
  rcases hbetween with ⟨hik, hkj⟩ | ⟨hjk, hki⟩
  · simp only [label, hik, show ¬ j.val < k.val by omega, decide_true, decide_false, ne_eq,
      Bool.true_eq_false, not_false_eq_true]
  · simp only [label, hjk, show ¬ i.val < k.val by omega, decide_true, decide_false, ne_eq,
      Bool.false_eq_true, not_false_eq_true]

end
end ForestSampling.PathClass.Parameters
