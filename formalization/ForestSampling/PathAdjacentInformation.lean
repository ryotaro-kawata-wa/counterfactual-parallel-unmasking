import ForestSampling.PairLocalMarkov

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.PathClass.Parameters
noncomputable section
variable {B : ℕ}

/-- The four possible positive outer-boundary type tables depend only on
the binary parameter, not on the path length or vocabulary size. -/
def adjacentTypeWeight (P : Parameters B) (left right : Bool) (st : Bool × Bool) : ℝ :=
  P.typeJointMass st.1 st.2 * P.interaction left st.1 * P.interaction st.2 right

theorem adjacentTypeWeight_pos (P : Parameters B) (left right : Bool) (st : Bool × Bool) :
    0 < P.adjacentTypeWeight left right st :=
  mul_pos (mul_pos (P.typeJointMass_pos _ _) (P.interaction_pos _ _)) (P.interaction_pos _ _)

def adjacentTypeLaw (P : Parameters B) (left right : Bool) : FinDist (Bool × Bool) :=
  FinDist.ofPositiveWeights (P.adjacentTypeWeight left right) (P.adjacentTypeWeight_pos left right)

theorem adjacentTypeLaw_positive (P : Parameters B) (left right : Bool) :
    (P.adjacentTypeLaw left right).StrictlyPositive := by
  intro st
  exact div_pos (P.adjacentTypeWeight_pos left right st)
    (Finset.sum_pos (fun st _ ↦ P.adjacentTypeWeight_pos left right st) Finset.univ_nonempty)

/-- Positive row/column rescaling preserves the strict binary determinant. -/
theorem adjacentTypeWeight_determinant_pos (P : Parameters B) (left right : Bool) :
    0 < P.adjacentTypeWeight left right (false,false) * P.adjacentTypeWeight left right (true,true) -
      P.adjacentTypeWeight left right (false,true) * P.adjacentTypeWeight left right (true,false) := by
  have hfactor := mul_pos (mul_pos (mul_pos (P.interaction_pos left false)
    (P.interaction_pos left true)) (P.interaction_pos false right)) (P.interaction_pos true right)
  have hh := mul_pos hfactor P.typeJoint_determinant_pos
  unfold adjacentTypeWeight
  nlinarith only [hh]

theorem adjacentTypeLaw_determinant_pos (P : Parameters B) (left right : Bool) :
    0 < P.adjacentTypeLaw left right (false,false) * P.adjacentTypeLaw left right (true,true) -
      P.adjacentTypeLaw left right (false,true) * P.adjacentTypeLaw left right (true,false) := by
  let Z := ∑ st, P.adjacentTypeWeight left right st
  have hz : 0 < Z := Finset.sum_pos (fun st _ ↦ P.adjacentTypeWeight_pos left right st) Finset.univ_nonempty
  have hh := div_pos (P.adjacentTypeWeight_determinant_pos left right) (sq_pos_of_pos hz)
  change 0 < P.adjacentTypeWeight left right (false,false)/Z * (P.adjacentTypeWeight left right (true,true)/Z) -
    P.adjacentTypeWeight left right (false,true)/Z * (P.adjacentTypeWeight left right (true,false)/Z)
  rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, ← pow_two]
  exact hh

/-- Every one of the four conditional type pairs has strictly positive MI. -/
theorem adjacentTypeLaw_mutualInformation_pos (P : Parameters B) (left right : Bool) :
    0 < (P.adjacentTypeLaw left right).mutualInformation := by
  apply FinDist.mutualInformation_pos_of_ne _ (P.adjacentTypeLaw_positive left right)
  intro heq
  have hh := P.adjacentTypeLaw_determinant_pos left right
  rw [heq] at hh
  simp only [FinDist.prod_apply] at hh
  nlinarith

/-- The minimum over the four outer-type pairs is uniform in all histories. -/
def adjacentInformationConstant (P : Parameters B) : ℝ :=
  min (min (P.adjacentTypeLaw false false).mutualInformation (P.adjacentTypeLaw false true).mutualInformation)
    (min (P.adjacentTypeLaw true false).mutualInformation (P.adjacentTypeLaw true true).mutualInformation)

theorem adjacentInformationConstant_pos (P : Parameters B) : 0 < P.adjacentInformationConstant := by
  exact lt_min (lt_min (P.adjacentTypeLaw_mutualInformation_pos false false)
    (P.adjacentTypeLaw_mutualInformation_pos false true))
    (lt_min (P.adjacentTypeLaw_mutualInformation_pos true false)
      (P.adjacentTypeLaw_mutualInformation_pos true true))

theorem adjacentInformationConstant_le (P : Parameters B) (left right : Bool) :
    P.adjacentInformationConstant ≤ (P.adjacentTypeLaw left right).mutualInformation := by
  unfold adjacentInformationConstant
  cases left <;> cases right
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)


theorem adjacentTypeLaw_eq_of_parameter {B' : ℕ} (P : Parameters B) (Q : Parameters B')
    (hp : P.p = Q.p) (left right : Bool) : P.adjacentTypeLaw left right = Q.adjacentTypeLaw left right := by
  ext st
  simp only [adjacentTypeLaw, FinDist.ofPositiveWeights_apply, adjacentTypeWeight, interaction,
    typeJointMass, typeMass, hp]

theorem adjacentInformationConstant_eq_of_parameter {B' : ℕ} (P : Parameters B) (Q : Parameters B')
    (hp : P.p = Q.p) : P.adjacentInformationConstant = Q.adjacentInformationConstant := by
  simp only [adjacentInformationConstant, P.adjacentTypeLaw_eq_of_parameter Q hp]

/-- The full-vocabulary normalizer equals its four-entry type normalizer. -/
theorem adjacentPairWeight_sum (P : Parameters B) (left right : Bool) :
    (∑ ab, P.adjacentPairWeight left right ab) = ∑ st, P.adjacentTypeWeight left right st := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hh := P.marginal_pair_type_sum
    (fun s t ↦ P.interaction left s * P.interaction s t * P.interaction t right)
  calc
    _ = ∑ a, ∑ b, P.marginal a * P.marginal b *
        (P.interaction left (tokenType a) * P.interaction (tokenType a) (tokenType b) *
          P.interaction (tokenType b) right) := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      unfold adjacentPairWeight
      ring
    _ = _ := hh
    _ = _ := by
      apply Finset.sum_congr rfl; intro s _
      apply Finset.sum_congr rfl; intro t _
      unfold adjacentTypeWeight interaction
      field_simp [(P.typeMass_pos s).ne', (P.typeMass_pos t).ne']
      <;> ring

/-- Independent within-type emissions cancel exactly after conditioning
on both outer neighbors, giving the actual four-entry type law. -/
theorem adjacentPair_mutualInformation_eq_type (P : Parameters B) (left right : Bool) :
    (FinDist.ofPositiveWeights (P.adjacentPairWeight left right)
      (P.adjacentPairWeight_pos left right)).mutualInformation =
        (P.adjacentTypeLaw left right).mutualInformation := by
  let Z := ∑ st, P.adjacentTypeWeight left right st
  let f : Bool → Bool → ℝ := fun s t ↦
    P.interaction left s * P.interaction s t * P.interaction t right / Z
  let p := FinDist.ofPositiveWeights (P.adjacentPairWeight left right) (P.adjacentPairWeight_pos left right)
  have hform (a b : Token B) : p (a,b) = P.marginal a * P.marginal b * f (tokenType a) (tokenType b) := by
    change P.adjacentPairWeight left right (a,b) / (∑ ab, P.adjacentPairWeight left right ab) = _
    rw [P.adjacentPairWeight_sum left right]
    unfold adjacentPairWeight f Z
    ring
  rw [P.pair_mutualInformation_eq_types p f hform]
  congr 1
  ext st
  rw [P.pair_type_map_apply p f hform]
  change P.typeMass st.1 * P.typeMass st.2 * f st.1 st.2 = P.adjacentTypeWeight left right st / Z
  unfold f adjacentTypeWeight interaction
  field_simp [(P.typeMass_pos st.1).ne', (P.typeMass_pos st.2).ne']
  <;> ring

/-- The actual observed-history adjacent pair has the same positive
uniform lower bound whenever its two outer neighbors are observed. -/
theorem exactPair_adjacent_mutualInformation_ge (P : Parameters B) {n : ℕ}
    (y : MaskedState (n + 1) (Token B)) (l i j r : Position (n + 1))
    (hli : l.val + 1 = i.val) (hijv : i.val + 1 = j.val) (hjr : j.val + 1 = r.val)
    (hi : y i = none) (hj : y j = none) (left right : Token B)
    (hl : y l = some left) (hr : y r = some right) :
    P.adjacentInformationConstant ≤
      (y.exactPair (P.target (n + 1)) (P.target_positive _) i j).mutualInformation := by
  rw [P.exactPair_adjacent_of_neighbors y l i j r hli hijv hjr hi hj left right hl hr,
    P.adjacentPair_mutualInformation_eq_type]
  exact P.adjacentInformationConstant_le _ _

end
end ForestSampling.PathClass.Parameters
