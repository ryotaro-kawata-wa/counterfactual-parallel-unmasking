import ForestSampling.PathClass
import ForestSampling.FiniteInformation

set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators

namespace ForestSampling.PathClass.Parameters
noncomputable section
variable {B : ℕ}

/-- Grouping both independent emission marginals recovers their actual
binary type masses, for any function of the two types. -/
theorem marginal_pair_type_sum (P : Parameters B) (f : Bool → Bool → ℝ) :
    (∑ a : Token B, ∑ b : Token B, P.marginal a * P.marginal b * f (tokenType a) (tokenType b)) =
      ∑ s : Bool, ∑ t : Bool, P.typeMass s * P.typeMass t * f s t := by
  calc
    _ = ∑ a, P.marginal a * (∑ b, P.marginal b * f (tokenType a) (tokenType b)) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ a, P.marginal a * (∑ t : Bool, P.typeMass t * f (tokenType a) t) := by
      simp_rw [P.marginal_type_sum]
    _ = ∑ s : Bool, P.typeMass s * (∑ t : Bool, P.typeMass t * f s t) :=
      P.marginal_type_sum (fun s ↦ ∑ t : Bool, P.typeMass t * f s t)
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

/-- A pair density with independent within-type emissions has precisely
its weighted two-type table as its actual deterministic pushforward. -/
theorem pair_type_map_apply (P : Parameters B) (p : FinDist (Token B × Token B))
    (f : Bool → Bool → ℝ)
    (hp : ∀ a b, p (a,b) = P.marginal a * P.marginal b * f (tokenType a) (tokenType b))
    (s t : Bool) :
    p.map (fun x ↦ (tokenType x.1, tokenType x.2)) (s,t) = P.typeMass s * P.typeMass t * f s t := by
  rw [FinDist.map_apply, Fintype.sum_prod_type]
  calc
    _ = ∑ a, ∑ b, P.marginal a * P.marginal b *
        (if tokenType a = s ∧ tokenType b = t then f (tokenType a) (tokenType b) else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hp]
      by_cases ha : tokenType a = s <;> by_cases hb : tokenType b = t <;>
        simp [Prod.ext_iff, ha, hb]
    _ = ∑ u : Bool, ∑ v : Bool, P.typeMass u * P.typeMass v *
        (if u = s ∧ v = t then f u v else 0) := P.marginal_pair_type_sum (fun u v ↦ if u = s ∧ v = t then f u v else 0)
    _ = _ := by cases s <;> cases t <;> simp [Fintype.sum_bool]

/-- The left token marginal retains the original within-type emission. -/
theorem pair_leftMarginal_apply (P : Parameters B) (p : FinDist (Token B × Token B))
    (f : Bool → Bool → ℝ)
    (hp : ∀ a b, p (a,b) = P.marginal a * P.marginal b * f (tokenType a) (tokenType b))
    (a : Token B) :
    p.leftMarginal a = P.marginal a * (∑ t : Bool, P.typeMass t * f (tokenType a) t) := by
  rw [FinDist.leftMarginal_apply]
  simp_rw [hp, mul_assoc]
  rw [← Finset.mul_sum, P.marginal_type_sum]

/-- The right token marginal retains the original within-type emission. -/
theorem pair_rightMarginal_apply (P : Parameters B) (p : FinDist (Token B × Token B))
    (f : Bool → Bool → ℝ)
    (hp : ∀ a b, p (a,b) = P.marginal a * P.marginal b * f (tokenType a) (tokenType b))
    (b : Token B) :
    p.rightMarginal b = P.marginal b * (∑ s : Bool, P.typeMass s * f s (tokenType b)) := by
  rw [FinDist.rightMarginal_apply]
  simp_rw [hp]
  calc
    _ = P.marginal b * (∑ a, P.marginal a * f (tokenType a) (tokenType b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [P.marginal_type_sum (fun s ↦ f s (tokenType b))]

/-- Exact marginal formulas for the actual type-pair pushforward. -/
theorem pair_type_leftMarginal_apply (P : Parameters B) (p : FinDist (Token B × Token B))
    (f : Bool → Bool → ℝ)
    (hp : ∀ a b, p (a,b) = P.marginal a * P.marginal b * f (tokenType a) (tokenType b))
    (s : Bool) :
    (p.map (fun x ↦ (tokenType x.1, tokenType x.2))).leftMarginal s =
      P.typeMass s * (∑ t : Bool, P.typeMass t * f s t) := by
  rw [FinDist.leftMarginal_apply]
  simp_rw [P.pair_type_map_apply p f hp, mul_assoc]
  rw [← Finset.mul_sum]

theorem pair_type_rightMarginal_apply (P : Parameters B) (p : FinDist (Token B × Token B))
    (f : Bool → Bool → ℝ)
    (hp : ∀ a b, p (a,b) = P.marginal a * P.marginal b * f (tokenType a) (tokenType b))
    (t : Bool) :
    (p.map (fun x ↦ (tokenType x.1, tokenType x.2))).rightMarginal t =
      P.typeMass t * (∑ s : Bool, P.typeMass s * f s t) := by
  rw [FinDist.rightMarginal_apply]
  simp_rw [P.pair_type_map_apply p f hp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Independent emissions within the two types contribute no pair mutual
information, for every normalized density of the displayed type-weight form. -/
theorem pair_mutualInformation_eq_types (P : Parameters B) (p : FinDist (Token B × Token B))
    (f : Bool → Bool → ℝ)
    (hp : ∀ a b, p (a,b) = P.marginal a * P.marginal b * f (tokenType a) (tokenType b)) :
    p.mutualInformation = (p.map (fun x ↦ (tokenType x.1, tokenType x.2))).mutualInformation := by
  apply FinDist.mutualInformation_eq_map_of_ratio p (tokenType (B := B)) (tokenType (B := B))
  intro a b
  rw [← FinDist.leftMarginal_map_pair p (tokenType (B := B)) (tokenType (B := B)),
    ← FinDist.rightMarginal_map_pair p (tokenType (B := B)) (tokenType (B := B))]
  rw [P.pair_type_map_apply p f hp, P.pair_type_leftMarginal_apply p f hp,
    P.pair_type_rightMarginal_apply p f hp, P.pair_leftMarginal_apply p f hp,
    P.pair_rightMarginal_apply p f hp, hp]
  have ha := (P.marginal_positive a).ne'
  have hb := (P.marginal_positive b).ne'
  have hs := (P.typeMass_pos (tokenType a)).ne'
  have ht := (P.typeMass_pos (tokenType b)).ne'
  field_simp [ha, hb, hs, ht]

/-- The full-vocabulary pair information is bounded by the binary alphabet
cap, independently of the number of background tokens. -/
theorem pair_mutualInformation_le_log_two (P : Parameters B) (p : FinDist (Token B × Token B))
    (f : Bool → Bool → ℝ) (hf : ∀ s t, 0 < f s t)
    (hp : ∀ a b, p (a,b) = P.marginal a * P.marginal b * f (tokenType a) (tokenType b)) :
    p.mutualInformation ≤ Real.log 2 := by
  rw [P.pair_mutualInformation_eq_types p f hp]
  have hpos : (p.map (fun x ↦ (tokenType x.1, tokenType x.2))).StrictlyPositive := by
    intro z
    rw [P.pair_type_map_apply p f hp]
    exact mul_pos (mul_pos (P.typeMass_pos z.1) (P.typeMass_pos z.2)) (hf z.1 z.2)
  simpa only [Fintype.card_bool, Nat.cast_ofNat] using FinDist.mutualInformation_le_log_card_right _ hpos

end
end ForestSampling.PathClass.Parameters
