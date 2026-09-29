import ForestSampling.FiniteEntropy
import ForestSampling.ExactReference

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.FinDist
noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The two actual coordinate pushforwards of a finite pair law. -/
def leftMarginal (p : FinDist (α × β)) : FinDist α := p.map Prod.fst
def rightMarginal (p : FinDist (α × β)) : FinDist β := p.map Prod.snd

@[simp] theorem leftMarginal_apply (p : FinDist (α × β)) (a : α) :
    p.leftMarginal a = ∑ b, p (a,b) := by
  unfold leftMarginal
  rw [map_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp

@[simp] theorem rightMarginal_apply (p : FinDist (α × β)) (b : β) :
    p.rightMarginal b = ∑ a, p (a,b) := by
  unfold rightMarginal
  rw [map_apply, Fintype.sum_prod_type]
  simp

theorem leftMarginal_positive [Nonempty β] (p : FinDist (α × β)) (hp : p.StrictlyPositive) :
    p.leftMarginal.StrictlyPositive :=
  p.map_strictlyPositive_of_surjective hp Prod.fst (fun a ↦ ⟨(a, Classical.choice inferInstance), rfl⟩)

theorem rightMarginal_positive [Nonempty α] (p : FinDist (α × β)) (hp : p.StrictlyPositive) :
    p.rightMarginal.StrictlyPositive :=
  p.map_strictlyPositive_of_surjective hp Prod.snd (fun b ↦ ⟨(Classical.choice inferInstance, b), rfl⟩)

@[simp] theorem leftMarginal_prod (p : FinDist α) (q : FinDist β) : (p.prod q).leftMarginal = p := by
  ext a
  rw [leftMarginal_apply]
  simp only [prod_apply, ← Finset.mul_sum, q.sum_mass, mul_one]

@[simp] theorem rightMarginal_prod (p : FinDist α) (q : FinDist β) : (p.prod q).rightMarginal = q := by
  ext b
  rw [rightMarginal_apply]
  simp only [prod_apply, ← Finset.sum_mul, p.sum_mass, one_mul]

/-- Mutual information is the actual pair law's divergence to the product
of its own coordinate marginals. -/
def mutualInformation (p : FinDist (α × β)) : ℝ :=
  klDivergence p (p.leftMarginal.prod p.rightMarginal)

@[simp] theorem mutualInformation_prod (p : FinDist α) (q : FinDist β) :
    mutualInformation (p.prod q) = 0 := by
  simp only [mutualInformation, leftMarginal_prod, rightMarginal_prod, klDivergence_self]

theorem mutualInformation_nonneg [Nonempty α] [Nonempty β]
    (p : FinDist (α × β)) (hp : p.StrictlyPositive) : 0 ≤ p.mutualInformation :=
  klDivergence_nonneg _ _ hp
    (prod_strictlyPositive (p.leftMarginal_positive hp) (p.rightMarginal_positive hp))

theorem mutualInformation_pos_of_ne [Nonempty α] [Nonempty β]
    (p : FinDist (α × β)) (hp : p.StrictlyPositive)
    (hne : p ≠ p.leftMarginal.prod p.rightMarginal) : 0 < p.mutualInformation :=
  klDivergence_pos_of_ne _ _ hp
    (prod_strictlyPositive (p.leftMarginal_positive hp) (p.rightMarginal_positive hp)) hne

/-- A positive finite pair law has the ordinary normalized conditional
right-coordinate distribution at every left-coordinate value. -/
def conditionalRight [Nonempty β] (p : FinDist (α × β)) (hp : p.StrictlyPositive) (a : α) : FinDist β where
  mass b := p (a,b) / p.leftMarginal a
  nonneg b := div_nonneg (p.nonneg _) (p.leftMarginal.nonneg _)
  sum_mass := by
    rw [← Finset.sum_div, ← leftMarginal_apply]
    exact div_self (p.leftMarginal_positive hp a).ne'

@[simp] theorem conditionalRight_apply [Nonempty β] (p : FinDist (α × β))
    (hp : p.StrictlyPositive) (a : α) (b : β) :
    p.conditionalRight hp a b = p (a,b) / p.leftMarginal a := rfl

theorem conditionalRight_positive [Nonempty β] (p : FinDist (α × β))
    (hp : p.StrictlyPositive) (a : α) : (p.conditionalRight hp a).StrictlyPositive :=
  fun b ↦ div_pos (hp (a,b)) (p.leftMarginal_positive hp a)

/-- The normalized formula is the existing actual conditional-readout
operation, not a separate assumed family of posterior laws. -/
theorem conditionalRight_eq_conditionalMap [Nonempty β] (p : FinDist (α × β))
    (hp : p.StrictlyPositive) (a : α) :
    p.conditionalRight hp a = p.conditionalMap (fun x ↦ x.1 = a)
      (p.leftMarginal_positive hp a) Prod.snd := by
  ext b
  simp [conditionalRight, conditionalMap, map_apply, conditionOn, eventMass, Fintype.sum_prod_type]
  congr 1
  rw [Finset.sum_comm]
  simp

/-- Reconstruction of the original pair law from its actual marginal and
conditional kernel, via the canonical sigma/product equivalence. -/
theorem conditionalRight_reconstruct [Nonempty β] (p : FinDist (α × β))
    (hp : p.StrictlyPositive) :
    (sigmaJoint p.leftMarginal (p.conditionalRight hp)).map (Equiv.sigmaEquivProd α β) = p := by
  ext x
  rw [map_equiv_apply]
  change p.leftMarginal x.1 * (p (x.1,x.2) / p.leftMarginal x.1) = p x
  rw [mul_div_cancel₀ _ (p.leftMarginal_positive hp x.1).ne']

/-- The entropy chain rule uses the concrete normalized posterior kernel. -/
theorem entropy_eq_left_add_conditional [Nonempty β] (p : FinDist (α × β))
    (hp : p.StrictlyPositive) :
    entropy p = entropy p.leftMarginal + ∑ a, p.leftMarginal a * entropy (p.conditionalRight hp a) := by
  calc
    entropy p = entropy ((sigmaJoint p.leftMarginal (p.conditionalRight hp)).map (Equiv.sigmaEquivProd α β)) :=
      congrArg entropy (p.conditionalRight_reconstruct hp).symm
    _ = _ := by
      rw [entropy_map_equiv, entropy_sigmaJoint p.leftMarginal (p.conditionalRight hp)
        (p.leftMarginal_positive hp) (p.conditionalRight_positive hp)]

/-- Observing another coordinate cannot reduce joint entropy. -/
theorem entropy_left_le [Nonempty β] (p : FinDist (α × β)) (hp : p.StrictlyPositive) :
    entropy p.leftMarginal ≤ entropy p := by
  rw [entropy_eq_left_add_conditional p hp]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ ↦
    mul_nonneg (p.leftMarginal.nonneg a) (entropy_nonneg _))

/-- The KL definition agrees with the usual entropy expression. -/
theorem mutualInformation_eq_entropy [Nonempty α] [Nonempty β]
    (p : FinDist (α × β)) (hp : p.StrictlyPositive) :
    p.mutualInformation = entropy p.leftMarginal + entropy p.rightMarginal - entropy p := by
  rw [mutualInformation, klDivergence_eq_neg_entropy_sub _ _ hp
    (prod_strictlyPositive (p.leftMarginal_positive hp) (p.rightMarginal_positive hp))]
  have hs : (∑ x, p x * Real.log ((p.leftMarginal.prod p.rightMarginal) x)) =
      (∑ a, p.leftMarginal a * Real.log (p.leftMarginal a)) +
        ∑ b, p.rightMarginal b * Real.log (p.rightMarginal b) := by
    simp only [prod_apply, Real.log_mul (p.leftMarginal_positive hp _).ne' (p.rightMarginal_positive hp _).ne',
      mul_add, Finset.sum_add_distrib]
    rw [← p.sum_map_mul Prod.fst (fun a ↦ Real.log (p.leftMarginal a)),
      ← p.sum_map_mul Prod.snd (fun b ↦ Real.log (p.rightMarginal b))]
    rfl
  rw [hs]
  unfold entropy
  ring

theorem mutualInformation_le_right_entropy [Nonempty α] [Nonempty β]
    (p : FinDist (α × β)) (hp : p.StrictlyPositive) :
    p.mutualInformation ≤ entropy p.rightMarginal := by
  rw [mutualInformation_eq_entropy p hp]
  linarith [entropy_left_le p hp]

theorem mutualInformation_le_log_card_right [Nonempty α] [Nonempty β]
    (p : FinDist (α × β)) (hp : p.StrictlyPositive) :
    p.mutualInformation ≤ Real.log (Fintype.card β) :=
  (mutualInformation_le_right_entropy p hp).trans
    (entropy_le_log_card p.rightMarginal (p.rightMarginal_positive hp))


/-- A deterministic coarse readout preserves KL exactly whenever the
actual likelihood ratio is constant on each fiber of that readout. -/
theorem klDivergence_eq_map_of_ratio {δ : Type*} [Fintype δ] [DecidableEq δ]
    (p q : FinDist α) (f : α → δ)
    (hratio : ∀ a, p a / q a = p.map f (f a) / q.map f (f a)) :
    klDivergence p q = klDivergence (p.map f) (q.map f) := by
  unfold klDivergence
  calc
    _ = ∑ a, p a * Real.log (p.map f (f a) / q.map f (f a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hratio a]
    _ = _ := (p.sum_map_mul f (fun z ↦ Real.log (p.map f z / q.map f z))).symm

/-- Applying separate deterministic maps to independent coordinates keeps
exactly the product of the two actual pushed-forward marginal laws. -/
theorem prod_map_pair {δ ε : Type*} [Fintype δ] [Fintype ε] [DecidableEq δ] [DecidableEq ε]
    (p : FinDist α) (q : FinDist β) (f : α → δ) (g : β → ε) :
    (p.prod q).map (fun x ↦ (f x.1, g x.2)) = (p.map f).prod (q.map g) := by
  ext z
  rw [map_apply, prod_apply, map_apply, map_apply, Fintype.sum_prod_type, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hf : f a = z.1 <;> by_cases hg : g b = z.2 <;> simp [prod_apply, Prod.ext_iff, hf, hg]

theorem leftMarginal_map_pair {δ ε : Type*} [Fintype δ] [Fintype ε] [DecidableEq δ] [DecidableEq ε]
    (p : FinDist (α × β)) (f : α → δ) (g : β → ε) :
    (p.map (fun x ↦ (f x.1, g x.2))).leftMarginal = p.leftMarginal.map f := by
  unfold leftMarginal
  rw [map_comp, map_comp]
  rfl

theorem rightMarginal_map_pair {δ ε : Type*} [Fintype δ] [Fintype ε] [DecidableEq δ] [DecidableEq ε]
    (p : FinDist (α × β)) (f : α → δ) (g : β → ε) :
    (p.map (fun x ↦ (f x.1, g x.2))).rightMarginal = p.rightMarginal.map g := by
  unfold rightMarginal
  rw [map_comp, map_comp]
  rfl

/-- Independent within-type emissions cancel in pair information whenever
the full pair likelihood ratio equals its type-pair likelihood ratio. -/
theorem mutualInformation_eq_map_of_ratio {δ ε : Type*}
    [Fintype δ] [Fintype ε] [DecidableEq δ] [DecidableEq ε]
    (p : FinDist (α × β)) (f : α → δ) (g : β → ε)
    (hratio : ∀ a b, p (a,b) / (p.leftMarginal a * p.rightMarginal b) =
      p.map (fun x ↦ (f x.1, g x.2)) (f a, g b) /
        (p.leftMarginal.map f (f a) * p.rightMarginal.map g (g b))) :
    p.mutualInformation = (p.map (fun x ↦ (f x.1, g x.2))).mutualInformation := by
  unfold mutualInformation
  rw [leftMarginal_map_pair, rightMarginal_map_pair, ← prod_map_pair]
  apply klDivergence_eq_map_of_ratio
  intro x
  rw [prod_map_pair, prod_apply, prod_apply]
  exact hratio x.1 x.2

variable {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty α] [Nonempty β]

/-- Conditional mutual information averages actual pair mutual information
over the actual conditioning-coordinate marginal. -/
def conditionalMutualInformation (p : FinDist (γ × (α × β))) (hp : p.StrictlyPositive) : ℝ :=
  ∑ z, p.leftMarginal z * (p.conditionalRight hp z).mutualInformation

theorem conditionalMutualInformation_nonneg (p : FinDist (γ × (α × β))) (hp : p.StrictlyPositive) :
    0 ≤ p.conditionalMutualInformation hp :=
  Finset.sum_nonneg fun z _ ↦ mul_nonneg (p.leftMarginal.nonneg z)
    (mutualInformation_nonneg _ (p.conditionalRight_positive hp z))

theorem conditionalMutualInformation_le_log_card_right
    (p : FinDist (γ × (α × β))) (hp : p.StrictlyPositive) :
    p.conditionalMutualInformation hp ≤ Real.log (Fintype.card β) := by
  calc
    _ ≤ ∑ z, p.leftMarginal z * Real.log (Fintype.card β) :=
      Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_left
        (mutualInformation_le_log_card_right _ (p.conditionalRight_positive hp z)) (p.leftMarginal.nonneg z)
    _ = _ := by rw [← Finset.sum_mul, p.leftMarginal.sum_mass, one_mul]

/-- A uniform posterior pair-information bound survives actual averaging. -/
theorem le_conditionalMutualInformation (p : FinDist (γ × (α × β))) (hp : p.StrictlyPositive)
    (c : ℝ) (hc : ∀ z, c ≤ (p.conditionalRight hp z).mutualInformation) :
    c ≤ p.conditionalMutualInformation hp := by
  calc
    c = ∑ z, p.leftMarginal z * c := by rw [← Finset.sum_mul, p.leftMarginal.sum_mass, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_left (hc z) (p.leftMarginal.nonneg z)

end
end ForestSampling.FinDist
