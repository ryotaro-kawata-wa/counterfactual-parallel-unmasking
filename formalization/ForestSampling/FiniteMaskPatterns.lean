import ForestSampling.FiniteMaskedInformation

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.FinDist
noncomputable section

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A single fresh mask coin has its stated visibility probability,
independently of the original observation law. -/
theorem erase_visibility_eventMass (p : FinDist α) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (visible : Bool) :
    (p.erase q hq0 hq1).eventMass (fun y ↦ y.isSome = visible) = if visible then q else 1-q := by
  cases visible <;> simp [eventMass, Fintype.sum_option, ← Finset.mul_sum, p.sum_mass]

theorem maskChannel_pattern_eventMass (x : ι → α) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (S : Finset ι) (visible : Bool) :
    (maskChannel x q hq0 hq1).eventMass (fun y ↦ ∀ i ∈ S, (y i).isSome = visible) =
      (if visible then q else 1-q)^S.card := by
  classical
  change (piProduct (fun i : ι ↦ (dirac (x i)).erase q hq0 hq1)).eventMass
    (fun y ↦ ∀ i, i∈S → (y i).isSome=visible) = _
  rw [piProduct_eventMass_forall (fun i : ι ↦ (dirac (x i)).erase q hq0 hq1)
    (fun (i : ι) (a : Option α) ↦ i∈S → a.isSome=visible)]
  calc
    _ = ∏ i, if i∈S then (if visible then q else 1-q) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i∈S
      · simpa only [hi, true_implies, if_true] using
          erase_visibility_eventMass (dirac (x i)) q hq0 hq1 visible
      · simp only [hi, false_implies, if_false, eventMass_true]
    _ = _ := by rw [Fintype.prod_ite_mem]; simp

/-- Finite mixtures preserve event probabilities exactly; the source
configuration may have arbitrary dependence. -/
theorem bind_eventMass (p : FinDist α) (k : α → FinDist β) (E : β → Prop)
    [DecidablePred E] : (p.bind k).eventMass E = ∑ a, p a * (k a).eventMass E := by
  unfold eventMass
  simp only [bind_apply, Finset.mul_sum]
  have hh (b : β) : (if E b then ∑ a, p a*k a b else 0) =
      ∑ a, if E b then p a*k a b else 0 := by split_ifs <;> simp
  simp_rw [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

/-- A bound supported on an event averages to the bound times the event's
actual probability. No independence of source coordinates is assumed. -/
theorem sum_mul_le_eventMass (p : FinDist α) (f : α → ℝ) (E : α → Prop)
    [DecidablePred E] (c : ℝ) (hu : ∀ a, E a → f a ≤ c) (hz : ∀ a, ¬E a → f a=0) :
    (∑ a, p a*f a) ≤ c*p.eventMass E := by
  rw [eventMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : E a
  · simp only [if_pos ha]
    nlinarith [p.nonneg a, hu a ha]
  · simp [ha, hz a ha]

/-- Nonnegative information on a selected event contributes at least the
event probability times its pointwise information lower bound. -/
theorem eventMass_mul_le_sum (p : FinDist α) (f : α → ℝ) (E : α → Prop)
    [DecidablePred E] (c : ℝ) (h0 : ∀ a, 0≤f a) (hl : ∀ a, E a → c≤f a) :
    c*p.eventMass E ≤ ∑ a, p a*f a := by
  rw [eventMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : E a
  · simp only [if_pos ha]
    nlinarith [p.nonneg a, hl a ha]
  · simp only [if_neg ha, mul_zero]
    exact mul_nonneg (p.nonneg a) (h0 a)

end
end ForestSampling.FinDist

namespace ForestSampling.MaskedInformation
noncomputable section
variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The background mask pattern has independent Bernoulli probability
even after averaging over the full dependent source law. -/
theorem backgroundLaw_pattern_eventMass (p : FinDist (Configuration N V)) (i j : Position N)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (S : Finset {k : Position N // k≠i ∧ k≠j}) (visible : Bool) :
    (backgroundLaw p i j q hq0 hq1).eventMass
      (fun y ↦ ∀ k∈S, (y k).isSome = visible) = (if visible then q else 1-q)^S.card := by
  rw [backgroundLaw, FinDist.bind_eventMass]
  simp only [FinDist.maskChannel_pattern_eventMass, ← Finset.sum_mul, p.sum_mass, one_mul]

variable [Nonempty V]

/-- A background-dependent information upper bound is weighted by the
actual probability that every required separator stays masked. -/
theorem maskedPair_information_le_mask_pattern
    (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    {i j : Position N} (hij : i≠j) (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (S : Finset {k : Position N // k≠i ∧ k≠j}) (c : ℝ)
    (hu : ∀ y, ((outsideState i j y).exactPair p hp i j).mutualInformation ≤ c)
    (hz : ∀ y, ¬(∀ k∈S, (y k).isSome=false) →
      ((outsideState i j y).exactPair p hp i j).mutualInformation=0) :
    (maskedPairLaw p hij q hq0.le hq1.le).conditionalMutualInformation
      (maskedPairLaw_positive p hp hij q hq0 hq1) ≤ q^2*c*(1-q)^S.card := by
  classical
  rw [maskedPair_conditionalMutualInformation p hp hij q hq0 hq1]
  have hmean := FinDist.sum_mul_le_eventMass (backgroundLaw p i j q hq0.le hq1.le)
    (fun y ↦ ((outsideState i j y).exactPair p hp i j).mutualInformation)
    (fun y ↦ ∀ k∈S, (y k).isSome=false) c (fun y _ ↦ hu y) hz
  rw [backgroundLaw_pattern_eventMass] at hmean
  simp only [Bool.false_eq_true, ↓reduceIte] at hmean
  nlinarith [mul_le_mul_of_nonneg_left hmean (sq_nonneg q)]

/-- Visible boundary coordinates retain their exact independent-coin
probability when extracting a uniform positive pair-information bound. -/
theorem mask_pattern_le_maskedPair_information
    (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    {i j : Position N} (hij : i≠j) (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (S : Finset {k : Position N // k≠i ∧ k≠j}) (c : ℝ)
    (hl : ∀ y, (∀ k∈S, (y k).isSome=true) →
      c ≤ ((outsideState i j y).exactPair p hp i j).mutualInformation) :
    q^2*c*q^S.card ≤ (maskedPairLaw p hij q hq0.le hq1.le).conditionalMutualInformation
      (maskedPairLaw_positive p hp hij q hq0 hq1) := by
  classical
  rw [maskedPair_conditionalMutualInformation p hp hij q hq0 hq1]
  have hnonneg (y) : 0 ≤ ((outsideState i j y).exactPair p hp i j).mutualInformation := by
    apply FinDist.mutualInformation_nonneg
    apply MaskedState.exactPair_positive p hp _ hij
    · simp [outsideState, CompleteBoundary.extension]
    · simp [outsideState, CompleteBoundary.extension, hij.symm]
  have hmean := FinDist.eventMass_mul_le_sum (backgroundLaw p i j q hq0.le hq1.le)
    (fun y ↦ ((outsideState i j y).exactPair p hp i j).mutualInformation)
    (fun y ↦ ∀ k∈S, (y k).isSome=true) c hnonneg hl
  rw [backgroundLaw_pattern_eventMass] at hmean
  simp only [↓reduceIte] at hmean
  nlinarith [mul_le_mul_of_nonneg_left hmean (sq_nonneg q)]

end
end ForestSampling.MaskedInformation
