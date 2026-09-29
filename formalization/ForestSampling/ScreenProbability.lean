import ForestSampling.FiniteProbability

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

/-- Number of failed trials in a finite independent family. -/
def badCount (bad : ∀ i, Ω i → Prop) [∀ i, DecidablePred (bad i)]
    (x : ∀ i, Ω i) : ℕ := ∑ i, if bad i (x i) then 1 else 0

/-- Products of coordinate observables factor under the actual product law. -/
theorem piProduct_expect_prod (p : ∀ i, FinDist (Ω i)) (f : ∀ i, Ω i → ℝ) :
    (∑ x, piProduct p x * ∏ i, f i (x i)) = ∏ i, ∑ a, p i a * f i a := by
  simp only [piProduct_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun i a ↦ p i a * f i a).symm

/-- A finite Markov bound stated directly for the chosen event. -/
theorem eventMass_le_of_pointwise (p : FinDist (∀ i, Ω i))
    (E : (∀ i, Ω i) → Prop) [DecidablePred E]
    (f : (∀ i, Ω i) → ℝ) (t : ℝ) (ht : 0 < t)
    (hf : ∀ x, 0 ≤ f x) (hE : ∀ x, E x → t ≤ f x) :
    p.eventMass E ≤ (∑ x, p x * f x) / t := by
  apply (le_div_iff₀ ht).2
  rw [eventMass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x
  · simp only [if_pos hx]
    exact mul_le_mul_of_nonneg_left (hE x hx) (p.nonneg x)
  · simp only [if_neg hx, zero_mul]
    exact mul_nonneg (p.nonneg x) (hf x)

/-- Exact fourth-base moment of the number of independent failed trials. -/
theorem piProduct_four_pow_badCount (p : ∀ i, FinDist (Ω i))
    (bad : ∀ i, Ω i → Prop) [∀ i, DecidablePred (bad i)] :
    (∑ x, piProduct p x * (4 : ℝ) ^ badCount bad x) =
      ∏ i, (1 + 3 * (p i).eventMass (bad i)) := by
  have hpow (x : ∀ i, Ω i) : (4 : ℝ) ^ badCount bad x =
      ∏ i, (if bad i (x i) then (4 : ℝ) else 1) := by
    rw [badCount, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro i _
    split <;> simp_all
  simp_rw [hpow]
  rw [piProduct_expect_prod p (fun i a ↦ if bad i a then 4 else 1)]
  apply Finset.prod_congr rfl
  intro i _
  have hterm (a : Ω i) : p i a * (if bad i a then (4 : ℝ) else 1) =
      p i a + 3 * (if bad i a then p i a else 0) := by
    split <;> ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, (p i).sum_mass]
  rfl

/-- At most one quarter failure probability per independent trial gives a
geometric strict-majority failure bound, including a possible tie. -/
theorem piProduct_majority_failure_le_geometric (p : ∀ i, FinDist (Ω i))
    (bad : ∀ i, Ω i → Prop) [∀ i, DecidablePred (bad i)]
    (hbad : ∀ i, (p i).eventMass (bad i) ≤ 1 / 4) :
    (piProduct p).eventMass (fun x ↦ Fintype.card ι ≤ 2 * badCount bad x) ≤
      (7 / 8 : ℝ) ^ Fintype.card ι := by
  have hmoment : (∑ x, piProduct p x * (4 : ℝ) ^ badCount bad x) ≤
      (7 / 4 : ℝ) ^ Fintype.card ι := by
    rw [piProduct_four_pow_badCount]
    calc
      _ ≤ ∏ _i : ι, (7 / 4 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _
          have := (p i).eventMass_nonneg (bad i)
          positivity
        · intro i _
          linarith [hbad i]
      _ = _ := by rw [Finset.prod_const, Finset.card_univ]
  have hmarkov := (piProduct p).eventMass_le_of_pointwise
    (fun x ↦ Fintype.card ι ≤ 2 * badCount bad x)
    (fun x ↦ (4 : ℝ) ^ badCount bad x) ((2 : ℝ) ^ Fintype.card ι)
    (by positivity) (fun _ ↦ by positivity) (by
      intro x hx
      calc
        (2 : ℝ) ^ Fintype.card ι ≤ 2 ^ (2 * badCount bad x) :=
          pow_le_pow_right₀ (by norm_num) hx
        _ = 4 ^ badCount bad x := by rw [pow_mul]; norm_num)
  calc
    _ ≤ (∑ x, piProduct p x * (4 : ℝ) ^ badCount bad x) /
        (2 : ℝ) ^ Fintype.card ι := hmarkov
    _ ≤ (7 / 4 : ℝ) ^ Fintype.card ι / (2 : ℝ) ^ Fintype.card ι :=
      div_le_div_of_nonneg_right hmoment (by positivity)
    _ = _ := by rw [← div_pow]; norm_num

/-- The exponential bound used by the paper's fresh-color majority screen. -/
theorem piProduct_majority_failure_le_exp (p : ∀ i, FinDist (Ω i))
    (bad : ∀ i, Ω i → Prop) [∀ i, DecidablePred (bad i)]
    (hbad : ∀ i, (p i).eventMass (bad i) ≤ 1 / 4) :
    (piProduct p).eventMass (fun x ↦ Fintype.card ι ≤ 2 * badCount bad x) ≤
      Real.exp (-(Fintype.card ι : ℝ) / 8) := by
  apply (piProduct_majority_failure_le_geometric p bad hbad).trans
  have hbase : (7 / 8 : ℝ) ≤ Real.exp (-(1 / 8 : ℝ)) := by
    have h := Real.add_one_le_exp (-(1 / 8 : ℝ))
    linarith
  calc
    (7 / 8 : ℝ) ^ Fintype.card ι ≤ Real.exp (-(1 / 8 : ℝ)) ^ Fintype.card ι :=
      pow_le_pow_left₀ (by norm_num) hbase _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- The public repetition count allocates an exponential tail to one of B
possible tests. The budget and failure tolerance are strictly positive. -/
theorem exp_repetitions_le_budget (B η : ℝ) (hB : 0 < B) (hη : 0 < η)
    (T : ℕ) (hT : 8 * Real.log (B / η) ≤ (T : ℝ)) :
    Real.exp (-(T : ℝ) / 8) ≤ η / B := by
  have hexp := Real.exp_le_exp.mpr (show -(T : ℝ) / 8 ≤ -Real.log (B / η) by linarith)
  calc
    _ ≤ Real.exp (-Real.log (B / η)) := hexp
    _ = η / B := by rw [Real.exp_neg, Real.exp_log (div_pos hB hη), inv_div]

/-- Ceiling the paper's logarithmic repetition count supplies the same bound. -/
theorem exp_ceil_repetitions_le_budget (B η : ℝ) (hB : 0 < B) (hη : 0 < η) :
    Real.exp (-(⌈8 * Real.log (B / η)⌉₊ : ℝ) / 8) ≤ η / B :=
  exp_repetitions_le_budget B η hB hη _ (Nat.le_ceil _)

end FinDist
end ForestSampling
