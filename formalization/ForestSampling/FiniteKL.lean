import ForestSampling.AdaptiveMidpoint

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling
namespace FinDist

/-!
# Finite forward KL calculus

The first argument is the reference law and the second is the generated law.
Logarithmic identities below require strict positivity explicitly; the real
valued definition alone does not encode infinite KL at zero denominator mass.
-/

noncomputable section

variable {α : Type*} [Fintype α]

/-- Finite forward KL with natural logarithms. Positivity hypotheses are
required for its information-theoretic identities and bounds below. -/
def klDivergence (p q : FinDist α) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

/-- Self-divergence is zero, including atoms of mass zero. -/
@[simp]
theorem klDivergence_self (p : FinDist α) : klDivergence p p = 0 := by
  unfold klDivergence
  apply Finset.sum_eq_zero
  intro a _
  by_cases hpa : p a = 0 <;> simp [hpa]

/-- The exponential likelihood-ratio expression for a single affinity term. -/
theorem weighted_exp_half_log_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * Real.exp (Real.log (b / a) / 2) = Real.sqrt (a * b) := by
  rw [Real.exp_half, Real.exp_log (div_pos hb ha)]
  calc
    a * Real.sqrt (b / a) = Real.sqrt (a ^ 2) * Real.sqrt (b / a) := by
      rw [Real.sqrt_sq ha.le]
    _ = Real.sqrt (a ^ 2 * (b / a)) := (Real.sqrt_mul (sq_nonneg a) _).symm
    _ = Real.sqrt (a * b) := by
      congr 1
      field_simp

/-- Finite Jensen gives the exponential KL-to-affinity bound used in the
manuscript before relaxing it to a linear Hellinger estimate. -/
theorem exp_neg_half_klDivergence_le_affinity (p q : FinDist α)
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive) :
    Real.exp (-klDivergence p q / 2) ≤ affinity p q := by
  have hj := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := fun a ↦ p a) (p := fun a ↦ Real.log (q a / p a) / 2)
    (fun a _ ↦ p.nonneg a) p.sum_mass (fun _ _ ↦ Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have hleft : (∑ a, p a * (Real.log (q a / p a) / 2)) =
      -klDivergence p q / 2 := by
    calc
      (∑ a, p a * (Real.log (q a / p a) / 2)) =
          ∑ a, -(p a * Real.log (p a / q a)) / 2 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Real.log_div (ne_of_gt (hq a)) (ne_of_gt (hp a)),
          Real.log_div (ne_of_gt (hp a)) (ne_of_gt (hq a))]
        ring
      _ = -klDivergence p q / 2 := by
        rw [← Finset.sum_div, Finset.sum_neg_distrib]
        rfl
  have hright : (∑ a, p a * Real.exp (Real.log (q a / p a) / 2)) =
      affinity p q := by
    apply Finset.sum_congr rfl
    intro a _
    exact weighted_exp_half_log_ratio (hp a) (hq a)
  rwa [hleft, hright] at hj

/-- The stronger exponential form of the KL-to-Hellinger inequality. -/
theorem sqHellinger_le_one_sub_exp_neg_half_klDivergence (p q : FinDist α)
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive) :
    sqHellinger p q ≤ 1 - Real.exp (-klDivergence p q / 2) := by
  unfold sqHellinger
  linarith [exp_neg_half_klDivergence_le_affinity p q hp hq]

/-- With this project's normalization, squared Hellinger distance is bounded
by one half of forward KL. -/
theorem sqHellinger_le_half_klDivergence (p q : FinDist α)
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive) :
    sqHellinger p q ≤ klDivergence p q / 2 := by
  have hexp := Real.add_one_le_exp (-klDivergence p q / 2)
  linarith [sqHellinger_le_one_sub_exp_neg_half_klDivergence p q hp hq]

/-- Forward KL is nonnegative for strictly positive finite probability laws. -/
theorem klDivergence_nonneg (p q : FinDist α)
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive) :
    0 ≤ klDivergence p q := by
  linarith [sqHellinger_nonneg p q, sqHellinger_le_half_klDivergence p q hp hq]

/-- Relabeling by an equivalence preserves forward KL exactly. A generic
many-to-one output map would not justify replacing this equality by itself. -/
theorem klDivergence_map_equiv {γ : Type*} [Fintype γ] [DecidableEq γ]
    (p q : FinDist α) (e : α ≃ γ) :
    klDivergence (p.map e) (q.map e) = klDivergence p q := by
  unfold klDivergence
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_equiv_apply, map_equiv_apply]
  simp

variable {β : α → Type*} [∀ a, Fintype (β a)]

/-- Exact forward-KL chain rule on a retained, possibly dependent two-stage
outcome. The continuation divergence is averaged under the reference law. -/
theorem klDivergence_sigmaJoint (p q : FinDist α)
    (k l : (a : α) → FinDist (β a))
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive)
    (hk : ∀ a, (k a).StrictlyPositive) (hl : ∀ a, (l a).StrictlyPositive) :
    klDivergence (sigmaJoint p k) (sigmaJoint q l) =
      klDivergence p q + ∑ a, p a * klDivergence (k a) (l a) := by
  have hlog (a : α) (b : β a) :
      Real.log ((p a * k a b) / (q a * l a b)) =
        Real.log (p a / q a) + Real.log (k a b / l a b) := by
    rw [Real.log_div (mul_ne_zero (hp a).ne' (hk a b).ne')
      (mul_ne_zero (hq a).ne' (hl a b).ne'),
      Real.log_mul (hp a).ne' (hk a b).ne',
      Real.log_mul (hq a).ne' (hl a b).ne',
      Real.log_div (hp a).ne' (hq a).ne',
      Real.log_div (hk a b).ne' (hl a b).ne']
    ring
  unfold klDivergence
  rw [Fintype.sum_sigma, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [sigmaJoint_apply, hlog]
  calc
    (∑ b, p a * k a b * (Real.log (p a / q a) + Real.log (k a b / l a b))) =
        (∑ b, k a b * (p a * Real.log (p a / q a))) +
          p a * ∑ b, k a b * Real.log (k a b / l a b) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = p a * Real.log (p a / q a) +
          p a * ∑ b, k a b * Real.log (k a b / l a b) := by
      rw [← Finset.sum_mul, (k a).sum_mass, one_mul]

section Entropy

/-- Finite entropy, using the real-log convention `0 * log 0 = 0`. -/
def entropy (p : FinDist α) : ℝ := -(∑ a, p a * Real.log (p a))

theorem entropy_nonneg (p : FinDist α) : 0 ≤ entropy p := by
  unfold entropy
  apply neg_nonneg.mpr
  exact Finset.sum_nonpos fun a _ ↦
    mul_nonpos_of_nonneg_of_nonpos (p.nonneg a)
      (Real.log_nonpos (p.nonneg a) (p.mass_le_one a))

/-- Expanding KL separates the reference entropy from its cross-entropy. -/
theorem klDivergence_eq_neg_entropy_sub (p q : FinDist α)
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive) :
    klDivergence p q = -entropy p - ∑ a, p a * Real.log (q a) := by
  unfold klDivergence entropy
  simp only [neg_neg]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [Real.log_div (hp a).ne' (hq a).ne']
  ring

/-- Uniform law on a nonempty finite type. -/
private def entropyUniform [Nonempty α] : FinDist α where
  mass _ := 1 / (Fintype.card α : ℝ)
  nonneg _ := by positivity
  sum_mass := by
    simp [Fintype.card_ne_zero]

private theorem entropyUniform_strictlyPositive [Nonempty α] :
    (entropyUniform : FinDist α).StrictlyPositive := by
  intro a
  exact div_pos zero_lt_one (by exact_mod_cast Fintype.card_pos)

/-- KL to the uniform law is the entropy deficit from the finite alphabet cap. -/
private theorem klDivergence_entropyUniform [Nonempty α] (p : FinDist α)
    (hp : p.StrictlyPositive) :
    klDivergence p entropyUniform = Real.log (Fintype.card α) - entropy p := by
  rw [klDivergence_eq_neg_entropy_sub p entropyUniform hp entropyUniform_strictlyPositive]
  have hcross : (∑ a, p a * Real.log ((entropyUniform : FinDist α) a)) =
      -Real.log (Fintype.card α) := by
    change (∑ a, p a * Real.log (1 / (Fintype.card α : ℝ))) = _
    rw [← Finset.sum_mul, p.sum_mass, one_mul]
    simp
  rw [hcross]
  ring

/-- Entropy of a positive law is at most the log alphabet size. -/
theorem entropy_le_log_card [Nonempty α] (p : FinDist α)
    (hp : p.StrictlyPositive) :
    entropy p ≤ Real.log (Fintype.card α) := by
  have h := klDivergence_nonneg p entropyUniform hp entropyUniform_strictlyPositive
  rw [klDivergence_entropyUniform p hp] at h
  linarith

end Entropy

section Marginals

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

/-- Expectation under a pushforward is expectation of the composed readout. -/
theorem sum_map_mul (p : FinDist α) (f : α → γ) (g : γ → ℝ) :
    (∑ b, p.map f b * g b) = ∑ a, p a * g (f a) := by
  classical
  simp only [map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  exact Fintype.sum_ite_eq (f a) (fun b ↦ p a * g b)

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- A singleton marginal of a law on a finite Cartesian power. -/
def piMarginal (p : FinDist (ι → V)) (i : ι) : FinDist V :=
  p.map (fun x ↦ x i)

theorem piMarginal_strictlyPositive (p : FinDist (ι → V))
    (hp : p.StrictlyPositive) (i : ι) : (p.piMarginal i).StrictlyPositive := by
  apply p.map_strictlyPositive_of_surjective hp (fun x ↦ x i)
  intro a
  exact ⟨fun _ ↦ a, rfl⟩

/-- Product cross-entropy decomposes into singleton cross-entropies, even
when the reference coordinates are dependent. -/
theorem klDivergence_piProduct_eq (p : FinDist (ι → V)) (q : ι → FinDist V)
    (hp : p.StrictlyPositive) (hq : ∀ i, (q i).StrictlyPositive) :
    klDivergence p (piProduct q) =
      -entropy p - ∑ i, ∑ a, p.piMarginal i a * Real.log (q i a) := by
  rw [klDivergence_eq_neg_entropy_sub p (piProduct q) hp
    (piProduct_strictlyPositive hq)]
  congr 1
  calc
    (∑ x, p x * Real.log (piProduct q x)) =
        ∑ x, ∑ i, p x * Real.log (q i (x i)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [piProduct_apply, Real.log_prod (fun i _ ↦ (hq i (x i)).ne'),
        Finset.mul_sum]
    _ = ∑ i, ∑ x, p x * Real.log (q i (x i)) := by rw [Finset.sum_comm]
    _ = ∑ i, ∑ a, p.piMarginal i a * Real.log (q i a) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (p.sum_map_mul (fun x ↦ x i) (fun a ↦ Real.log (q i a))).symm

/-- Total correlation is divergence to the product of the law's own
singleton marginals. -/
def totalCorrelation (p : FinDist (ι → V)) : ℝ :=
  klDivergence p (piProduct p.piMarginal)

/-- Total correlation is the sum of marginal entropies minus joint entropy. -/
theorem totalCorrelation_eq_entropy (p : FinDist (ι → V))
    (hp : p.StrictlyPositive) :
    totalCorrelation p = (∑ i, entropy (p.piMarginal i)) - entropy p := by
  rw [totalCorrelation, klDivergence_piProduct_eq p p.piMarginal hp
    (p.piMarginal_strictlyPositive hp)]
  unfold entropy
  rw [Finset.sum_neg_distrib]
  ring

/-- Inserting the product of the true marginals separates dependence error
from singleton oracle error, with the exact forward-KL direction. -/
theorem klDivergence_piProduct_decomposition (p : FinDist (ι → V))
    (q : ι → FinDist V) (hp : p.StrictlyPositive)
    (hq : ∀ i, (q i).StrictlyPositive) :
    klDivergence p (piProduct q) =
      totalCorrelation p + ∑ i, klDivergence (p.piMarginal i) (q i) := by
  rw [klDivergence_piProduct_eq p q hp hq, totalCorrelation_eq_entropy p hp]
  have hrows : (∑ i, klDivergence (p.piMarginal i) (q i)) =
      -(∑ i, entropy (p.piMarginal i)) -
        ∑ i, ∑ a, p.piMarginal i a * Real.log (q i a) := by
    simp_rw [klDivergence_eq_neg_entropy_sub _ _ (p.piMarginal_strictlyPositive hp _)
      (hq _)]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hrows]
  ring

theorem totalCorrelation_nonneg (p : FinDist (ι → V))
    (hp : p.StrictlyPositive) : 0 ≤ totalCorrelation p :=
  klDivergence_nonneg p (piProduct p.piMarginal) hp
    (piProduct_strictlyPositive (p.piMarginal_strictlyPositive hp))

/-- Dependence cost of a batch is bounded by its coordinate count times the
log vocabulary size, independently of minimum atom mass. -/
theorem totalCorrelation_le_card_mul_log_card [Nonempty V] (p : FinDist (ι → V))
    (hp : p.StrictlyPositive) :
    totalCorrelation p ≤ (Fintype.card ι : ℝ) * Real.log (Fintype.card V) := by
  rw [totalCorrelation_eq_entropy p hp]
  have hmarg : (∑ i, entropy (p.piMarginal i)) ≤
      (Fintype.card ι : ℝ) * Real.log (Fintype.card V) := by
    calc
      (∑ i, entropy (p.piMarginal i)) ≤ ∑ _i : ι, Real.log (Fintype.card V) :=
        Finset.sum_le_sum fun i _ ↦
          entropy_le_log_card (p.piMarginal i) (p.piMarginal_strictlyPositive hp i)
      _ = _ := by simp
  linarith [entropy_nonneg p]

/-- Conditional independence makes the batch's total correlation vanish. -/
theorem totalCorrelation_eq_zero_of_factorizes (p : FinDist (ι → V))
    (hfactor : p = piProduct p.piMarginal) : totalCorrelation p = 0 := by
  unfold totalCorrelation
  rw [← hfactor, klDivergence_self]

/-- A product law has exactly its specified singleton marginals. -/
@[simp]
theorem piMarginal_piProduct (q : ι → FinDist V) (i : ι) :
    (piProduct q).piMarginal i = q i := piProduct_map_eval q i

/-- Independent coordinates have zero total correlation. -/
@[simp]
theorem totalCorrelation_piProduct (q : ι → FinDist V) :
    totalCorrelation (piProduct q) = 0 := by
  have hmarg : (piProduct q).piMarginal = q := by
    funext i
    exact piMarginal_piProduct q i
  unfold totalCorrelation
  rw [hmarg, klDivergence_self]

end Marginals

end

end FinDist
end ForestSampling
