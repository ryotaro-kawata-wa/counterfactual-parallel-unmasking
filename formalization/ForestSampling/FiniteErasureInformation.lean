import ForestSampling.FiniteInformation

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.FinDist
noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Independent erasure of one finite observation; `none` is the mask and
`some a` retains the actual observed value. -/
def erase (p : FinDist α) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : FinDist (Option α) where
  mass x := match x with | none => 1 - q | some a => q * p a
  nonneg x := by
    cases x with
    | none => exact sub_nonneg.mpr hq1
    | some a => exact mul_nonneg hq0 (p.nonneg a)
  sum_mass := by
    rw [Fintype.sum_option]
    change (1 - q) + (∑ a, q * p a) = 1
    rw [← Finset.mul_sum, p.sum_mass]
    ring

@[simp] theorem erase_none (p : FinDist α) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    p.erase q hq0 hq1 none = 1 - q := rfl

@[simp] theorem erase_some (p : FinDist α) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (a : α) :
    p.erase q hq0 hq1 (some a) = q * p a := rfl

/-- The actual pair law under two independent erasure coins, independent
of the original pair. Each of the four mask cases has its full probability. -/
def erasePair (p : FinDist (α × β)) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    FinDist (Option α × Option β) where
  mass x := match x.1, x.2 with
    | none, none => (1-q)^2
    | some a, none => q*(1-q)*p.leftMarginal a
    | none, some b => q*(1-q)*p.rightMarginal b
    | some a, some b => q^2*p (a,b)
  nonneg x := by
    obtain ⟨a,b⟩ := x
    cases a with
    | none =>
        cases b with
        | none => exact sq_nonneg _
        | some b => exact mul_nonneg (mul_nonneg hq0 (sub_nonneg.mpr hq1)) (p.rightMarginal.nonneg b)
    | some a =>
        cases b with
        | none => exact mul_nonneg (mul_nonneg hq0 (sub_nonneg.mpr hq1)) (p.leftMarginal.nonneg a)
        | some b => exact mul_nonneg (sq_nonneg q) (p.nonneg (a,b))
  sum_mass := by
    rw [Fintype.sum_prod_type, Fintype.sum_option]
    simp only [Fintype.sum_option]
    change (1-q)^2 + (∑ b, q*(1-q)*p.rightMarginal b) +
      (∑ a, (q*(1-q)*p.leftMarginal a + ∑ b, q^2*p (a,b))) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, p.rightMarginal.sum_mass,
      ← Finset.mul_sum, p.leftMarginal.sum_mass]
    simp_rw [← Finset.mul_sum]
    rw [← Fintype.sum_prod_type, p.sum_mass]
    ring

@[simp] theorem erasePair_leftMarginal (p : FinDist (α × β)) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (p.erasePair q hq0 hq1).leftMarginal = p.leftMarginal.erase q hq0 hq1 := by
  ext a
  rw [leftMarginal_apply, Fintype.sum_option]
  cases a with
  | none =>
      change (1-q)^2 + (∑ b, q*(1-q)*p.rightMarginal b) = 1-q
      rw [← Finset.mul_sum, p.rightMarginal.sum_mass]
      ring
  | some a =>
      change q*(1-q)*p.leftMarginal a + (∑ b, q^2*p (a,b)) = q*p.leftMarginal a
      rw [← Finset.mul_sum, ← leftMarginal_apply]
      ring

@[simp] theorem erasePair_rightMarginal (p : FinDist (α × β)) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (p.erasePair q hq0 hq1).rightMarginal = p.rightMarginal.erase q hq0 hq1 := by
  ext b
  rw [rightMarginal_apply, Fintype.sum_option]
  cases b with
  | none =>
      change (1-q)^2 + (∑ a, q*(1-q)*p.leftMarginal a) = 1-q
      rw [← Finset.mul_sum, p.leftMarginal.sum_mass]
      ring
  | some b =>
      change q*(1-q)*p.rightMarginal b + (∑ a, q^2*p (a,b)) = q*p.rightMarginal b
      rw [← Finset.mul_sum, ← rightMarginal_apply]
      ring

theorem erasePair_positive [Nonempty α] [Nonempty β] (p : FinDist (α × β))
    (hp : p.StrictlyPositive) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (p.erasePair q hq0.le hq1.le).StrictlyPositive := by
  intro x
  obtain ⟨a,b⟩ := x
  have hmask : 0 < 1-q := by linarith
  have hl := p.leftMarginal_positive hp
  have hr := p.rightMarginal_positive hp
  cases a with
  | none =>
      cases b with
      | none => exact sq_pos_of_pos hmask
      | some b => exact mul_pos (mul_pos hq0 hmask) (hr b)
  | some a =>
      cases b with
      | none => exact mul_pos (mul_pos hq0 hmask) (hl a)
      | some b => exact mul_pos (sq_pos_of_pos hq0) (hp (a,b))

/-- The pair likelihood ratio is one as soon as either endpoint is erased;
when both are retained, the two independent coin weights cancel exactly. -/
theorem erasePair_likelihood_ratio [Nonempty α] [Nonempty β] (p : FinDist (α × β))
    (hp : p.StrictlyPositive) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (a : Option α) (b : Option β) :
    p.erasePair q hq0.le hq1.le (a,b) /
      (p.leftMarginal.erase q hq0.le hq1.le a * p.rightMarginal.erase q hq0.le hq1.le b) =
      match a,b with | some x, some y => p (x,y)/(p.leftMarginal x * p.rightMarginal y) | _,_ => 1 := by
  have hmask : 1-q ≠ 0 := by linarith
  have hl : ∀ a, p.leftMarginal a ≠ 0 := fun a ↦ (p.leftMarginal_positive hp a).ne'
  have hr : ∀ b, p.rightMarginal b ≠ 0 := fun b ↦ (p.rightMarginal_positive hp b).ne'
  cases a <;> cases b <;> simp only [erasePair, erase]
  all_goals field_simp [hq0.ne', hmask, hl, hr]
  all_goals first | exact div_self (hl _) | exact div_self (hr _)

/-- Independent endpoint erasure multiplies the actual pair mutual
information by exactly the probability that both endpoints remain visible. -/
theorem mutualInformation_erasePair [Nonempty α] [Nonempty β] (p : FinDist (α × β))
    (hp : p.StrictlyPositive) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (p.erasePair q hq0.le hq1.le).mutualInformation = q^2 * p.mutualInformation := by
  unfold mutualInformation klDivergence
  rw [erasePair_leftMarginal, erasePair_rightMarginal, Fintype.sum_prod_type]
  simp only [prod_apply, erasePair_likelihood_ratio p hp q hq0 hq1]
  rw [Fintype.sum_option]
  simp only [Fintype.sum_option, Real.log_one, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  change (∑ a, ∑ b, q^2*p (a,b) * Real.log (p (a,b)/(p.leftMarginal a*p.rightMarginal b))) = _
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [prod_apply]
  ring

/-- The explicit erasure law is the actual mixture of independent erasure
channels applied to each possible original observation. -/
theorem bind_dirac_erase (p : FinDist α) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    p.bind (fun a ↦ (dirac a).erase q hq0 hq1) = p.erase q hq0 hq1 := by
  ext x
  cases x with
  | none => simp [bind_apply, ← Finset.sum_mul, p.sum_mass]
  | some b =>
      simp only [bind_apply, erase_some, dirac_apply]
      simp [mul_ite, mul_comm]

/-- Two independent endpoint channels produce precisely the four-case
pair erasure law, including the cases in which only one value is observed. -/
theorem bind_dirac_erase_pair (p : FinDist (α × β))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    p.bind (fun ab ↦ ((dirac ab.1).erase q hq0 hq1).prod
      ((dirac ab.2).erase q hq0 hq1)) = p.erasePair q hq0 hq1 := by
  ext x
  obtain ⟨a,b⟩ := x
  cases a with
  | none =>
      cases b with
      | none =>
          simp only [bind_apply, prod_apply, erase_none]
          rw [← Finset.sum_mul, p.sum_mass]
          simp [erasePair, pow_two]
      | some b =>
          simp only [bind_apply, prod_apply, erase_none, erase_some, dirac_apply,
            Fintype.sum_prod_type, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_one]
          change (∑ a, p (a,b) * ((1-q)*q)) = q*(1-q)*p.rightMarginal b
          rw [← Finset.sum_mul, rightMarginal_apply]
          ring
  | some a =>
      cases b with
      | none =>
          simp only [bind_apply, prod_apply, erase_none, erase_some, dirac_apply,
            Fintype.sum_prod_type]
          rw [Finset.sum_comm]
          simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
            Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_one]
          change (∑ b, p (a,b) * (q*(1-q))) = q*(1-q)*p.leftMarginal a
          rw [← Finset.sum_mul, leftMarginal_apply]
          ring
      | some b =>
          simp [bind_apply, prod_apply, dirac_apply, Fintype.sum_prod_type,
            mul_ite, ite_mul, erasePair, pow_two, mul_comm, mul_left_comm]

end
end ForestSampling.FinDist
