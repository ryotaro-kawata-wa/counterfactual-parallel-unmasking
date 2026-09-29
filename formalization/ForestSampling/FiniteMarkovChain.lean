import ForestSampling.FiniteKL

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FiniteMarkovChain

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- Retained head/tail outcomes are in bijection with the complete finite
configuration; this is an explicit coordinate equivalence. -/
def consJointEquiv (n : ℕ) : ((_a : V) × (Fin n → V)) ≃ (Fin (n + 1) → V) where
  toFun z := Fin.cons z.1 z.2
  invFun x := ⟨x 0, Fin.tail x⟩
  left_inv z := by cases z; simp
  right_inv x := by ext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

/-- Draw `n` future states from a fixed initial state using the actual
transition laws, retaining the whole finite path. -/
def continuation (K : V → FinDist V) (initial : V) : (n : ℕ) → FinDist (Fin n → V)
  | 0 => FinDist.dirac Fin.elim0
  | n + 1 =>
      (FinDist.sigmaJoint (K initial) (fun a ↦ continuation K a n)).map (consJointEquiv n)

/-- The actual finite Markov-chain law, including the empty configuration.
For a nonempty path, the first state has law `pi`. -/
def law (π : FinDist V) (K : V → FinDist V) : (n : ℕ) → FinDist (Fin n → V)
  | 0 => FinDist.dirac Fin.elim0
  | n + 1 =>
      (FinDist.sigmaJoint π (fun a ↦ continuation K a n)).map (consJointEquiv n)

@[simp] theorem continuation_apply_zero (K : V → FinDist V) (initial : V) (x : Fin 0 → V) :
    continuation K initial 0 x = 1 := by
  have hx : x = Fin.elim0 := Subsingleton.elim _ _
  simp only [continuation, FinDist.dirac_apply, hx, ite_true]

@[simp] theorem continuation_apply_succ (K : V → FinDist V) (initial : V)
    (n : ℕ) (x : Fin (n + 1) → V) :
    continuation K initial (n + 1) x = K initial (x 0) * continuation K (x 0) n (Fin.tail x) := by
  rw [continuation, FinDist.map_equiv_apply]
  rfl

@[simp] theorem law_apply_succ (π : FinDist V) (K : V → FinDist V)
    (n : ℕ) (x : Fin (n + 1) → V) :
    law π K (n + 1) x = π (x 0) * continuation K (x 0) n (Fin.tail x) := by
  rw [law, FinDist.map_equiv_apply]
  rfl

theorem continuation_positive (K : V → FinDist V) (hK : ∀ a, (K a).StrictlyPositive)
    (initial : V) (n : ℕ) : (continuation K initial n).StrictlyPositive := by
  induction n generalizing initial with
  | zero => intro x; rw [continuation_apply_zero]; exact zero_lt_one
  | succ n ih =>
      intro x
      rw [continuation_apply_succ]
      exact mul_pos (hK initial (x 0)) (ih (x 0) (Fin.tail x))

theorem law_positive (π : FinDist V) (K : V → FinDist V) (hπ : π.StrictlyPositive)
    (hK : ∀ a, (K a).StrictlyPositive) (n : ℕ) : (law π K n).StrictlyPositive := by
  cases n with
  | zero =>
      intro x
      have hx : x = Fin.elim0 := Subsingleton.elim _ _
      simp [law, FinDist.dirac_apply, hx]
  | succ n =>
      intro x
      rw [law_apply_succ]
      exact mul_pos (hπ (x 0)) (continuation_positive K hK (x 0) n (Fin.tail x))

/-- The constructed future law has the product density of the actual
successive transitions, with no assumed Markov factorization premise. -/
theorem continuation_tail_apply (K : V → FinDist V) (n : ℕ) (x : Fin (n + 1) → V) :
    continuation K (x 0) n (Fin.tail x) = ∏ i : Fin n, K (x i.castSucc) (x i.succ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [continuation_apply_succ, Fin.prod_univ_succ]
      rw [ih (Fin.tail x)]
      rfl

/-- The exact manuscript path density, obtained from the normalized
sequential construction rather than postulated as a probability mass. -/
theorem law_apply (π : FinDist V) (K : V → FinDist V) (n : ℕ) (x : Fin (n + 1) → V) :
    law π K (n + 1) x = π (x 0) * ∏ i : Fin n, K (x i.castSucc) (x i.succ) := by
  rw [law_apply_succ, continuation_tail_apply]

/-- Finite expectation under the constructed chain splits into its initial
state and the normalized conditional continuation. -/
theorem expectation_law_succ (π : FinDist V) (K : V → FinDist V) (n : ℕ)
    (f : (Fin (n + 1) → V) → ℝ) :
    (∑ x, law π K (n + 1) x * f x) =
      ∑ a, π a * ∑ tail, continuation K a n tail * f (Fin.cons a tail) := by
  rw [← (consJointEquiv (V := V) n).sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ tail, law π K (n + 1) (Fin.cons a tail) * f (Fin.cons a tail)) = _
  simp only [law_apply_succ, Fin.cons_zero, Fin.tail_cons, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  ring

theorem expectation_continuation_succ (K : V → FinDist V) (initial : V) (n : ℕ)
    (f : (Fin (n + 1) → V) → ℝ) :
    (∑ x, continuation K initial (n + 1) x * f x) =
      ∑ a, K initial a * ∑ tail, continuation K a n tail * f (Fin.cons a tail) :=
  expectation_law_succ (K initial) K n f

omit [DecidableEq V] in
/-- Stationarity transports every finite one-coordinate observable, not
just a chosen collection of token indicators. -/
theorem stationary_sum (π : FinDist V) (K : V → FinDist V)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) (f : V → ℝ) :
    (∑ a, π a * ∑ b, K a b * f b) = ∑ b, π b * f b := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hstationary]

private theorem expectation_const {α : Type*} [Fintype α] (p : FinDist α) (c : ℝ) :
    (∑ a, p a * c) = c := by rw [← Finset.sum_mul, p.sum_mass, one_mul]

/-- Averaging the start of a conditional chain under a stationary law
leaves each subsequent coordinate stationary, regardless of path length. -/
theorem stationary_continuation_expectation (π : FinDist V) (K : V → FinDist V)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b)
    (n : ℕ) (i : Fin n) (f : V → ℝ) :
    (∑ initial, π initial * ∑ x, continuation K initial n x * f (x i)) =
      ∑ a, π a * f a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      simp_rw [expectation_continuation_succ]
      rw [stationary_sum π K hstationary]
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp only [Fin.cons_zero, expectation_const]
      · simp only [Fin.cons_succ]
        exact ih j

/-- Every actual coordinate of the normalized stationary Markov chain has
the initial stationary law, proved from the transition equation. -/
theorem stationary_law_expectation (π : FinDist V) (K : V → FinDist V)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b)
    (n : ℕ) (i : Fin n) (f : V → ℝ) :
    (∑ x, law π K n x * f (x i)) = ∑ a, π a * f a := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      rw [expectation_law_succ]
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp only [Fin.cons_zero, expectation_const]
      · simp only [Fin.cons_succ]
        exact stationary_continuation_expectation π K hstationary n j f

theorem stationary_law_marginal (π : FinDist V) (K : V → FinDist V)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) (n : ℕ) (i : Fin n) :
    (law π K n).map (fun x ↦ x i) = π := by
  classical
  ext b
  rw [FinDist.map_apply]
  have hh := stationary_law_expectation π K hstationary n i (fun a ↦ if a = b then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh

end
end FiniteMarkovChain
end ForestSampling
