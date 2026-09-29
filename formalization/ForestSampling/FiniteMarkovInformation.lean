import ForestSampling.FiniteMarkovChain
import ForestSampling.ScreeningPreprocess

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling

namespace FinDist

variable {V : Type*} [Fintype V]

/-- Distinct strictly positive finite laws have strictly positive forward
KL. The proof uses the already verified KL-to-Hellinger and TV bounds. -/
theorem klDivergence_pos_of_ne (p q : FinDist V) (hp : p.StrictlyPositive)
    (hq : q.StrictlyPositive) (hne : p ≠ q) : 0 < klDivergence p q := by
  classical
  by_contra h
  have hk : klDivergence p q ≤ 0 := le_of_not_gt h
  have hh : sqHellinger p q = 0 := by
    have hb := sqHellinger_le_half_klDivergence p q hp hq
    have hn := sqHellinger_nonneg p q
    linarith
  have ht : tv p q = 0 := by
    have hb := tv_le_sqrt_two_mul_sqHellinger p q
    rw [hh, mul_zero, Real.sqrt_zero] at hb
    exact le_antisymm hb (tv_nonneg p q)
  apply hne
  ext a
  have ha := abs_apply_sub_le_tv p q a
  rw [ht] at ha
  exact sub_eq_zero.mp ((abs_eq_zero).mp (le_antisymm ha (abs_nonneg _)))

end FinDist

namespace FiniteMarkovChain

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- An independent-transition chain is exactly the product law on its
retained coordinates, including the empty path. -/
theorem continuation_constant (π : FinDist V) (initial : V) (n : ℕ) :
    continuation (fun _ ↦ π) initial n = FinDist.piProduct (fun _ : Fin n ↦ π) := by
  ext x
  induction n generalizing initial with
  | zero => simp [FinDist.piProduct_apply]
  | succ n ih =>
      rw [continuation_apply_succ, ih, FinDist.piProduct_apply, FinDist.piProduct_apply,
        Fin.prod_univ_succ]
      rfl

theorem law_constant (π : FinDist V) (n : ℕ) :
    law π (fun _ ↦ π) n = FinDist.piProduct (fun _ : Fin n ↦ π) := by
  cases n with
  | zero =>
      ext x
      have hx : x = Fin.elim0 := Subsingleton.elim _ _
      simp [law, FinDist.dirac_apply, hx, FinDist.piProduct_apply]
  | succ n =>
      ext x
      rw [law_apply_succ, continuation_constant, FinDist.piProduct_apply,
        FinDist.piProduct_apply, Fin.prod_univ_succ]
      rfl

/-- KL accumulated by a conditional continuation obeys the exact finite
transition recursion, under the reference transition probabilities. -/
theorem continuation_kl_succ (π : FinDist V) (K : V → FinDist V)
    (hπ : π.StrictlyPositive) (hK : ∀ a, (K a).StrictlyPositive)
    (initial : V) (n : ℕ) :
    FinDist.klDivergence (continuation K initial (n + 1))
      (continuation (fun _ ↦ π) initial (n + 1)) =
      FinDist.klDivergence (K initial) π +
        ∑ a, K initial a * FinDist.klDivergence (continuation K a n)
          (continuation (fun _ ↦ π) a n) := by
  rw [continuation, continuation, FinDist.klDivergence_map_equiv,
    FinDist.klDivergence_sigmaJoint (K initial) π _ _ (hK initial) hπ]
  · exact fun a ↦ continuation_positive K hK a n
  · exact fun a ↦ continuation_positive (fun _ ↦ π) (fun _ ↦ hπ) a n

/-- Stationarity makes the mean local divergence identical at every
transition, so the exact continuation KL is linear in the path length. -/
theorem mean_continuation_kl (π : FinDist V) (K : V → FinDist V)
    (hπ : π.StrictlyPositive) (hK : ∀ a, (K a).StrictlyPositive)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) (n : ℕ) :
    (∑ initial, π initial * FinDist.klDivergence (continuation K initial n)
      (continuation (fun _ ↦ π) initial n)) =
      n * (∑ a, π a * FinDist.klDivergence (K a) π) := by
  induction n with
  | zero => simp [continuation, FinDist.klDivergence_self]
  | succ n ih =>
      simp_rw [continuation_kl_succ π K hπ hK, mul_add]
      rw [Finset.sum_add_distrib, stationary_sum π K hstationary, ih]
      push_cast
      ring

/-- Exact total correlation of every nonempty stationary finite Markov
chain: one copy of the adjacent-pair mutual information per edge. -/
theorem totalCorrelation_law (π : FinDist V) (K : V → FinDist V)
    (hπ : π.StrictlyPositive) (hK : ∀ a, (K a).StrictlyPositive)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) (n : ℕ) :
    FinDist.totalCorrelation (law π K (n + 1)) =
      n * (∑ a, π a * FinDist.klDivergence (K a) π) := by
  have hmarg : (law π K (n + 1)).piMarginal = fun _ ↦ π := by
    funext i
    exact stationary_law_marginal π K hstationary _ i
  rw [FinDist.totalCorrelation, hmarg, ← law_constant]
  rw [law, law, FinDist.klDivergence_map_equiv,
    FinDist.klDivergence_sigmaJoint π π _ _ hπ hπ]
  · rw [FinDist.klDivergence_self, zero_add]
    exact mean_continuation_kl π K hπ hK hstationary n
  · exact fun a ↦ continuation_positive K hK a n
  · exact fun a ↦ continuation_positive (fun _ ↦ π) (fun _ ↦ hπ) a n

end
end FiniteMarkovChain
end ForestSampling
