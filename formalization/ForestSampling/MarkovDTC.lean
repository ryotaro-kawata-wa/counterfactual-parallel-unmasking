import ForestSampling.MarkovDeletion
import ForestSampling.MarkovEntropy

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

variable {α : Type*} [Fintype α]

theorem entropy_of_subsingleton [Subsingleton α] (p : FinDist α) : entropy p = 0 := by
  classical
  have hnonempty : Nonempty α := by
    by_contra hh
    let : IsEmpty α := not_nonempty_iff.mp hh
    have hs := p.sum_mass
    simp at hs
  let a : α := Classical.choice hnonempty
  let : Unique α := ⟨⟨a⟩, fun b ↦ Subsingleton.elim _ _⟩
  have hp : p (default : α) = 1 := by simpa using p.sum_mass
  simp only [entropy, Finset.univ_unique, Finset.sum_singleton]
  change -(p (default : α) * Real.log (p (default : α))) = 0
  rw [hp, Real.log_one, mul_zero, neg_zero]

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- The actual marginal after forgetting one coordinate. -/
noncomputable def erasedMarginal (p : FinDist (ι → V)) (i : ι) :
    FinDist ({j : ι // j ≠ i} → V) := p.map (fun x j ↦ x j)

/-- Dual total correlation in its standard complementary-marginal entropy
form, equivalent to joint entropy minus the sum of full conditional entropies. -/
noncomputable def dualTotalCorrelation (p : FinDist (ι → V)) : ℝ :=
  (∑ i, entropy (p.erasedMarginal i)) - ((Fintype.card ι : ℝ) - 1) * entropy p

end FinDist

namespace FiniteMarkovChain

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

noncomputable section

omit [Nonempty V] in
private theorem deleteCoordinate_zero_fun (n : ℕ) :
    (deleteCoordinate (V := V) (0 : Fin (n + 1))) = Fin.tail := by
  funext x
  exact deleteCoordinate_zero x

theorem deleted_continuation_positive (K : V → FinDist V)
    (hK : ∀ a, (K a).StrictlyPositive) (a : V) (n : ℕ) (i : Fin (n + 1)) :
    ((continuation K a (n + 1)).map (deleteCoordinate i)).StrictlyPositive :=
  FinDist.map_strictlyPositive_of_surjective _ (continuation_positive K hK a _)
    _ (deleteCoordinate_surjective i)

/-- Deleting the final future state removes one ordinary transition;
deleting any earlier future state replaces one transition by the actual
two-step bridge. The identity is averaged under the stationary start. -/
theorem mean_deleted_continuation_entropy (π : FinDist V) (K : V → FinDist V)
    (hK : ∀ a, (K a).StrictlyPositive)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b)
    (n : ℕ) (i : Fin (n + 1)) :
    (∑ a, π a * FinDist.entropy ((continuation K a (n + 1)).map (deleteCoordinate i))) =
      n * meanTransitionEntropy π K +
        if i = Fin.last n then 0 else meanTransitionEntropy π (twoStep K) - meanTransitionEntropy π K := by
  induction n with
  | zero =>
      have hi : i = Fin.last 0 := by apply Fin.ext; have hh := i.isLt; omega
      simp [FinDist.entropy_of_subsingleton, hi]
  | succ n ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · have hz : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
          intro hh
          have hh' := congrArg Fin.val hh
          simp only [Fin.val_zero, Fin.val_last] at hh'
          omega
        simp only [deleteCoordinate_zero_fun, continuation_map_tail, hz, ite_false]
        change (∑ a, π a * FinDist.entropy (law (twoStep K a) K (n + 1))) = _
        rw [mean_twoStep_law_entropy π K hK hstationary]
        push_cast
        ring
      · simp only [continuation_delete_succ, FinDist.entropy_map_equiv]
        simp_rw [FinDist.entropy_sigmaJoint _ _ (hK _) (fun a ↦ deleted_continuation_positive K hK a n j),
          mul_add]
        rw [Finset.sum_add_distrib, stationary_sum π K hstationary, ih j]
        have hlast : j.succ = Fin.last (n + 1) ↔ j = Fin.last n := by
          rw [← Fin.succ_last, Fin.succ_inj]
        simp only [hlast]
        change meanTransitionEntropy π K + (_ + _) = _
        push_cast
        ring

/-- Entropy of every actual complementary marginal, distinguishing the
two endpoints from interior coordinates without an independence premise. -/
theorem entropy_deleted_law (π : FinDist V) (K : V → FinDist V)
    (hπ : π.StrictlyPositive) (hK : ∀ a, (K a).StrictlyPositive)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b)
    (n : ℕ) (i : Fin (n + 2)) :
    FinDist.entropy ((law π K (n + 2)).map (deleteCoordinate i)) =
      FinDist.entropy π + n * meanTransitionEntropy π K +
        if i = 0 ∨ i = Fin.last (n + 1) then 0
        else meanTransitionEntropy π (twoStep K) - meanTransitionEntropy π K := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [deleteCoordinate_zero_fun, stationary_law_map_tail π K hstationary,
      true_or, ite_true, add_zero]
    exact entropy_law_stationary π K hπ hK hstationary n
  · rw [law_delete_succ, FinDist.entropy_map_equiv,
      FinDist.entropy_sigmaJoint π _ hπ (fun a ↦ deleted_continuation_positive K hK a n j),
      mean_deleted_continuation_entropy π K hK hstationary]
    have hlast : j.succ = Fin.last (n + 1) ↔ j = Fin.last n := by
      rw [← Fin.succ_last, Fin.succ_inj]
    simp only [Fin.succ_ne_zero, false_or, hlast]
    ring

omit [Nonempty V] in
/-- Relabeling the complementary coordinates in increasing order does not
change their entropy. -/
theorem entropy_erasedMarginal (n : ℕ) (p : FinDist (Fin (n + 1) → V)) (i : Fin (n + 1)) :
    FinDist.entropy (p.erasedMarginal i) =
      FinDist.entropy (p.map (deleteCoordinate i)) := by
  let e := Equiv.arrowCongr (finSuccAboveEquiv i).symm (Equiv.refl V)
  have heq : (p.erasedMarginal i).map e = p.map (deleteCoordinate i) := by
    rw [FinDist.erasedMarginal, FinDist.map_comp]
    rfl
  rw [← heq, FinDist.entropy_map_equiv]

/-- Exact DTC of a stationary positive Markov chain, from the actual
complementary marginals. The second coefficient is the increase in
transition entropy caused by skipping one hidden middle state. -/
theorem dualTotalCorrelation_law (π : FinDist V) (K : V → FinDist V)
    (hπ : π.StrictlyPositive) (hK : ∀ a, (K a).StrictlyPositive)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) (n : ℕ) :
    FinDist.dualTotalCorrelation (law π K (n + 2)) =
      (FinDist.entropy π - meanTransitionEntropy π K) +
        n * (meanTransitionEntropy π (twoStep K) - meanTransitionEntropy π K) := by
  unfold FinDist.dualTotalCorrelation
  simp_rw [entropy_erasedMarginal, entropy_deleted_law π K hπ hK hstationary]
  rw [entropy_law_stationary π K hπ hK hstationary]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hz : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro hh
    have hh' := congrArg Fin.val hh
    simp only [Fin.val_zero, Fin.val_last] at hh'
    omega
  have hcast (i : Fin n) : i.castSucc.succ ≠ Fin.last (n + 1) := by
    intro hh
    have hh' : i.castSucc = Fin.last n := Fin.succ_injective _ hh
    exact Fin.castSucc_ne_last i hh'
  simp only [true_or, ite_true, add_zero, Fin.succ_ne_zero, false_or,
    Fin.succ_last, hcast, ite_false, or_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end
end FiniteMarkovChain
end ForestSampling
