import ForestSampling.FiniteEntropy

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FiniteMarkovChain

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

def meanTransitionEntropy (π : FinDist V) (K : V → FinDist V) : ℝ :=
  ∑ a, π a * FinDist.entropy (K a)

theorem entropy_law_succ (π : FinDist V) (K : V → FinDist V)
    (hπ : π.StrictlyPositive) (hK : ∀ a, (K a).StrictlyPositive) (n : ℕ) :
    FinDist.entropy (law π K (n + 1)) = FinDist.entropy π +
      ∑ a, π a * FinDist.entropy (continuation K a n) := by
  rw [law, FinDist.entropy_map_equiv,
    FinDist.entropy_sigmaJoint π _ hπ (fun a ↦ continuation_positive K hK a n)]

theorem entropy_continuation_succ (K : V → FinDist V)
    (hK : ∀ a, (K a).StrictlyPositive) (a : V) (n : ℕ) :
    FinDist.entropy (continuation K a (n + 1)) = FinDist.entropy (K a) +
      ∑ b, K a b * FinDist.entropy (continuation K b n) :=
  entropy_law_succ (K a) K (hK a) hK n

theorem mean_continuation_entropy (π : FinDist V) (K : V → FinDist V)
    (hK : ∀ a, (K a).StrictlyPositive)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) (n : ℕ) :
    (∑ a, π a * FinDist.entropy (continuation K a n)) =
      n * meanTransitionEntropy π K := by
  induction n with
  | zero => simp [continuation]
  | succ n ih =>
      simp_rw [entropy_continuation_succ K hK, mul_add]
      rw [Finset.sum_add_distrib, stationary_sum π K hstationary, ih]
      change meanTransitionEntropy π K + n * meanTransitionEntropy π K = _
      push_cast
      ring

theorem entropy_law_stationary (π : FinDist V) (K : V → FinDist V)
    (hπ : π.StrictlyPositive) (hK : ∀ a, (K a).StrictlyPositive)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) (n : ℕ) :
    FinDist.entropy (law π K (n + 1)) =
      FinDist.entropy π + n * meanTransitionEntropy π K := by
  rw [entropy_law_succ π K hπ hK, mean_continuation_entropy π K hK hstationary]

/-- The actual two-step transition obtained by marginalizing its middle
state, rather than postulating a separate bridge kernel. -/
def twoStep (K : V → FinDist V) (a : V) : FinDist V := (K a).bind K

omit [DecidableEq V] in
theorem twoStep_positive [Nonempty V] (K : V → FinDist V)
    (hK : ∀ a, (K a).StrictlyPositive) (a : V) : (twoStep K a).StrictlyPositive := by
  intro b
  exact Finset.sum_pos (fun c _ ↦ mul_pos (hK a c) (hK c b)) Finset.univ_nonempty

omit [DecidableEq V] in
theorem twoStep_stationary (π : FinDist V) (K : V → FinDist V)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) (b : V) :
    (∑ a, π a * twoStep K a b) = π b := by
  simp only [twoStep, FinDist.bind_apply]
  rw [stationary_sum π K hstationary]
  exact hstationary b

/-- After deleting the first future coordinate, the remaining chain has
one two-step transition followed by the ordinary transition entropy. -/
theorem mean_twoStep_law_entropy [Nonempty V] (π : FinDist V) (K : V → FinDist V)
    (hK : ∀ a, (K a).StrictlyPositive)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) (n : ℕ) :
    (∑ a, π a * FinDist.entropy (law (twoStep K a) K (n + 1))) =
      meanTransitionEntropy π (twoStep K) + n * meanTransitionEntropy π K := by
  simp_rw [entropy_law_succ _ K (twoStep_positive K hK _) hK, mul_add]
  rw [Finset.sum_add_distrib, stationary_sum π (twoStep K) (twoStep_stationary π K hstationary),
    mean_continuation_entropy π K hK hstationary]
  rfl

end
end FiniteMarkovChain
end ForestSampling
