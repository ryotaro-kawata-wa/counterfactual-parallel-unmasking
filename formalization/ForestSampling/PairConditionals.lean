import ForestSampling.LocalMarkov

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace CompleteBoundary

variable {N : ℕ} {V : Type*} [DecidableEq V]

/-- Split a configuration into the two distinguished values and the
complete outside boundary; this is an explicit finite-coordinate bijection. -/
def pairSplitEquiv {i j : Position N} (hij : i ≠ j) :
    Configuration N V ≃ ((V × V) × CompleteBoundary N V i j) where
  toFun x := ((x i, x j), fun k ↦ x k)
  invFun z := extension i j z.1.1 z.1.2 z.2
  left_inv x := by
    funext k
    by_cases hki : k = i
    · subst k; simp [extension]
    · by_cases hkj : k = j
      · subst k; simp [extension, hij.symm]
      · simp [extension, hki, hkj]
  right_inv z := by
    rcases z with ⟨⟨a, b⟩, z⟩
    apply Prod.ext
    · apply Prod.ext <;> simp [extension, hij.symm]
    · funext k; simp [extension, k.2.1, k.2.2]

end CompleteBoundary

namespace MaskedState

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem agrees_pair_extension_iff (y : MaskedState N V) {i j : Position N}
    (hi : y i = none) (hj : y j = none) (a b a' b' : V)
    (z : CompleteBoundary N V i j) :
    y.Agrees (CompleteBoundary.extension i j a b z) ↔
      y.Agrees (CompleteBoundary.extension i j a' b' z) := by
  have haux (a b a' b' : V) :
      y.Agrees (CompleteBoundary.extension i j a b z) →
      y.Agrees (CompleteBoundary.extension i j a' b' z) := by
    intro hh k c hkc
    have hki : k ≠ i := by intro h; subst k; simp [hi] at hkc
    have hkj : k ≠ j := by intro h; subst k; simp [hj] at hkc
    simpa [CompleteBoundary.extension, hki, hkj] using hh k c hkc
  exact ⟨haux a b a' b', haux a' b' a b⟩

/-- The actual observed-history pair event sums over just its outside
coordinates, without assuming conditional independence. -/
theorem eventMass_agrees_pair (p : FinDist (Configuration N V))
    (y : MaskedState N V) {i j : Position N} (hij : i ≠ j) (a b : V) :
    p.eventMass (fun x ↦ y.Agrees x ∧ (x i, x j) = (a, b)) =
      ∑ z : CompleteBoundary N V i j,
        if y.Agrees (CompleteBoundary.extension i j a b z)
          then p (CompleteBoundary.extension i j a b z) else 0 := by
  classical
  unfold FinDist.eventMass
  rw [← (CompleteBoundary.pairSplitEquiv (V := V) hij).symm.sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  change (∑ ab : V × V, if y.Agrees (CompleteBoundary.extension i j ab.1 ab.2 z) ∧
    ((CompleteBoundary.extension i j ab.1 ab.2 z) i,
     (CompleteBoundary.extension i j ab.1 ab.2 z) j) = (a, b)
      then p (CompleteBoundary.extension i j ab.1 ab.2 z) else 0) = _
  simp only [CompleteBoundary.extension, dite_true, hij.symm, dite_false]
  rw [Finset.sum_eq_single (a, b)]
  · simp
  · intro ab _ hab
    simp [hab]
  · simp

variable [Nonempty V]

/-- Actual joint conditional of two masked coordinates given an arbitrary
observed history. Its definition is the ordinary finite conditional map. -/
noncomputable def exactPair (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (y : MaskedState N V) (i j : Position N) : FinDist (V × V) :=
  p.conditionalMap y.Agrees (y.probability_pos p hp) (fun x ↦ (x i, x j))

theorem exactPair_positive (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (y : MaskedState N V) {i j : Position N} (hij : i ≠ j)
    (hi : y i = none) (hj : y j = none) : (y.exactPair p hp i j).StrictlyPositive := by
  apply p.conditionalMap_strictlyPositive hp
  intro ab
  let x := y.completion (Classical.choice (inferInstance : Nonempty V))
  let z : CompleteBoundary N V i j := fun k ↦ x k
  refine ⟨CompleteBoundary.extension i j ab.1 ab.2 z, ?_, ?_⟩
  · intro k c hkc
    have hki : k ≠ i := by intro h; subst k; simp [hi] at hkc
    have hkj : k ≠ j := by intro h; subst k; simp [hj] at hkc
    simpa [CompleteBoundary.extension, hki, hkj, z, x] using
      y.completion_agrees (Classical.choice (inferInstance : Nonempty V)) k c hkc
  · simp [CompleteBoundary.extension, hij.symm]

end MaskedState
end ForestSampling
