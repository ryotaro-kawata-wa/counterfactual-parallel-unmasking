import ForestSampling.FiniteEntropy
import ForestSampling.ProgramMidpoint

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

omit [DecidableEq β] in
/-- A fiberwise deterministic readout retains the first-stage label and
pushes forward only its actual conditional law. -/
theorem sigmaJoint_map_fiber (p : FinDist α) (k : α → FinDist β) (f : β → γ) :
    (sigmaJoint p k).map (fun z ↦ (⟨z.1, f z.2⟩ : (_a : α) × γ)) =
      sigmaJoint p (fun a ↦ (k a).map f) := by
  ext z
  rcases z with ⟨a, c⟩
  rw [map_apply, Fintype.sum_sigma, sigmaJoint_apply, map_apply, Finset.mul_sum]
  rw [Finset.sum_eq_single a]
  · apply Finset.sum_congr rfl
    intro b _
    by_cases hh : f b = c <;> simp [hh]
  · intro a' _ ha
    apply Finset.sum_eq_zero
    intro b _
    simp [ha]
  · simp

end FinDist

namespace FiniteMarkovChain

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

def deleteCoordinate {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 1) → V) : Fin n → V :=
  x ∘ i.succAbove

omit [Fintype V] [DecidableEq V] in
theorem deleteCoordinate_surjective [Nonempty V] {n : ℕ} (i : Fin (n + 1)) :
    Function.Surjective (deleteCoordinate (V := V) i) := by
  intro x
  let a : V := Classical.choice (inferInstance : Nonempty V)
  exact ⟨i.insertNth a x, by funext k; simp [deleteCoordinate]⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem deleteCoordinate_zero {n : ℕ} (x : Fin (n + 1) → V) :
    deleteCoordinate 0 x = Fin.tail x := by
  funext i
  simp [deleteCoordinate, Fin.tail]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem deleteCoordinate_cons {n : ℕ} (i : Fin (n + 1))
    (a : V) (x : Fin (n + 1) → V) :
    deleteCoordinate i.succ (Fin.cons a x) = Fin.cons a (deleteCoordinate i x) :=
  Fin.cons_comp_succ_succAbove a x i

/-- Discarding the initial state leaves the actual mixture of its
conditional future laws. -/
theorem law_map_tail (π : FinDist V) (K : V → FinDist V) (n : ℕ) :
    (law π K (n + 1)).map Fin.tail = π.bind (fun a ↦ continuation K a n) := by
  rw [law, FinDist.map_comp, FinDist.sigmaJoint_map]
  congr 1
  funext a
  change (continuation K a n).map (fun x ↦ Fin.tail (Fin.cons a x : Fin (n + 1) → V)) = _
  simp only [Fin.tail_cons]
  change (continuation K a n).map id = continuation K a n
  exact FinDist.map_id _

/-- Marginalizing one transition composes the actual transition laws. -/
theorem bind_continuation (π : FinDist V) (K : V → FinDist V) (n : ℕ) :
    π.bind (fun a ↦ continuation K a n) = law (π.bind K) K n := by
  ext x
  cases n with
  | zero =>
      have hx : x = Fin.elim0 := Subsingleton.elim _ _
      simp only [FinDist.bind_apply, continuation_apply_zero, mul_one, π.sum_mass,
        law, FinDist.dirac_apply, hx, ite_true]
  | succ n =>
      simp only [FinDist.bind_apply, continuation_apply_succ, law_apply_succ]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring

omit [DecidableEq V] in
theorem stationary_bind (π : FinDist V) (K : V → FinDist V)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) : π.bind K = π := by
  ext b
  exact hstationary b

theorem stationary_law_map_tail (π : FinDist V) (K : V → FinDist V)
    (hstationary : ∀ b, (∑ a, π a * K a b) = π b) (n : ℕ) :
    (law π K (n + 1)).map Fin.tail = law π K n := by
  rw [law_map_tail, bind_continuation, stationary_bind π K hstationary]

theorem continuation_map_tail (K : V → FinDist V) (initial : V) (n : ℕ) :
    (continuation K initial (n + 1)).map Fin.tail = law ((K initial).bind K) K n := by
  change (law (K initial) K (n + 1)).map Fin.tail = _
  rw [law_map_tail, bind_continuation]

/-- Deleting a later coordinate preserves the initial state and applies
the same deletion to its actual conditional continuation. -/
theorem law_delete_succ (π : FinDist V) (K : V → FinDist V) (n : ℕ)
    (i : Fin (n + 1)) :
    (law π K (n + 2)).map (deleteCoordinate i.succ) =
      (FinDist.sigmaJoint π (fun a ↦
        (continuation K a (n + 1)).map (deleteCoordinate i))).map (consJointEquiv n) := by
  rw [law, FinDist.map_comp]
  rw [← FinDist.sigmaJoint_map_fiber π (fun a ↦ continuation K a (n + 1))
    (deleteCoordinate i), FinDist.map_comp]
  congr 1
  funext z
  exact deleteCoordinate_cons i z.1 z.2

theorem continuation_delete_succ (K : V → FinDist V) (initial : V) (n : ℕ)
    (i : Fin (n + 1)) :
    (continuation K initial (n + 2)).map (deleteCoordinate i.succ) =
      (FinDist.sigmaJoint (K initial) (fun a ↦
        (continuation K a (n + 1)).map (deleteCoordinate i))).map (consJointEquiv n) :=
  law_delete_succ (K initial) K n i

end
end FiniteMarkovChain
end ForestSampling
