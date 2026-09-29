import ForestSampling.ProgramFailure
import ForestSampling.ForestConditionals

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace Program

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

private theorem complete_of_cover_nil (h : History N V)
    (hcover : h.uncommitted ⊆ ([] : List (Position N)).toFinset) :
    h.committed = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  by_contra hi
  have hm : i ∈ h.uncommitted := by simp [History.uncommitted, hi]
  simpa using hcover hm

private theorem cover_after_singleton (h : History N V) (j : Position N)
    (todo : List (Position N)) (hcover : h.uncommitted ⊆ (j :: todo).toFinset)
    (fresh : {j} ⊆ h.uncommitted) (z : ({j} : Finset (Position N)) → V) :
    (h.appendBatch {j} fresh z).uncommitted ⊆ todo.toFinset := by
  intro i hi
  have hparts : i ∉ h.committed ∧ i ≠ j := by
    simpa [History.uncommitted, History.appendBatch_committed, and_comm] using hi
  have hold : i ∈ h.uncommitted := by simp [History.uncommitted, hparts.1]
  have hh := hcover hold
  simpa [hparts.2] using hh

private theorem cover_skip (h : History N V) (j : Position N)
    (todo : List (Position N)) (hcover : h.uncommitted ⊆ (j :: todo).toFinset)
    (hj : j ∉ h.uncommitted) : h.uncommitted ⊆ todo.toFinset := by
  intro i hi
  have hne : i ≠ j := by rintro rfl; exact hj hi
  simpa [hne] using hcover hi

/-- Complete a history by visiting a fixed finite list and committing each
remaining coordinate singly. The coverage invariant ensures termination. -/
noncomputable def singletonCompletionFrom :
    (todo : List (Position N)) → (h : History N V) →
      (h.uncommitted ⊆ todo.toFinset) → Program N V h
  | [], h, hcover => .done (complete_of_cover_nil h hcover)
  | j :: todo, h, hcover =>
      if hj : j ∈ h.uncommitted then
        .commit {j} (Finset.singleton_nonempty _) (by simpa using hj)
          (fun z ↦ singletonCompletionFrom todo (h.appendBatch {j} (by simpa using hj) z)
            (cover_after_singleton h j todo hcover _ z))
      else singletonCompletionFrom todo h (cover_skip h j todo hcover hj)

/-- Every commit in the fallback completion is structurally safe for the
actual target, regardless of its forest or the frozen oracle. -/
theorem singletonCompletionFrom_safe (M : ForestModel N V) (O : FrozenOracle N V)
    (todo : List (Position N)) (h : History N V)
    (hcover : h.uncommitted ⊆ todo.toFinset) :
    StructurallySafe M O (singletonCompletionFrom todo h hcover) := by
  induction todo generalizing h with
  | nil => trivial
  | cons j todo ih =>
      rw [singletonCompletionFrom]
      split
      · exact ⟨M.batchStructurallySafe_singleton h j _, fun z ↦ ih _ _⟩
      · exact ih _ _

/-- A safe analytic continuation available at every first-failure marker. -/
noncomputable def singletonCompletion (h : History N V) : Program N V h :=
  singletonCompletionFrom Finset.univ.toList h (by simp)

theorem singletonCompletion_safe (M : ForestModel N V) (O : FrozenOracle N V)
    (h : History N V) : StructurallySafe M O (singletonCompletion h) :=
  singletonCompletionFrom_safe M O _ _ _

namespace PrefixRepair

/-- Safety is required before the first repair, for the actual frozen query
reply and every commit value. Marked continuations impose no condition. -/
def SafeBeforeStop (M : ForestModel N V) (O : FrozenOracle N V) :
    {h : History N V} → {left right : Program N V h} → PrefixRepair left right → Prop
  | _, _, _, .stop _ _ => True
  | _, _, _, .done _ => True
  | _, _, _, .query state _ _ _ next => SafeBeforeStop M O (next (O.readState state))
  | h, _, _, .commit batch _ fresh _ _ next =>
      M.BatchStructurallySafe h batch fresh ∧ ∀ z, SafeBeforeStop M O (next z)

@[simp] theorem safeBeforeStop_selfTransport (M : ForestModel N V) (O : FrozenOracle N V)
    {h : History N V} {p q : Program N V h} (heq : p = q) (marked : PrefixRepair q q) :
    (selfTransport heq marked).SafeBeforeStop M O ↔ marked.SafeBeforeStop M O := by
  cases heq
  rfl

@[simp] theorem safeBeforeStop_unmarked (M : ForestModel N V) (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) :
    (unmarked p).SafeBeforeStop M O ↔ StructurallySafe M O p := by
  induction p with
  | done complete => rfl
  | query state respects next ih => exact ih (O.readState state)
  | commit batch nonempty fresh next ih =>
      simp only [unmarked, SafeBeforeStop, StructurallySafe, ih]

/-- Replace each first marked continuation by an explicit safe singleton
completion while preserving every earlier query and commit. -/
noncomputable def repaired : {h : History N V} → {left right : Program N V h} →
    PrefixRepair left right → Program N V h
  | h, _, _, .stop _ _ => singletonCompletion h
  | _, _, _, .done complete => .done complete
  | _, _, _, .query state respects _ _ next =>
      .query state respects (fun reply ↦ repaired (next reply))
  | _, _, _, .commit batch nonempty fresh _ _ next =>
      .commit batch nonempty fresh (fun z ↦ repaired (next z))

/-- The original and repaired programs share precisely the same marked
prefix; this witness does not change the marker location. -/
noncomputable def replacement : {h : History N V} → {left right : Program N V h} →
    (marker : PrefixRepair left right) → PrefixRepair left marker.repaired
  | _, _, _, .stop left _ => .stop left _
  | _, _, _, .done complete => .done complete
  | _, _, _, .query state respects left _ next =>
      .query state respects left _ (fun reply ↦ replacement (next reply))
  | _, _, _, .commit batch nonempty fresh left _ next =>
      .commit batch nonempty fresh left _ (fun z ↦ replacement (next z))

/-- Replacing the stopped continuation preserves its first-hit probability
under every fixed commit kernel, including both laws used in the paper. -/
theorem replacement_failureMassWith (O : FrozenOracle N V) (K : BatchKernel N V)
    {h : History N V} {left right : Program N V h} (marker : PrefixRepair left right) :
    marker.replacement.failureMassWith O K = marker.failureMassWith O K := by
  induction marker with
  | stop left right => rfl
  | done complete => rfl
  | query state respects left right next ih => exact ih (O.readState state)
  | commit batch nonempty fresh left right next ih =>
      change (∑ z, _ * _) = ∑ z, _ * _
      exact Finset.sum_congr rfl (fun z _ ↦ congrArg (fun x ↦ _ * x) (ih z))

/-- The repaired controller is safe on all of its actual frozen-oracle
paths, including every continuation after a failed screen. -/
theorem repaired_safe (M : ForestModel N V) (O : FrozenOracle N V)
    {h : History N V} {left right : Program N V h} (marker : PrefixRepair left right)
    (hsafe : marker.SafeBeforeStop M O) : StructurallySafe M O marker.repaired := by
  induction marker with
  | stop left right => exact singletonCompletion_safe M O _
  | done complete => trivial
  | query state respects left right next ih => exact ih (O.readState state) hsafe
  | commit batch nonempty fresh left right next ih =>
      exact ⟨hsafe.1, fun z ↦ ih z (hsafe.2 z)⟩

/-- A retained path which never reaches the marker has factorizing target
batches, derived directly from pre-marker structural safety. -/
theorem pathBatchesFactorize_of_safeBeforeStop [Nonempty V] (M : ForestModel N V) (O : FrozenOracle N V)
    {h : History N V} {left right : Program N V h} (marker : PrefixRepair left right)
    (hsafe : marker.SafeBeforeStop M O) (path : RetainedPath O left)
    (hgood : ¬ marker.HitsRepair O path) :
    PathBatchesFactorize M.target M.target_positive O left path := by
  induction marker with
  | stop left right => exact (hgood True.intro).elim
  | done complete => trivial
  | query state respects left right next ih => exact ih (O.readState state) hsafe path hgood
  | @commit h batch nonempty fresh left right next ih =>
      exact ⟨M.jointBatchLaw_factorizes_of_safe h batch fresh hsafe.1,
        ih path.1 (hsafe.2 path.1) path.2 hgood⟩

end PrefixRepair
end Program
end ForestSampling
