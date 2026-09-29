import ForestSampling.ProgramCoupling
import ForestSampling.QuerySchedule

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace Program
namespace PrefixRepair

variable {N : ℕ} {V Index : Type*} [Fintype V] [DecidableEq V]

/-- Marked failure probability for any fixed history-dependent batch law.
Queries still use the same frozen oracle. This includes both the implemented
product draws and the exact joint-reference execution. -/
noncomputable def failureMassWith (O : FrozenOracle N V) (K : BatchKernel N V) :
    {h : History N V} → {left right : Program N V h} → PrefixRepair left right → ℝ
  | _, _, _, .stop _ _ => 1
  | _, _, _, .done _ => 0
  | _, _, _, .query state _ _ _ next => failureMassWith O K (next (O.readState state))
  | h, _, _, .commit batch _ fresh _ _ next =>
      ∑ z, K.law h batch fresh z * failureMassWith O K (next z)

theorem failureMassWith_nonneg (O : FrozenOracle N V) (K : BatchKernel N V)
    {h : History N V} {left right : Program N V h} (repair : PrefixRepair left right) :
    0 ≤ repair.failureMassWith O K := by
  induction repair with
  | stop left right => exact zero_le_one
  | done complete => exact le_rfl
  | query state respects left right next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh left right next ih =>
      exact Finset.sum_nonneg fun z _ ↦ mul_nonneg ((K.law h batch fresh).nonneg z) (ih z)

theorem failureMassWith_le_one (O : FrozenOracle N V) (K : BatchKernel N V)
    {h : History N V} {left right : Program N V h} (repair : PrefixRepair left right) :
    repair.failureMassWith O K ≤ 1 := by
  induction repair with
  | stop left right => exact le_rfl
  | done complete => exact zero_le_one
  | query state respects left right next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh left right next ih =>
      change (∑ z, K.law h batch fresh z * failureMassWith O K (next z)) ≤ 1
      calc
        _ ≤ ∑ z, K.law h batch fresh z * 1 := Finset.sum_le_sum fun z _ ↦
          mul_le_mul_of_nonneg_left (ih z) ((K.law h batch fresh).nonneg z)
        _ = 1 := by simpa using (K.law h batch fresh).sum_mass

theorem failureMassWith_ofOracle (O : FrozenOracle N V)
    {h : History N V} {left right : Program N V h} (repair : PrefixRepair left right) :
    repair.failureMassWith O (BatchKernel.ofOracle O) = repair.failureMass O := by
  induction repair with
  | stop left right => rfl
  | done complete => rfl
  | query state respects left right next ih => exact ih (O.readState state)
  | commit batch nonempty fresh left right next ih =>
      simp only [failureMassWith, failureMass]
      apply Finset.sum_congr rfl
      intro z _
      rw [ih]
      rfl

/-- The marker event is measured under the actual retained execution of
the left program, with the selected commit kernel and unchanged queries. -/
theorem failureMassWith_eq_event (O : FrozenOracle N V) (K : BatchKernel N V)
    {h : History N V} {left right : Program N V h} (repair : PrefixRepair left right) :
    repair.failureMassWith O K =
      (retainedLaw O K left).eventMass (repair.HitsRepair O) := by
  classical
  induction repair with
  | stop left right =>
      rw [(retainedLaw O K left).eventMass_congr
        (HitsRepair O (stop left right)) (fun _ ↦ True) (fun _ ↦ by simp [HitsRepair])]
      simp [failureMassWith]
  | done complete => simp [failureMassWith, HitsRepair, FinDist.eventMass]
  | query state respects left right next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh left right next ih =>
      change (∑ z, K.law h batch fresh z * failureMassWith O K (next z)) = _
      simp_rw [ih]
      unfold FinDist.eventMass
      change _ = ∑ path : (z : batch → V) × RetainedPath O (left z),
        if HitsRepair O (next path.1) path.2 then
          K.law h batch fresh path.1 * retainedLaw O K (left path.1) path.2 else 0
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro path _
      change K.law h batch fresh z *
        (if HitsRepair O (next z) path then retainedLaw O K (left z) path else 0) =
        (if HitsRepair O (next z) path then
          K.law h batch fresh z * retainedLaw O K (left z) path else 0)
      split <;> simp

/-- Annotate an existing program without introducing any failure marker. -/
def unmarked : {h : History N V} → (p : Program N V h) → PrefixRepair p p
  | _, .done complete => .done complete
  | _, .query state respects next => .query state respects next next (fun r ↦ unmarked (next r))
  | _, .commit batch nonempty fresh next =>
      .commit batch nonempty fresh next next (fun z ↦ unmarked (next z))

@[simp] theorem failureMassWith_unmarked (O : FrozenOracle N V) (K : BatchKernel N V)
    {h : History N V} (p : Program N V h) :
    (unmarked p).failureMassWith O K = 0 := by
  induction p with
  | done complete => rfl
  | query state respects next ih => exact ih (O.readState state)
  | commit batch nonempty fresh next ih => simp only [unmarked, failureMassWith, ih, mul_zero, Finset.sum_const_zero]

/-- Transport an annotation along a proved equality of its actual source
programs. Its event probability is independent of this type-level transport. -/
def selfTransport {h : History N V} {p q : Program N V h}
    (heq : p = q) (marked : PrefixRepair q q) : PrefixRepair p p :=
  heq ▸ marked

@[simp] theorem failureMassWith_selfTransport (O : FrozenOracle N V) (K : BatchKernel N V)
    {h : History N V} {p q : Program N V h} (heq : p = q) (marked : PrefixRepair q q) :
    (selfTransport heq marked).failureMassWith O K = marked.failureMassWith O K := by
  cases heq
  rfl

/-- Query collection introduces no new failure event. Its continuation can
carry markers, and all replies remain those supplied to actual constructors. -/
noncomputable def querySchedule [DecidableEq Index] {h : History N V}
    (queries : Index → Submission h) :
    (todo : List Index) → (replies : ReplyTable queries) →
    (next : ReplyTable queries → Program N V h) →
    (∀ table, PrefixRepair (next table) (next table)) →
      PrefixRepair (runQuerySchedule queries todo replies next)
        (runQuerySchedule queries todo replies next)
  | [], replies, _next, marked => marked replies
  | i :: todo, replies, next, marked =>
      .query (queries i).state (queries i).respects _ _ (fun reply ↦
        querySchedule queries todo (Function.update replies i reply) next marked)

theorem failureMassWith_querySchedule [DecidableEq Index] {h : History N V}
    (queries : Index → Submission h) (todo : List Index) (replies : ReplyTable queries)
    (next : ReplyTable queries → Program N V h)
    (marked : ∀ table, PrefixRepair (next table) (next table))
    (O : FrozenOracle N V) (K : BatchKernel N V) :
    (querySchedule queries todo replies next marked).failureMassWith O K =
      (marked (fillQueryReplies queries O todo replies)).failureMassWith O K := by
  induction todo generalizing replies with
  | nil => rfl
  | cons i todo ih => exact ih _

end PrefixRepair
end Program
end ForestSampling
