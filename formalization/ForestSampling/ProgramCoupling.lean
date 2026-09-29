import ForestSampling.FiniteCoupling
import ForestSampling.ProgramMidpoint
import ForestSampling.Minimax

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

namespace ForestSampling
namespace Program

universe u
variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Two programs share exactly the same operations until an explicitly marked
repair point, after which either continuation may be arbitrary. The marker
represents a failed-screen switch when this interface is instantiated. -/
inductive PrefixRepair : {h : History N V} → Program N V h → Program N V h → Type (u + 1)
  | stop {h : History N V} (left right : Program N V h) : PrefixRepair left right
  | done {h : History N V} (complete : h.committed = Finset.univ) :
      PrefixRepair (.done complete) (.done complete)
  | query {h : History N V} (state : MaskedState N V) (respects : state.RespectsHistory h)
      (left right : (MaskedPosition state → FinDist V) → Program N V h)
      (next : ∀ reply, PrefixRepair (left reply) (right reply)) :
      PrefixRepair (.query state respects left) (.query state respects right)
  | commit {h : History N V} (batch : Finset (Position N)) (nonempty : batch.Nonempty)
      (fresh : batch ⊆ h.uncommitted)
      (left right : (z : batch → V) → Program N V (h.appendBatch batch fresh z))
      (next : ∀ z, PrefixRepair (left z) (right z)) :
      PrefixRepair (.commit batch nonempty fresh left) (.commit batch nonempty fresh right)

namespace PrefixRepair

/-- Probability of reaching the first marked repair, accumulated only while
the two programs still share their query replies and product-commit laws. -/
noncomputable def failureMass (O : FrozenOracle N V) :
    {h : History N V} → {left right : Program N V h} → PrefixRepair left right → ℝ
  | _, _, _, .stop _ _ => 1
  | _, _, _, .done _ => 0
  | _, _, _, .query state _ _ _ next => failureMass O (next (O.readState state))
  | h, _, _, .commit batch _ fresh _ _ next =>
      ∑ z, O.commitDistribution h batch fresh z * failureMass O (next z)

theorem failureMass_nonneg (O : FrozenOracle N V) {h : History N V}
    {left right : Program N V h} (repair : PrefixRepair left right) :
    0 ≤ repair.failureMass O := by
  induction repair with
  | stop left right => exact zero_le_one
  | done complete => exact le_rfl
  | query state respects left right next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh left right next ih =>
      exact Finset.sum_nonneg fun z _ ↦
        mul_nonneg ((O.commitDistribution h batch fresh).nonneg z) (ih z)

theorem failureMass_le_one (O : FrozenOracle N V) {h : History N V}
    {left right : Program N V h} (repair : PrefixRepair left right) :
    repair.failureMass O ≤ 1 := by
  induction repair with
  | stop left right => exact le_rfl
  | done complete => exact zero_le_one
  | query state respects left right next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh left right next ih =>
      change (∑ z, O.commitDistribution h batch fresh z * failureMass O (next z)) ≤ 1
      calc
        _ ≤ ∑ z, O.commitDistribution h batch fresh z * 1 :=
          Finset.sum_le_sum fun z _ ↦
            mul_le_mul_of_nonneg_left (ih z) ((O.commitDistribution h batch fresh).nonneg z)
        _ = 1 := by simpa using (O.commitDistribution h batch fresh).sum_mass

/-- A marked repair point is reached along the original program's retained
path. It is an ordinary event on the actual execution, not a change of law. -/
def HitsRepair (O : FrozenOracle N V) :
    {h : History N V} → {left right : Program N V h} →
      PrefixRepair left right → RetainedPath O left → Prop
  | _, _, _, .stop _ _, _ => True
  | _, _, _, .done _, _ => False
  | _, _, _, .query state _ _ _ next, path =>
      HitsRepair O (next (O.readState state)) path
  | _, _, _, .commit _ _ _ _ _ next, path => HitsRepair O (next path.1) path.2

noncomputable instance hitsRepairDecidable (O : FrozenOracle N V) {h : History N V}
    {left right : Program N V h} (repair : PrefixRepair left right) :
    DecidablePred (repair.HitsRepair O) := fun _ ↦ Classical.propDecidable _

/-- The recursively accumulated failure mass equals the actual first-repair
probability under the original oracle-product execution. -/
theorem failureMass_eq_actual_event (O : FrozenOracle N V) {h : History N V}
    {left right : Program N V h} (repair : PrefixRepair left right) :
    repair.failureMass O =
      (retainedLaw O (BatchKernel.ofOracle O) left).eventMass (repair.HitsRepair O) := by
  classical
  induction repair with
  | stop left right =>
      rw [(retainedLaw O (BatchKernel.ofOracle O) left).eventMass_congr
        (HitsRepair O (stop left right)) (fun _ ↦ True) (fun _ ↦ by simp [HitsRepair])]
      simp [failureMass]
  | done complete => simp [failureMass, HitsRepair, FinDist.eventMass]
  | query state respects left right next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh left right next ih =>
      change (∑ z, O.commitDistribution h batch fresh z * failureMass O (next z)) = _
      simp_rw [ih]
      unfold FinDist.eventMass
      change _ = ∑ path : (z : batch → V) × RetainedPath O (left z),
        if HitsRepair O (next path.1) path.2 then
          O.commitDistribution h batch fresh path.1 *
            retainedLaw O (BatchKernel.ofOracle O) (left path.1) path.2 else 0
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro path _
      change O.commitDistribution h batch fresh z *
        (if HitsRepair O (next z) path then retainedLaw O (BatchKernel.ofOracle O) (left z) path else 0) =
        (if HitsRepair O (next z) path then
          O.commitDistribution h batch fresh z * retainedLaw O (BatchKernel.ofOracle O) (left z) path else 0)
      split <;> simp

/-- Common-prefix coupling for the existing actual Program semantics.
After the repair marker there is no restriction on the two continuations. -/
theorem tv_eval_le_failureMass (O : FrozenOracle N V) {h : History N V}
    {left right : Program N V h} (repair : PrefixRepair left right) :
    FinDist.tv (eval O left) (eval O right) ≤ repair.failureMass O := by
  induction repair with
  | stop left right => exact FinDist.tv_le_one _ _
  | done complete => exact le_of_eq (FinDist.tv_self _)
  | query state respects left right next ih => exact ih (O.readState state)
  | @commit h batch nonempty fresh left right next ih =>
      change FinDist.tv ((O.commitDistribution h batch fresh).bind (fun z ↦ eval O (left z)))
        ((O.commitDistribution h batch fresh).bind (fun z ↦ eval O (right z))) ≤ _
      apply (FinDist.tv_bind_same_le _ _ _).trans
      exact Finset.sum_le_sum fun z _ ↦
        mul_le_mul_of_nonneg_left (ih z) ((O.commitDistribution h batch fresh).nonneg z)

/-- A target-error bound for the repaired program transfers back to the
original program, charging only the probability of reaching the repair. -/
theorem tv_target_eval_le (O : FrozenOracle N V)
    (target : FinDist (Configuration N V)) {h : History N V}
    {left right : Program N V h} (repair : PrefixRepair left right)
    (ρ : ℝ) (hright : FinDist.tv target (eval O right) ≤ ρ) :
    FinDist.tv target (eval O left) ≤ ρ + repair.failureMass O := by
  have ht := FinDist.tv_triangle target (eval O right) (eval O left)
  have hc := repair.tv_eval_le_failureMass O
  rw [FinDist.tv_comm (eval O left) (eval O right)] at hc
  linarith

end PrefixRepair
end Program

namespace Sampler

variable {N : ℕ} {V Seed : Type*} [Fintype V] [DecidableEq V]
variable [MeasurableSpace Seed]

/-- Average the actual common-prefix comparison over seeds. The repaired
sampler's fixed-seed target error and the mean first-repair probability are
separate, explicit inputs; the construction must supply them. -/
theorem seedRisk_le_of_prefix_repair (A B : Sampler N V Seed) (μ : Measure Seed)
    [IsProbabilityMeasure μ] (M : ForestModel N V) (O : FrozenOracle N V)
    (ρ η : ℝ)
    (repair : ∀ w : Seed, Program.PrefixRepair
      (A.program w (O.readState (MaskedState.allMask N V)))
      (B.program w (O.readState (MaskedState.allMask N V))))
    (hB : ∀ w, FinDist.tv M.target (B.outputLaw w O) ≤ ρ)
    (hmeas : AEStronglyMeasurable (fun w ↦ FinDist.tv M.target (A.outputLaw w O)) μ)
    (hfailMeas : AEStronglyMeasurable (fun w ↦ (repair w).failureMass O) μ)
    (hfailure : (∫ w, (repair w).failureMass O ∂μ) ≤ η) :
    A.seedRisk μ M O ≤ ρ + η := by
  have hintf : Integrable (fun w ↦ (repair w).failureMass O) μ := by
    refine (integrable_const (1 : ℝ)).mono' hfailMeas ?_
    exact ae_of_all _ fun w ↦ by
      rw [Real.norm_of_nonneg ((repair w).failureMass_nonneg O)]
      exact (repair w).failureMass_le_one O
  have hintA := A.integrable_seed_loss μ M O hmeas
  have hpoint : ∀ w, FinDist.tv M.target (A.outputLaw w O) ≤
      ρ + (repair w).failureMass O := by
    intro w
    exact (repair w).tv_target_eval_le O M.target ρ (hB w)
  unfold seedRisk
  calc
    (∫ w, FinDist.tv M.target (A.outputLaw w O) ∂μ) ≤
        ∫ w, ρ + (repair w).failureMass O ∂μ :=
      integral_mono hintA ((integrable_const ρ).add hintf) hpoint
    _ = ρ + ∫ w, (repair w).failureMass O ∂μ := by
      rw [integral_add (integrable_const _) hintf]
      simp
    _ ≤ ρ + η := add_le_add le_rfl hfailure

end Sampler
end ForestSampling
