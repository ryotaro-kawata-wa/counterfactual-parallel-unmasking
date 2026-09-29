import ForestSampling.CompensatedLaplace
import ForestSampling.RetirementCollisionBound

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace HardMatching.SurvivorRecord

variable (N K : ℕ)

/-- The initial compatibility predicate excludes no hidden instance. -/
def initialFiberEquiv :
    {I : InstanceIndex N K // (initial N K).Compatible I} ≃ InstanceIndex N K where
  toFun := Subtype.val
  invFun I := ⟨I, compatible_initial I⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

end HardMatching.SurvivorRecord

namespace NonlinearMatchingParameters

variable {N : ℕ}

noncomputable section

/-- The initial compatible fiber is nonempty for the concrete hard family. -/
theorem initialFiberNonempty (P : NonlinearMatchingParameters N) :
    Nonempty {I : HardMatching.InstanceIndex N P.bankSize //
      (HardMatching.SurvivorRecord.initial N P.bankSize).Compatible I} :=
  Nonempty.map (HardMatching.SurvivorRecord.initialFiberEquiv N P.bankSize).symm
    P.instanceIndex_nonempty

/-- The public all-mask reply selects the same initial program for every
hidden instance at a fixed algorithm seed. -/
def commonInitialProgram (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) : Program N (HardVocabulary P.bankSize P.backgroundSize)
      (History.empty N (HardVocabulary P.bankSize P.backgroundSize)) :=
  A.program w (fun _ ↦ P.toHardLocal.commonMarginal)

/-- The actual preprocessing branch equals this common initial program. -/
theorem hard_initialProgram_eq_common (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (I : HardMatching.InstanceIndex N P.bankSize) :
    A.program w ((P.hardFamily I).oracle.readState
      (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize))) =
        P.commonInitialProgram A w := by
  change A.program w ((HardMatching.selectedOracle P.toHardLocal I.1 I.2).readState _) = _
  rw [HardMatching.readState_allMask_common]
  rfl

/-- The terminal compensated ledger moment under the actual midpoint joint
law equals the hard-prior average of the fixed-instance recursive evaluation.
The preprocessing equality makes the initial program common across instances. -/
theorem midpointLedger_expectation_eq_prior_laplace (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) :
    letI := P.vocabularyNonempty
    (P.midpointJoint A w).expectation (fun outcome ↦
      Real.exp (-((P.midpointLedger A w outcome).collisions : ℝ) +
        (P.midpointLedger A w outcome).activity / 64)) =
      P.instancePrior.expectation (fun I ↦
        HardMatching.SurvivorRecord.laplaceEval P.toHardLocal I (P.commonInitialProgram A w)
          (HardMatching.SurvivorRecord.initial N P.bankSize)
          (HardMatching.SurvivorRecord.compatible_initial I)) := by
  let := P.vocabularyNonempty
  rw [midpointJoint, FinDist.expectation_sigmaJoint]
  apply congrArg P.instancePrior.expectation
  funext I
  calc
    _ = HardMatching.SurvivorRecord.laplaceEval P.toHardLocal I
        (A.program w ((P.hardFamily I).oracle.readState
          (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize))))
        (HardMatching.SurvivorRecord.initial N P.bankSize)
        (HardMatching.SurvivorRecord.compatible_initial I) := by
      exact (HardMatching.SurvivorRecord.laplaceEval_eq_retained_expectation
        P.toHardLocal I _ _ (HardMatching.SurvivorRecord.compatible_initial I)).symm
    _ = _ := by rw [P.hard_initialProgram_eq_common A w I]

/-- The hard prior is exactly the uniform average over the full initial
compatible fiber, using the explicit initial-fiber equivalence. -/
theorem prior_laplace_eq_initial_fiber (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) :
    letI := P.vocabularyNonempty
    letI := P.initialFiberNonempty
    P.instancePrior.expectation (fun I ↦
      HardMatching.SurvivorRecord.laplaceEval P.toHardLocal I (P.commonInitialProgram A w)
        (HardMatching.SurvivorRecord.initial N P.bankSize)
        (HardMatching.SurvivorRecord.compatible_initial I)) =
      (FinDist.uniform {I : HardMatching.InstanceIndex N P.bankSize //
        (HardMatching.SurvivorRecord.initial N P.bankSize).Compatible I}).expectation
        (fun I ↦ HardMatching.SurvivorRecord.laplaceEval P.toHardLocal I.1
          (P.commonInitialProgram A w) (HardMatching.SurvivorRecord.initial N P.bankSize) I.2) := by
  let := P.vocabularyNonempty
  let := P.initialFiberNonempty
  let := P.instanceIndex_nonempty
  exact (FinDist.uniform_expectation_equiv
    (HardMatching.SurvivorRecord.initialFiberEquiv N P.bankSize)
    (fun I ↦ HardMatching.SurvivorRecord.laplaceEval P.toHardLocal I (P.commonInitialProgram A w)
      (HardMatching.SurvivorRecord.initial N P.bankSize)
      (HardMatching.SurvivorRecord.compatible_initial I))).symm

/-- Exact transport from the initial uniform survivor fiber to the genuine
instance--midpoint expectation of the terminal compensated retirement ledger. -/
theorem midpointLedger_expectation_eq_initial_fiber_laplace
    (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) :
    letI := P.vocabularyNonempty
    letI := P.initialFiberNonempty
    (P.midpointJoint A w).expectation (fun outcome ↦
      Real.exp (-((P.midpointLedger A w outcome).collisions : ℝ) +
        (P.midpointLedger A w outcome).activity / 64)) =
      (FinDist.uniform {I : HardMatching.InstanceIndex N P.bankSize //
        (HardMatching.SurvivorRecord.initial N P.bankSize).Compatible I}).expectation
        (fun I ↦ HardMatching.SurvivorRecord.laplaceEval P.toHardLocal I.1
          (P.commonInitialProgram A w) (HardMatching.SurvivorRecord.initial N P.bankSize) I.2) := by
  let := P.vocabularyNonempty
  let := P.initialFiberNonempty
  exact (P.midpointLedger_expectation_eq_prior_laplace A w).trans
    (P.prior_laplace_eq_initial_fiber A w)

end
end NonlinearMatchingParameters
end ForestSampling
