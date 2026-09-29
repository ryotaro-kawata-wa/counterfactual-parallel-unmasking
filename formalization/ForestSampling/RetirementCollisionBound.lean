import ForestSampling.CollisionLedger
import ForestSampling.NonlinearLowerReduction
import ForestSampling.FiniteEvents

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace Program

variable {N K B : ℕ}
open HardMatching HardMatching.SurvivorRecord

/-- Newly colliding unresolved edges are a subset of all matching edges
committed internally along the same actual retained execution. -/
theorem retirementLedger_collisions_le_retained (I : InstanceIndex N K)
    (O : FrozenOracle N (HardVocabulary K B))
    {h : History N (HardVocabulary K B)} (p : Program N (HardVocabulary K B) h)
    (r : SurvivorRecord N K) (hI : r.Compatible I) (path : RetainedPath O p) :
    (retirementLedger I O p r hI path).collisions ≤
      retainedMatchingCollisionCount I.1 O p path := by
  induction p generalizing r with
  | done complete => exact le_rfl
  | query state respects next ih => exact ih (O.readState state) _ _ path
  | commit batch nonempty fresh next ih =>
      change I.1.internalEdgeCount (batch \ r.retired) +
        (retirementLedger I O (next path.1) (r.commitUpdate I hI batch) _ path.2).collisions ≤
        Fintype.card (I.1.BatchEdge batch) + retainedMatchingCollisionCount I.1 O (next path.1) path.2
      apply Nat.add_le_add _ (ih path.1 _ _ path.2)
      rw [← I.1.internalEdgeCount_eq_batchEdge_card]
      exact I.1.internalEdgeCount_mono Finset.sdiff_subset

end Program

namespace NonlinearMatchingParameters

variable {N : ℕ}

/-- The actual survivor-retirement ledger on a hard-instance midpoint outcome. -/
noncomputable def midpointLedger (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (outcome : P.MidpointOutcome A w) : CollisionLedger :=
  Program.retirementLedger outcome.1 (P.hardFamily outcome.1).oracle
    (A.program w ((P.hardFamily outcome.1).oracle.readState
      (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize))))
    (HardMatching.SurvivorRecord.initial N P.bankSize)
    (HardMatching.SurvivorRecord.compatible_initial outcome.1) outcome.2

/-- The paper's undisclosed-edge count is dominated by the already verified
all-internal-edge path count, with the same instance and path. -/
theorem midpointLedger_collisions_le (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (outcome : P.MidpointOutcome A w) :
    (P.midpointLedger A w outcome).collisions ≤ P.midpointCollisionCount A w outcome :=
  Program.retirementLedger_collisions_le_retained outcome.1 _ _ _ _ outcome.2

/-- The concrete local affinity loss applies to the exact dynamic
undisclosed-edge count used by the retirement ledger. -/
theorem midpointPenalty_ge_retirement_collision_loss (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (outcome : P.MidpointOutcome A w) :
    1 - Real.exp (-(P.edgeCoupling^2/12 *
      ((P.midpointLedger A w outcome).collisions : ℝ))) ≤ P.midpointPenalty A w outcome := by
  apply le_trans _ (P.midpointPenalty_ge_collision_loss A w outcome)
  apply sub_le_sub_left
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast P.midpointLedger_collisions_le A w outcome


/-- The exact power loss holds for the concrete undisclosed-edge count,
with any reference trigger pair because the edge affinity is invariant. -/
theorem midpointPenalty_ge_retirement_affinity_loss (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (outcome : P.MidpointOutcome A w) (s t : Fin P.bankSize) :
    1 - (FinDist.affinity (P.toHardLocal.edgeLaw s t)
      (P.toHardLocal.commonMarginal.prod P.toHardLocal.commonMarginal)) ^
        (P.midpointLedger A w outcome).collisions ≤ P.midpointPenalty A w outcome := by
  let := P.vocabularyNonempty
  let a := FinDist.affinity (P.toHardLocal.edgeLaw s t)
    (P.toHardLocal.commonMarginal.prod P.toHardLocal.commonMarginal)
  have hp := HardMatching.retainedAffinityWeight_le_edgeAffinity_pow P.toHardLocal
    outcome.1.1 outcome.1.2 (P.hardFamily outcome.1).oracle
    (A.program w ((P.hardFamily outcome.1).oracle.readState
      (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize)))) outcome.2 s t
  have hpow : a ^ P.midpointCollisionCount A w outcome ≤
      a ^ (P.midpointLedger A w outcome).collisions :=
    pow_le_pow_of_le_one (FinDist.affinity_nonneg _ _) (FinDist.affinity_le_one _ _)
      (P.midpointLedger_collisions_le A w outcome)
  change 1 - a ^ (P.midpointLedger A w outcome).collisions ≤
    1 - A.midpointPathWeight (P.hardFamily outcome.1).model w
      (P.hardFamily outcome.1).oracle outcome.2
  apply sub_le_sub_left
  apply le_trans _ hpow
  simpa only [a, midpointCollisionCount, Sampler.matchingCollisionCount,
    Sampler.midpointPathWeight, hardFamily, HardMatching.family,
    HardMatching.samplingInstance, HardMatching.model] using hp

/-- The paper's exact averaged collision-affinity inequality, under the
actual joint instance--midpoint law and its dynamically retired-edge count. -/
theorem prior_sqHellinger_ge_retirement_power_loss (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (s t : Fin P.bankSize) :
    (∑ outcome, P.midpointJoint A w outcome *
      (1 - (1 - FinDist.sqHellinger (P.toHardLocal.edgeLaw s t)
        (P.toHardLocal.commonMarginal.prod P.toHardLocal.commonMarginal)) ^
          (P.midpointLedger A w outcome).collisions)) ≤
      ∑ I, P.instancePrior I * FinDist.sqHellinger (P.hardFamily I).model.target
        (A.outputLaw w (P.hardFamily I).oracle) := by
  have heq : 1 - FinDist.sqHellinger (P.toHardLocal.edgeLaw s t)
      (P.toHardLocal.commonMarginal.prod P.toHardLocal.commonMarginal) =
      FinDist.affinity (P.toHardLocal.edgeLaw s t)
        (P.toHardLocal.commonMarginal.prod P.toHardLocal.commonMarginal) := by
    rw [FinDist.sqHellinger]
    ring
  rw [heq, P.prior_sqHellinger_eq_midpoint_penalty]
  exact Finset.sum_le_sum fun outcome _ ↦
    mul_le_mul_of_nonneg_left (P.midpointPenalty_ge_retirement_affinity_loss A w outcome s t)
      ((P.midpointJoint A w).nonneg outcome)

/-- With the actual retirement-count tail supplied, all remaining affinity,
replay, prior averaging and minimax steps of the finite lower bound are proved. -/
theorem lowerValue_le_minimax_of_retirement_collision_tail
    (P : NonlinearMatchingParameters N) (Q R : ℕ) (hR : 1 ≤ R)
    (htail : ∀ A : InstanceFamily.BudgetedSampler P.hardFamily Q R,
      ∀ w : A.1.Seed,
      (1 / 4 : ℝ) ≤ (P.midpointJoint A.1.sampler w).eventMass
        (fun outcome ↦ (N : ℝ)/(8192*(R : ℝ)) ≤
          ((P.midpointLedger A.1.sampler w outcome).collisions : ℝ))) :
    P.lowerValue R ≤ InstanceFamily.minimax P.hardFamily Q R := by
  exact P.lowerValue_le_minimax_of_midpoint_estimates Q R hR
    (fun A w outcome ↦ (P.midpointLedger A.1.sampler w outcome).collisions)
    (fun A w outcome ↦ P.midpointPenalty_ge_retirement_collision_loss A.1.sampler w outcome)
    htail

end NonlinearMatchingParameters
end ForestSampling
