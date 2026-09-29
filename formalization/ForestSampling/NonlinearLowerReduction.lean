import ForestSampling.NonlinearPenalty
import ForestSampling.HardCollisionAffinity

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace NonlinearMatchingParameters

variable {N : ℕ}

/-- Total internal matching edges committed in the actual retained path.
This count is determined by the sampled instance and the adaptive program. -/
noncomputable def midpointCollisionCount (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (outcome : P.MidpointOutcome A w) : ℕ :=
  A.matchingCollisionCount outcome.1.1 w (P.hardFamily outcome.1).oracle outcome.2

/-- Concrete batch affinity estimates discharge the pointwise hypothesis in
the nonlinear midpoint reduction, for every actual execution path. -/
theorem midpointPenalty_ge_collision_loss (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (outcome : P.MidpointOutcome A w) :
    1 - Real.exp (-(P.edgeCoupling ^ 2 / 12 *
      (P.midpointCollisionCount A w outcome : ℝ))) ≤ P.midpointPenalty A w outcome := by
  let := P.vocabularyNonempty
  let trigger : Fin P.bankSize := ⟨0, P.bank_nonempty⟩
  have h := HardMatching.midpointPathWeight_le_exp_collisions P.toHardLocal
    outcome.1.1 outcome.1.2 A w outcome.2 trigger trigger
  change 1 - Real.exp (-(P.edgeCoupling ^ 2 / 12 *
      (A.matchingCollisionCount outcome.1.1 w (P.hardFamily outcome.1).oracle outcome.2 : ℝ))) ≤
    1 - A.midpointPathWeight (P.hardFamily outcome.1).model w
      (P.hardFamily outcome.1).oracle outcome.2
  apply sub_le_sub_left
  simpa only [neg_mul, toHardLocal, hardFamily, HardMatching.family,
    HardMatching.samplingInstance] using h

/-- The remaining lower-bound obligation is precisely a tail bound for the
actual collision count under the joint instance--midpoint law. This theorem
is conditional on that adaptive tail estimate; it does not assume a local
affinity inequality, a replay equivalence, or a minimax conversion. -/
theorem lowerValue_le_minimax_of_actual_collision_tail
    (P : NonlinearMatchingParameters N) (Q R : ℕ) (hR : 1 ≤ R)
    (htail : ∀ A : InstanceFamily.BudgetedSampler P.hardFamily Q R,
      ∀ w : A.1.Seed,
      (1 / 4 : ℝ) ≤ (P.midpointJoint A.1.sampler w).eventMass
        (fun outcome ↦ (N : ℝ) / (8192 * (R : ℝ)) ≤
          (P.midpointCollisionCount A.1.sampler w outcome : ℝ))) :
    P.lowerValue R ≤ InstanceFamily.minimax P.hardFamily Q R := by
  exact P.lowerValue_le_minimax_of_midpoint_estimates Q R hR
    (fun A w ↦ P.midpointCollisionCount A.1.sampler w)
    (fun A w outcome ↦ P.midpointPenalty_ge_collision_loss A.1.sampler w outcome)
    htail

end NonlinearMatchingParameters
end ForestSampling
