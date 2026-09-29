import ForestSampling.OracleMinimax
import ForestSampling.AdaptiveCollisionMoment

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace NonlinearMatchingParameters

variable {N : ℕ}

/-- The current finite lower claim with the manuscript's actual family-oracle
all-path admissibility, without the legacy arbitrary-reply restriction.
This is a specification; the theorem below still lists its disclosure input. -/
def OracleFiniteAdaptiveLowerBound (P : NonlinearMatchingParameters N) : Prop :=
  ∀ Q R : ℕ, Q ≤ P.bankSize / 8 → 1 ≤ R → R ≤ N / 16384 →
    P.lowerValue R ≤ InstanceFamily.oracleMinimax P.hardFamily Q R

/-- The finite lower bound for the correct oracle-budgeted minimax class,
conditional only on the actual mean query-disclosure estimate. No collision,
activity, affinity, replay, or minimax-conversion assumption remains. -/
theorem lowerValue_le_oracleMinimax_of_disclosure (P : NonlinearMatchingParameters N)
    (Q R : ℕ) (hR : 1 ≤ R) (hRN : R ≤ N / 16384)
    (hdisclosure : ∀ A : InstanceFamily.OracleBudgetedSampler P.hardFamily Q R,
      ∀ w : A.1.Seed,
      (∑ outcome, P.midpointJoint A.1.sampler w outcome *
        ((P.midpointLedger A.1.sampler w outcome).queryVertices : ℝ)/2) ≤ (N : ℝ)/8) :
    P.lowerValue R ≤ InstanceFamily.oracleMinimax P.hardFamily Q R := by
  apply P.le_oracleMinimax_of_midpoint_penalty Q R hR
  intro A w
  have htail := P.midpointLedger_collision_tail_of_disclosure A.1.sampler w Q R hR hRN
    A.2.1 (hdisclosure A w)
  have hh := nonlinear_penalty_of_tail (P.midpointJoint A.1.sampler w)
    (P.midpointPenalty A.1.sampler w)
    (fun outcome ↦ ((P.midpointLedger A.1.sampler w outcome).collisions : ℝ))
    (P.edgeCoupling^2/12) ((N : ℝ)/(8192*(R : ℝ))) (1/4)
    (by positivity) (by positivity)
    (P.midpointPenalty_nonneg A.1.sampler w)
    (fun outcome ↦ P.midpointPenalty_ge_retirement_collision_loss A.1.sampler w outcome)
    htail
  have heq : P.edgeCoupling^2/12*((N : ℝ)/(8192*(R : ℝ))) =
      (N : ℝ)*P.edgeCoupling^2/(98304*(R : ℝ)) := by ring
  simpa only [lowerValue, heq] using hh

end NonlinearMatchingParameters
end ForestSampling
