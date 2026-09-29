import ForestSampling.AdaptiveSurvivorLaplace
import ForestSampling.CompensatedLaplaceTransport
import ForestSampling.OracleBudgets

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace NonlinearMatchingParameters

variable {N : ℕ}

/-- The terminal compensated collision moment is bounded by one under the
actual joint instance--midpoint execution, for every sampler and fixed seed. -/
theorem midpointLedger_compensated_laplace_le_one (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) :
    (P.midpointJoint A w).expectation (fun outcome ↦
      Real.exp (-((P.midpointLedger A w outcome).collisions : ℝ) +
        (P.midpointLedger A w outcome).activity / 64)) ≤ 1 := by
  let := P.vocabularyNonempty
  let := P.initialFiberNonempty
  rw [P.midpointLedger_expectation_eq_initial_fiber_laplace A w]
  exact HardMatching.SurvivorRecord.uniformLaplaceEval_le_one P.toHardLocal
    (P.commonInitialProgram A w) (HardMatching.SurvivorRecord.initial N P.bankSize)
    (by simp [History.empty])

/-- The real adaptive ledger satisfies the manuscript's collision tail once
its mean query disclosure is supplied. All pathwise activity and compensated
Laplace estimates are established here from the actual oracle-budgeted run. -/
theorem midpointLedger_collision_tail_of_disclosure (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (Q R : ℕ) (hR : 1 ≤ R) (hRN : R ≤ N / 16384)
    (hbudgets : ∀ I, A.WithinOracleBudgets (P.hardFamily I).oracle Q R)
    (hdisclosure : (∑ outcome, P.midpointJoint A w outcome *
      ((P.midpointLedger A w outcome).queryVertices : ℝ)/2) ≤ (N : ℝ)/8) :
    (1/4 : ℝ) ≤ (P.midpointJoint A w).eventMass
      (fun outcome ↦ (N : ℝ)/(8192*(R : ℝ)) ≤
        ((P.midpointLedger A w outcome).collisions : ℝ)) := by
  have hN : 0 < N := by omega
  have hNR : 16384 * R ≤ N := by omega
  have hNRreal : (16384 : ℝ) * R ≤ N := by exact_mod_cast hNR
  have hRNreal : (R : ℝ) ≤ (N : ℝ)/8 := by
    have hr0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    linarith
  apply CollisionBudget.collision_tail_of_laplace_and_activity
    (P.midpointJoint A w)
    (fun outcome ↦ ((P.midpointLedger A w outcome).queryVertices : ℝ)/2)
    (fun outcome ↦ ((P.midpointLedger A w outcome).collisions : ℝ))
    (fun outcome ↦ (P.midpointLedger A w outcome).activity)
    N R hR hRN
  · intro outcome
    positivity
  · simpa only [mul_div_assoc] using hdisclosure
  · intro outcome hsmall
    have hround := (Program.retainedPath_withinOracleBudgets (P.hardFamily outcome.1).oracle
      (A.program w ((P.hardFamily outcome.1).oracle.readState
        (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize))))
      outcome.2 Q R (hbudgets outcome.1 w)).2
    exact Program.retirementLedger_initial_activity outcome.1 (P.hardFamily outcome.1).oracle
      _ outcome.2 R hN hR hround hRNreal hsmall
  · exact P.midpointLedger_compensated_laplace_le_one A w

end NonlinearMatchingParameters
end ForestSampling
