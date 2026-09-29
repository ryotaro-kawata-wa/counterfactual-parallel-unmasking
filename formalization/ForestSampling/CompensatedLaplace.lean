import ForestSampling.FiniteFibers
import ForestSampling.CollisionLedger

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace HardMatching
namespace SurvivorRecord

variable {N K : ℕ}

/-- One commit's concrete exponential compensation factor, using the current
active batch and the actual hidden matching. -/
noncomputable def laplaceFactor (r : SurvivorRecord N K) (I : InstanceIndex N K)
    (batch : Finset (Position N)) : ℝ :=
  Real.exp (-(I.1.internalEdgeCount (batch \ r.retired) : ℝ) +
    (((batch \ r.retired).card - 1 : ℕ) : ℝ)^2 / (N - r.retired.card : ℕ) / 64)

/-- Actual finite midpoint execution evaluated with its collision compensation.
This recursion uses no hypothetical survivor law; the hidden instance is fixed. -/
noncomputable def laplaceEval {B : ℕ} [Nonempty (HardVocabulary K B)]
    (P : HardLocalParameters K B) (I : InstanceIndex N K) :
    {h : History N (HardVocabulary K B)} → (p : Program N (HardVocabulary K B) h) →
    (r : SurvivorRecord N K) → r.Compatible I → ℝ
  | _, .done _, _, _ => 1
  | _, .query state _ next, r, hI =>
      laplaceEval P I (next ((selectedOracle P I.1 I.2).readState state))
        (r.queryUpdate I hI state) (r.compatible_queryUpdate I hI state)
  | h, .commit batch _ fresh next, r, hI =>
      r.laplaceFactor I batch *
        ((instanceMidpointKernel P I).law h batch fresh).expectation (fun z ↦
          laplaceEval P I (next z) (r.commitUpdate I hI batch)
            (r.compatible_commitUpdate I hI batch))

/-- The recursive evaluation is exactly the terminal exponential moment of
the actual retained-path ledger, including all adaptive queries and values. -/
theorem laplaceEval_eq_retained_expectation {B : ℕ} [Nonempty (HardVocabulary K B)]
    (P : HardLocalParameters K B) (I : InstanceIndex N K)
    {h : History N (HardVocabulary K B)} (p : Program N (HardVocabulary K B) h)
    (r : SurvivorRecord N K) (hI : r.Compatible I) :
    laplaceEval P I p r hI =
      (Program.retainedLaw (selectedOracle P I.1 I.2) (instanceMidpointKernel P I) p).expectation
        (fun path ↦ let L := Program.retirementLedger I (selectedOracle P I.1 I.2) p r hI path
          Real.exp (-(L.collisions : ℝ) + L.activity/64)) := by
  induction p generalizing r with
  | done complete =>
      simp [laplaceEval, FinDist.expectation, Program.retainedLaw,
        Program.retirementLedger, CollisionLedger.collisions, CollisionLedger.activity]
      exact (FinDist.dirac PUnit.unit).sum_mass.symm
  | query state respects next ih => exact ih _ _ _
  | @commit h batch nonempty fresh next ih =>
      simp only [laplaceEval]
      simp_rw [ih]
      unfold FinDist.expectation
      simp only [Program.retirementLedger, CollisionLedger.collisions, CollisionLedger.activity,
        List.map_cons, List.sum_cons, Nat.cast_add]
      change _ = ∑ path : (z : batch → HardVocabulary K B) ×
        Program.RetainedPath (selectedOracle P I.1 I.2) (next z),
        ((instanceMidpointKernel P I).law h batch fresh path.1 *
          Program.retainedLaw (selectedOracle P I.1 I.2) (instanceMidpointKernel P I)
            (next path.1) path.2) *
          Real.exp (-((I.1.internalEdgeCount (batch \ r.retired) : ℝ) +
            (Program.retirementLedger I (selectedOracle P I.1 I.2) (next path.1)
              (r.commitUpdate I hI batch) (r.compatible_commitUpdate I hI batch) path.2).collisions) +
            ((((batch \ r.retired).card - 1 : ℕ) : ℝ)^2 / (N - r.retired.card : ℕ) +
              (Program.retirementLedger I (selectedOracle P I.1 I.2) (next path.1)
                (r.commitUpdate I hI batch) (r.compatible_commitUpdate I hI batch) path.2).activity)/64)
      rw [Fintype.sum_sigma, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro path _
      rw [laplaceFactor]
      have heq :
          -(I.1.internalEdgeCount (batch \ r.retired) : ℝ) +
              (((batch \ r.retired).card - 1 : ℕ) : ℝ)^2 / (N - r.retired.card : ℕ) / 64 +
              (-(Program.retirementLedger I (selectedOracle P I.1 I.2) (next z)
                (r.commitUpdate I hI batch) (r.compatible_commitUpdate I hI batch) path).collisions +
                (Program.retirementLedger I (selectedOracle P I.1 I.2) (next z)
                  (r.commitUpdate I hI batch) (r.compatible_commitUpdate I hI batch) path).activity/64) =
          -((I.1.internalEdgeCount (batch \ r.retired) : ℝ) +
            (Program.retirementLedger I (selectedOracle P I.1 I.2) (next z)
              (r.commitUpdate I hI batch) (r.compatible_commitUpdate I hI batch) path).collisions) +
            ((((batch \ r.retired).card - 1 : ℕ) : ℝ)^2 / (N - r.retired.card : ℕ) +
              (Program.retirementLedger I (selectedOracle P I.1 I.2) (next z)
                (r.commitUpdate I hI batch) (r.compatible_commitUpdate I hI batch) path).activity)/64 := by ring
      rw [← heq]
      simp only [Real.exp_add, CollisionLedger.collisions, CollisionLedger.activity]
      ring

end SurvivorRecord
end HardMatching
end ForestSampling
