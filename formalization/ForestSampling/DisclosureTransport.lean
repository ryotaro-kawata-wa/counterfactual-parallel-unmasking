import ForestSampling.SurvivorDisclosure
import ForestSampling.CompensatedLaplaceTransport

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace NonlinearMatchingParameters
open HardMatching.SurvivorRecord

variable {N : ℕ}

noncomputable section

/-- The actual joint expectation of query-retired vertices is exactly the
initial uniform survivor-fiber average of the concrete disclosure recursion. -/
theorem midpointLedger_queryVertices_eq_initial_disclosure
    (P : NonlinearMatchingParameters N) {Seed : Type*}
    (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed) (w : Seed) :
    letI := P.vocabularyNonempty
    letI := P.initialFiberNonempty
    (P.midpointJoint A w).expectation
      (fun outcome ↦ ((P.midpointLedger A w outcome).queryVertices : ℝ)) =
      uniformDisclosureEval P.toHardLocal (P.commonInitialProgram A w)
        (initial N P.bankSize) := by
  let := P.vocabularyNonempty
  let := P.initialFiberNonempty
  let := P.instanceIndex_nonempty
  rw [midpointJoint, FinDist.expectation_sigmaJoint]
  calc
    _ = P.instancePrior.expectation (fun I ↦
        disclosureEval P.toHardLocal I (P.commonInitialProgram A w)
          (initial N P.bankSize) (compatible_initial I)) := by
      apply congrArg P.instancePrior.expectation
      funext I
      calc
        _ = disclosureEval P.toHardLocal I
            (A.program w ((P.hardFamily I).oracle.readState
              (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize))))
            (initial N P.bankSize) (compatible_initial I) :=
          (disclosureEval_eq_retained_expectation P.toHardLocal I _ _ (compatible_initial I)).symm
        _ = _ := by rw [P.hard_initialProgram_eq_common A w I]
    _ = _ := (FinDist.uniform_expectation_equiv (initialFiberEquiv N P.bankSize)
      (fun I ↦ disclosureEval P.toHardLocal I (P.commonInitialProgram A w)
        (initial N P.bankSize) (compatible_initial I))).symm

/-- The actual adaptive query-disclosure expectation has the exact Q/K
constant. Budgets cover the actual frozen oracle of every hard instance and
all possible commit values, including under the analytic midpoint process. -/
theorem midpointLedger_queryVertices_expectation_le (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (Q R : ℕ) (hQ : Q < P.bankSize)
    (hbudgets : ∀ I, A.WithinOracleBudgets (P.hardFamily I).oracle Q R) :
    (P.midpointJoint A w).expectation
      (fun outcome ↦ ((P.midpointLedger A w outcome).queryVertices : ℝ)) ≤
      2 * (N : ℝ) * Q / P.bankSize := by
  let := P.vocabularyNonempty
  let := P.initialFiberNonempty
  rw [P.midpointLedger_queryVertices_eq_initial_disclosure A w]
  have hbound := uniformDisclosureEval_le P.toHardLocal (P.commonInitialProgram A w)
    (initial N P.bankSize) (by simp [History.empty]) P.bankSize Q R hQ
    (by intro i; simp [initial])
    (by
      intro I _
      rw [← P.hard_initialProgram_eq_common A w I]
      exact hbudgets I w)
  simpa only [initial, Finset.card_empty, Nat.sub_zero] using hbound

/-- With at most K/8 extra queries, the expected number of query-retired
edges is at most N/8 under the actual instance--midpoint law. This is the
remaining numerical input to the concrete adaptive collision-tail theorem. -/
theorem midpointLedger_disclosure_le_eighth (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (Q R : ℕ) (hQ : Q ≤ P.bankSize / 8)
    (hbudgets : ∀ I, A.WithinOracleBudgets (P.hardFamily I).oracle Q R) :
    (∑ outcome, P.midpointJoint A w outcome *
      ((P.midpointLedger A w outcome).queryVertices : ℝ) / 2) ≤ (N : ℝ) / 8 := by
  have hK : 0 < P.bankSize := P.bank_nonempty
  have hQlt : Q < P.bankSize := by omega
  have hbound := P.midpointLedger_queryVertices_expectation_le A w Q R hQlt hbudgets
  have hratio : (Q : ℝ) / P.bankSize ≤ 1 / 8 := by
    have hKr : (0 : ℝ) < P.bankSize := by exact_mod_cast hK
    apply (div_le_iff₀ hKr).mpr
    have hnat : 8 * Q ≤ P.bankSize := by omega
    have hreal : (8 : ℝ) * Q ≤ P.bankSize := by exact_mod_cast hnat
    linarith
  have hscale := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ 2 * N by positivity)
  rw [← Finset.sum_div]
  change (P.midpointJoint A w).expectation
    (fun outcome ↦ ((P.midpointLedger A w outcome).queryVertices : ℝ)) / 2 ≤ _
  have hupper : 2 * (N : ℝ) * Q / P.bankSize ≤ (N : ℝ) / 4 := by
    calc
      _ = 2 * (N : ℝ) * ((Q : ℝ) / P.bankSize) := by ring
      _ ≤ 2 * (N : ℝ) * (1 / 8) := hscale
      _ = _ := by ring
  linarith

end
end NonlinearMatchingParameters
end ForestSampling
