import ForestSampling.OracleLowerReduction
import ForestSampling.DisclosureTransport

set_option autoImplicit false

namespace ForestSampling
namespace Program

/-- A complete program with no permitted commit rounds must already have a
complete history. Queries cannot fill an uncommitted coordinate. -/
theorem complete_of_withinOracleBudgets_zero {N : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) (Q : ℕ)
    (hb : p.WithinOracleBudgets O Q 0) : h.committed = Finset.univ := by
  induction p generalizing Q with
  | done complete => exact complete
  | query state respects next ih => exact ih (O.readState state) (Q - 1) hb.2
  | commit batch nonempty fresh next ih => exact (Nat.not_lt_zero 0 hb.1).elim

end Program

namespace NonlinearMatchingParameters

variable {N : ℕ}

/-- The concrete finite adaptive lower bound for the manuscript's actual
family-oracle budget class. The survivor posterior, adaptive disclosure,
collision tail, midpoint affinity, and seed averaging are all proved. -/
theorem lowerValue_le_oracleMinimax (P : NonlinearMatchingParameters N)
    (Q R : ℕ) (hQ : Q ≤ P.bankSize / 8) (hR : 1 ≤ R)
    (hRN : R ≤ N / 16384) :
    P.lowerValue R ≤ InstanceFamily.oracleMinimax P.hardFamily Q R := by
  apply P.lowerValue_le_oracleMinimax_of_disclosure Q R hR hRN
  intro A w
  exact P.midpointLedger_disclosure_le_eighth A.1.sampler w Q R hQ A.2.1

/-- The finite lower-bound contract is satisfied by the explicit matching
family, with no remaining collision or disclosure premise. -/
theorem oracleFiniteAdaptiveLowerBound (P : NonlinearMatchingParameters N) :
    P.OracleFiniteAdaptiveLowerBound := by
  intro Q R hQ hR hRN
  exact P.lowerValue_le_oracleMinimax Q R hQ hR hRN

/-- The actual dynamic unresolved-collision count satisfies the finite
constant-probability tail with no remaining moment or disclosure premise. -/
theorem midpointLedger_collision_tail (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (Q R : ℕ) (hQ : Q ≤ P.bankSize / 8) (hR : 1 ≤ R)
    (hRN : R ≤ N / 16384)
    (hbudgets : ∀ I, A.WithinOracleBudgets (P.hardFamily I).oracle Q R) :
    (1/4 : ℝ) ≤ (P.midpointJoint A w).eventMass
      (fun outcome ↦ (N : ℝ)/(8192*(R : ℝ)) ≤
        ((P.midpointLedger A w outcome).collisions : ℝ)) := by
  exact P.midpointLedger_collision_tail_of_disclosure A w Q R hR hRN hbudgets
    (P.midpointLedger_disclosure_le_eighth A w Q R hQ hbudgets)

/-- The finite target-error tradeoff for any admissible actual-oracle
sampler. Zero rounds are handled from the program semantics; they do not
require an additional assumption in the manuscript corollary. -/
theorem oracle_target_error_alternative (P : NonlinearMatchingParameters N)
    (Q R : ℕ) (A : InstanceFamily.OracleBudgetedSampler P.hardFamily Q R)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ (1/8 : ℝ))
    (hrisk : InstanceFamily.worstCaseRisk P.hardFamily A.1 ≤ ε) :
    P.bankSize / 8 < Q ∨ N / 16384 < R ∨
      (N : ℝ) * P.edgeCoupling ^ 2 / (786432 * ε) ≤ (R : ℝ) := by
  let := P.instanceIndex_nonempty
  by_cases hN : N = 0
  · right; right
    simp only [hN, Nat.cast_zero, zero_mul, zero_div]
    positivity
  have hR : 1 ≤ R := by
    by_contra hn
    have hR0 : R = 0 := by omega
    letI : MeasurableSpace A.1.Seed := A.1.seedMeasurableSpace
    letI : MeasureTheory.IsProbabilityMeasure A.1.seedMeasure := A.1.seedIsProbability
    obtain ⟨w⟩ := MeasureTheory.nonempty_of_isProbabilityMeasure A.1.seedMeasure
    let I := Classical.choice P.instanceIndex_nonempty
    have hb := A.2.1 I w
    have hb0 := (congrArg
      (fun r ↦ Program.WithinOracleBudgets (P.hardFamily I).oracle
        (A.1.sampler.program w ((P.hardFamily I).oracle.readState
          (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize)))) Q r)
      hR0).mp hb
    have hc := Program.complete_of_withinOracleBudgets_zero (P.hardFamily I).oracle _ Q hb0
    have hcard := congrArg Finset.card hc
    simp only [History.empty_committed, Finset.card_empty, Finset.card_univ,
      Fintype.card_fin] at hcard
    exact hN hcard.symm
  apply nonlinear_target_error_alternative P Q R
    (InstanceFamily.worstCaseRisk P.hardFamily A.1) ε hε0 hε1 hR hrisk
  intro hQ hRN
  exact (P.lowerValue_le_oracleMinimax Q R hQ hR hRN).trans
    (InstanceFamily.oracleMinimax_le_worstCaseRisk P.hardFamily Q R A)

end NonlinearMatchingParameters
end ForestSampling
