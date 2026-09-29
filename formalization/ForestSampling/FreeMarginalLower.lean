import ForestSampling.FreeMarginalBudgets
import ForestSampling.FreeMarginalDisclosure
import ForestSampling.AdaptiveCollisionMoment
import ForestSampling.Minimax
import ForestSampling.HardMidpoint

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.NonlinearMatchingParameters

variable {N : ℕ}

/-- The concrete collision tail remains valid when current-history marginal
reads are free. The proof uses the actual retained commit count, rather than
an ordinary-query budget or a surrogate execution. -/
theorem midpointLedger_freeMarginal_collision_tail_of_disclosure (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (Q R : ℕ) (hR : 1 ≤ R) (hRN : R ≤ N / 16384)
    (hbudgets : ∀ I, A.WithinFreeMarginalBudgets (P.hardFamily I).oracle Q R)
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
    have hround := Program.retainedRoundCount_le_freeMarginalBudget (P.hardFamily outcome.1).oracle
      (A.program w ((P.hardFamily outcome.1).oracle.readState
        (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize))))
      outcome.2 Q R (hbudgets outcome.1 w)
    exact Program.retirementLedger_initial_activity outcome.1 (P.hardFamily outcome.1).oracle
      _ outcome.2 R hN hR hround hRNreal hsmall
  · exact P.midpointLedger_compensated_laplace_le_one A w

/-- The actual midpoint affinity reduction yields a seedwise finite-prior
TV lower bound in the stronger observation model. Free marginal observations
change only the admissibility premise; the output laws and prior are unchanged. -/
theorem freeMarginal_seedwise_prior_tv_lower_of_disclosure (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (Q R : ℕ) (hR : 1 ≤ R) (hRN : R ≤ N / 16384)
    (hbudgets : ∀ I, A.WithinFreeMarginalBudgets (P.hardFamily I).oracle Q R)
    (hdisclosure : (∑ outcome, P.midpointJoint A w outcome *
      ((P.midpointLedger A w outcome).queryVertices : ℝ)/2) ≤ (N : ℝ)/8) :
    P.lowerValue R ≤ ∑ I, P.instancePrior I *
      FinDist.tv (P.hardFamily I).model.target (A.outputLaw w (P.hardFamily I).oracle) := by
  have htail := P.midpointLedger_freeMarginal_collision_tail_of_disclosure A w Q R hR hRN hbudgets hdisclosure
  have hh := nonlinear_penalty_of_tail (P.midpointJoint A w)
    (P.midpointPenalty A w)
    (fun outcome ↦ ((P.midpointLedger A w outcome).collisions : ℝ))
    (P.edgeCoupling^2/12) ((N : ℝ)/(8192*(R : ℝ))) (1/4)
    (by positivity) (by positivity) (P.midpointPenalty_nonneg A w)
    (fun outcome ↦ P.midpointPenalty_ge_retirement_collision_loss A w outcome) htail
  have heq : P.edgeCoupling^2/12*((N : ℝ)/(8192*(R : ℝ))) =
      (N : ℝ)*P.edgeCoupling^2/(98304*(R : ℝ)) := by ring
  have hpenalty : P.lowerValue R ≤ ∑ outcome, P.midpointJoint A w outcome * P.midpointPenalty A w outcome := by
    simpa only [lowerValue, heq] using hh
  exact hpenalty.trans (P.midpoint_penalty_le_prior_tv A w)

/-- Finite-prior seed averaging applies directly to arbitrary randomized
sampler data with its actual probability seed measure and stored TV
measurability. No legacy budget subtype is introduced. -/
theorem freeMarginal_lowerValue_le_worstCaseRisk_of_disclosure (P : NonlinearMatchingParameters N)
    (A : RandomizedSamplerData N (HardVocabulary P.bankSize P.backgroundSize))
    (Q R : ℕ) (hR : 1 ≤ R) (hRN : R ≤ N / 16384)
    (hbudgets : ∀ I, A.sampler.WithinFreeMarginalBudgets (P.hardFamily I).oracle Q R)
    (hmeas : ∀ I, A.RiskMeasurableAt (P.hardFamily I))
    (hdisclosure : ∀ w : A.Seed, (∑ outcome, P.midpointJoint A.sampler w outcome *
      ((P.midpointLedger A.sampler w outcome).queryVertices : ℝ)/2) ≤ (N : ℝ)/8) :
    P.lowerValue R ≤ InstanceFamily.worstCaseRisk P.hardFamily A := by
  exact (InstanceFamily.le_priorRisk_of_seedwise P.hardFamily P.instancePrior A hmeas
    (P.lowerValue R) (fun w ↦ P.freeMarginal_seedwise_prior_tv_lower_of_disclosure A.sampler w
      Q R hR hRN hbudgets (hdisclosure w))).trans
    (InstanceFamily.priorRisk_le_worstCaseRisk P.hardFamily P.instancePrior A hmeas)


/-- With at most K/8 charged probes, the actual free-marginal midpoint
execution has the full constant-probability collision tail. -/
theorem midpointLedger_freeMarginal_collision_tail (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (Q R : ℕ) (hQ : Q ≤ P.bankSize / 8) (hR : 1 ≤ R)
    (hRN : R ≤ N / 16384)
    (hbudgets : ∀ I, A.WithinFreeMarginalBudgets (P.hardFamily I).oracle Q R) :
    (1/4 : ℝ) ≤ (P.midpointJoint A w).eventMass
      (fun outcome ↦ (N : ℝ)/(8192*(R : ℝ)) ≤
        ((P.midpointLedger A w outcome).collisions : ℝ)) :=
  P.midpointLedger_freeMarginal_collision_tail_of_disclosure A w Q R hR hRN hbudgets
    (P.midpointLedger_freeMarginal_disclosure_le_eighth A w Q R hQ hbudgets)

/-- The finite-prior TV lower bound holds seedwise for the stronger model
with arbitrary free current-history marginal observations. -/
theorem freeMarginal_seedwise_prior_tv_lower (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (Q R : ℕ) (hQ : Q ≤ P.bankSize / 8) (hR : 1 ≤ R)
    (hRN : R ≤ N / 16384)
    (hbudgets : ∀ I, A.WithinFreeMarginalBudgets (P.hardFamily I).oracle Q R) :
    P.lowerValue R ≤ ∑ I, P.instancePrior I *
      FinDist.tv (P.hardFamily I).model.target (A.outputLaw w (P.hardFamily I).oracle) :=
  P.freeMarginal_seedwise_prior_tv_lower_of_disclosure A w Q R hR hRN hbudgets
    (P.midpointLedger_freeMarginal_disclosure_le_eighth A w Q R hQ hbudgets)

/-- The actual seed-averaged worst-case TV lower bound for arbitrary
randomized sampler data, using its given seed law and measurable losses. -/
theorem freeMarginal_lowerValue_le_worstCaseRisk (P : NonlinearMatchingParameters N)
    (A : RandomizedSamplerData N (HardVocabulary P.bankSize P.backgroundSize))
    (Q R : ℕ) (hQ : Q ≤ P.bankSize / 8) (hR : 1 ≤ R) (hRN : R ≤ N / 16384)
    (hbudgets : ∀ I, A.sampler.WithinFreeMarginalBudgets (P.hardFamily I).oracle Q R)
    (hmeas : ∀ I, A.RiskMeasurableAt (P.hardFamily I)) :
    P.lowerValue R ≤ InstanceFamily.worstCaseRisk P.hardFamily A :=
  P.freeMarginal_lowerValue_le_worstCaseRisk_of_disclosure A Q R hR hRN hbudgets hmeas
    (fun w ↦ P.midpointLedger_freeMarginal_disclosure_le_eighth A.sampler w Q R hQ hbudgets)

/-- The same target-error query/round alternative holds even with free
current-history marginal feedback. The zero-round case follows from actual
program completion, including under an arbitrary probability seed law. -/
theorem freeMarginal_target_error_alternative (P : NonlinearMatchingParameters N)
    (A : RandomizedSamplerData N (HardVocabulary P.bankSize P.backgroundSize))
    (Q R : ℕ)
    (hbudgets : ∀ I, A.sampler.WithinFreeMarginalBudgets (P.hardFamily I).oracle Q R)
    (hmeas : ∀ I, A.RiskMeasurableAt (P.hardFamily I))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ (1/8 : ℝ))
    (hrisk : InstanceFamily.worstCaseRisk P.hardFamily A ≤ ε) :
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
    letI : MeasurableSpace A.Seed := A.seedMeasurableSpace
    letI : MeasureTheory.IsProbabilityMeasure A.seedMeasure := A.seedIsProbability
    obtain ⟨w⟩ := MeasureTheory.nonempty_of_isProbabilityMeasure A.seedMeasure
    let I := Classical.choice P.instanceIndex_nonempty
    have hb := hbudgets I w
    have hb0 := (congrArg
      (fun r ↦ Program.WithinFreeMarginalBudgets (P.hardFamily I).oracle
        (A.sampler.program w ((P.hardFamily I).oracle.readState
          (MaskedState.allMask N (HardVocabulary P.bankSize P.backgroundSize)))) Q r)
      hR0).mp hb
    have hc := Program.complete_of_freeMarginalBudget_zero (P.hardFamily I).oracle _ Q hb0
    have hcard := congrArg Finset.card hc
    simp only [History.empty_committed, Finset.card_empty, Finset.card_univ,
      Fintype.card_fin] at hcard
    exact hN hcard.symm
  apply nonlinear_target_error_alternative P Q R
    (InstanceFamily.worstCaseRisk P.hardFamily A) ε hε0 hε1 hR hrisk
  intro hQ hRN
  exact P.freeMarginal_lowerValue_le_worstCaseRisk A Q R hQ hR hRN hbudgets hmeas

end ForestSampling.NonlinearMatchingParameters
