import ForestSampling.ObservedEmbedding
import ForestSampling.FreeMarginalLower
import ForestSampling.LowerAsymptotics

set_option autoImplicit false

namespace ForestSampling
namespace NonlinearMatchingParameters

variable {N : ℕ}

/-- The finite nonlinear lower bound for the actual observed protocol,
including every commit's returned probability rows. Compilation preserves
risk exactly and spends no additional informative probe. -/
theorem observed_lowerValue_le_worstCaseRisk (P : NonlinearMatchingParameters N)
    (A : RandomizedObservedSamplerData N (HardVocabulary P.bankSize P.backgroundSize))
    (Q R : ℕ) (hQ : Q ≤ P.bankSize / 8) (hR : 1 ≤ R) (hRN : R ≤ N / 16384)
    (hbudgets : ∀ I, A.sampler.WithinOracleBudgets (P.hardFamily I).oracle Q R)
    (hmeas : ∀ I, A.RiskMeasurableAt (P.hardFamily I)) :
    P.lowerValue R ≤ InstanceFamily.observedWorstCaseRisk P.hardFamily A := by
  have h := P.freeMarginal_lowerValue_le_worstCaseRisk A.compile Q R hQ hR hRN
    (fun I ↦ (hbudgets I).compile_withinFreeMarginalBudgets)
    (fun I ↦ (A.riskMeasurableAt_compile_iff (P.hardFamily I)).mpr (hmeas I))
  rwa [InstanceFamily.worstCaseRisk_compile] at h

/-- The full observed-controller minimax theorem. Positive rounds supply
an actual measurable feasible sampler, so the infimum is not empty. -/
theorem lowerValue_le_observedMinimax (P : NonlinearMatchingParameters N)
    (Q R : ℕ) (hQ : Q ≤ P.bankSize / 8) (hR : 1 ≤ R) (hRN : R ≤ N / 16384) :
    P.lowerValue R ≤ InstanceFamily.observedMinimax P.hardFamily Q R := by
  let := InstanceFamily.observedBudgetedSampler_nonempty P.hardFamily Q R hR
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨A, rfl⟩
  exact P.observed_lowerValue_le_worstCaseRisk A.1 Q R hQ hR hRN A.2.1 A.2.2

/-- The printed nonlinear target-error alternative now covers controllers
that adapt to all ordinary commit feedback, with the original Q/R charges. -/
theorem observed_target_error_alternative (P : NonlinearMatchingParameters N)
    (A : RandomizedObservedSamplerData N (HardVocabulary P.bankSize P.backgroundSize))
    (Q R : ℕ)
    (hbudgets : ∀ I, A.sampler.WithinOracleBudgets (P.hardFamily I).oracle Q R)
    (hmeas : ∀ I, A.RiskMeasurableAt (P.hardFamily I))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ))
    (hrisk : InstanceFamily.observedWorstCaseRisk P.hardFamily A ≤ ε) :
    P.bankSize / 8 < Q ∨ N / 16384 < R ∨
      (N : ℝ) * P.edgeCoupling ^ 2 / (786432 * ε) ≤ (R : ℝ) := by
  apply P.freeMarginal_target_error_alternative A.compile Q R
    (fun I ↦ (hbudgets I).compile_withinFreeMarginalBudgets)
    (fun I ↦ (A.riskMeasurableAt_compile_iff (P.hardFamily I)).mpr (hmeas I)) ε hε0 hε1
  rwa [InstanceFamily.worstCaseRisk_compile]

end NonlinearMatchingParameters

/-- The calibrated finite lower alternative for the full observation
protocol, including the manuscript's real query and round thresholds. -/
theorem observed_signalCalibrated_alternative (N V : ℕ) (signal exponent : ℝ)
    (hNeven : Even N) (hs0 : 0 < signal) (hs1 : signal ≤ (1 / 2 : ℝ))
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * signal) :
    let P := signalCalibratedParameters N V signal exponent hNeven hs0 hs1 he hV
    ∀ (A : RandomizedObservedSamplerData N (HardVocabulary P.bankSize P.backgroundSize)) (Q R : ℕ),
      (∀ I, A.sampler.WithinOracleBudgets (P.hardFamily I).oracle Q R) →
      (∀ I, A.RiskMeasurableAt (P.hardFamily I)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ (1 / 8 : ℝ) →
      InstanceFamily.observedWorstCaseRisk P.hardFamily A ≤ ε →
      (calibratedBank signal exponent : ℝ) / 8 < (Q : ℝ) ∨
        min ((N : ℝ) / 16384) ((N : ℝ) * signal ^ 2 / (786432 * ε)) ≤ (R : ℝ) := by
  intro P A Q R hbudgets hmeas ε hε0 hε1 hrisk
  rcases P.observed_target_error_alternative A Q R hbudgets hmeas ε hε0 hε1 hrisk with hQ | hR | hr
  · left
    change calibratedBank signal exponent / 8 < Q at hQ
    have hnat : calibratedBank signal exponent < 8 * Q := by omega
    have hreal : (calibratedBank signal exponent : ℝ) < 8 * (Q : ℝ) := by exact_mod_cast hnat
    linarith
  · right
    apply (min_le_left _ _).trans
    have hnat : N < 16384 * R := by omega
    have hreal : (N : ℝ) < 16384 * (R : ℝ) := by exact_mod_cast hnat
    linarith
  · exact Or.inr ((min_le_right _ _).trans hr)

/-- The explicit main lower powers for the full feedback-aware controller
at the actual benchmark witness and original resource charges. -/
theorem main_observed_target_error_power_alternative (N V : ℕ) (ε exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ))
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * benchmarkSignal N (ε / 2)) :
    let P := benchmarkParameters N V (ε / 2) exponent hNeven hN
      (by positivity) (by linarith) he hV
    ∀ (A : RandomizedObservedSamplerData N (HardVocabulary P.bankSize P.backgroundSize)) (Q R : ℕ),
      (∀ I, A.sampler.WithinOracleBudgets (P.hardFamily I).oracle Q R) →
      (∀ I, A.RiskMeasurableAt (P.hardFamily I)) →
      InstanceFamily.observedWorstCaseRisk P.hardFamily A ≤ ε →
      ((N : ℝ) / ε ^ 2) ^ (1 / (3 * exponent)) / 16 < (Q : ℝ) ∨
        (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) / 12582912 ≤ (R : ℝ) := by
  intro P A Q R hbudgets hmeas hrisk
  have hb := benchmarkSignal_bounds N (ε / 2) hN (by positivity) (by linarith)
  rcases observed_signalCalibrated_alternative N V (benchmarkSignal N (ε / 2)) exponent
    hNeven hb.1 hb.2.1 he hV A Q R hbudgets hmeas ε hε0 hε1 hrisk with hq | hr
  · left
    have hf := calibratedBank_half_power_lt (benchmarkSignal N (ε / 2)) exponent
      hb.1 (by linarith [hb.2.1]) he
    rw [benchmarkSignal_query_power N (ε / 2) exponent hN (by positivity)] at hf
    have hp := main_query_scale_le N ε exponent hε0 he
    linarith
  · right
    rw [benchmarkSignal_round_power N (ε / 2) ε hN (by positivity)] at hr
    exact (main_round_scale_le_min N ε hN hε0 (by linarith)).trans hr

end ForestSampling
