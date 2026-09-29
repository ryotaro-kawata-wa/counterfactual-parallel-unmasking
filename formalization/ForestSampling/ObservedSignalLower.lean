import ForestSampling.ObservedBenchmarkLower

set_option autoImplicit false

namespace ForestSampling

/-- The finite signal-calibrated lower bound on the full public class,
with arbitrary finite vocabulary and all ordinary commit feedback. The
actual hard-family inclusion is proved from the cubic signal condition. -/
theorem signalCalibrated_observed_public_class_lower_any_vocabulary (N : ℕ) (V : Type)
    [Fintype V] [DecidableEq V] [Nonempty V] (signal radius ε exponent : ℝ)
    (hNeven : Even N) (hs0 : 0 < signal) (hs1 : signal ≤ (1 / 2 : ℝ))
    (hr0 : 0 ≤ radius) (hr1 : radius ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ)) (he : 1 < exponent)
    (hV : 1 < (Fintype.card V : ℝ) * signal)
    (hscale : signal ^ 3 ≤ radius ^ 2 / (2 * (N : ℝ)))
    (A : RandomizedObservedSamplerData N V) (Q R : ℕ)
    (hadm : A.HellingerPublicAdmissible exponent signal radius Q R)
    (hrisk : A.hellingerPublicRisk exponent signal radius ≤ ε) :
    (⌊signal ^ (-1 / exponent)⌋₊ : ℝ) / 8 < (Q : ℝ) ∨
      min ((N : ℝ) / 16384) ((N : ℝ) * signal ^ 2 / (786432 * ε)) ≤ (R : ℝ) := by
  let P := signalCalibratedParameters N (Fintype.card V) signal exponent
    hNeven hs0 hs1 he hV
  letI := P.vocabularyNonempty
  letI := P.instanceIndex_nonempty
  let e : HardVocabulary P.bankSize P.backgroundSize ≃ V :=
    Fintype.equivOfCardEq P.hardVocabulary_card
  let B := A.relabel e.symm
  have hincluded := signalCalibratedParameters_finiteIncluded N (Fintype.card V)
    signal exponent radius hNeven hs0 hs1 he hV hr0 hr1 hscale
  have hclass : ∀ I, HellingerPublicClass exponent signal radius (P.hardFamily I) :=
    fun I ↦ RandomizedSamplerData.publicClass_of_finiteIncluded
      P.hardFamily (P.hardFamilyRanking hV) exponent signal radius hincluded I
  have htransport : ∀ I, HellingerPublicClass exponent signal radius
      (VocabularyEquivalence.samplingInstance e (P.hardFamily I)) := by
    intro I
    exact VocabularyEquivalence.publicClass e (P.hardFamily I) exponent signal radius (hclass I)
  apply observed_signalCalibrated_alternative N (Fintype.card V) signal exponent
    hNeven hs0 hs1 he hV B Q R
  · intro I
    exact ObservedSampler.withinOracleBudgets_relabel_symm e A.sampler
      (P.hardFamily I).oracle Q R
      (hadm (VocabularyEquivalence.samplingInstance e (P.hardFamily I)) (htransport I)).1
  · intro I
    exact (A.riskMeasurableAt_relabel_symm_iff e (P.hardFamily I)
      (VocabularyEquivalence.samplingInstance e (P.hardFamily I)) rfl rfl).mpr
      (hadm (VocabularyEquivalence.samplingInstance e (P.hardFamily I)) (htransport I)).2
  · exact hε0
  · exact hε1
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨I, rfl⟩
    change (A.relabel e.symm).risk (P.hardFamily I) ≤ ε
    rw [A.risk_relabel_symm e (P.hardFamily I)
      (VocabularyEquivalence.samplingInstance e (P.hardFamily I)) rfl rfl]
    exact (A.risk_le_hellingerPublicRisk exponent signal radius Q R hadm _
      (htransport I)).trans hrisk

/-- The benchmark specialization retains the exact integer floor and finite
minimum printed in the manuscript's direct finite lower alternative. -/
theorem benchmark_observed_public_class_lower_floor_any_vocabulary (N : ℕ) (V : Type)
    [Fintype V] [DecidableEq V] [Nonempty V] (radius ε exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hr0 : 0 < radius) (hr1 : radius ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ)) (he : 1 < exponent)
    (hV : 1 < (Fintype.card V : ℝ) * benchmarkSignal N radius)
    (A : RandomizedObservedSamplerData N V) (Q R : ℕ)
    (hadm : A.HellingerPublicAdmissible exponent (benchmarkSignal N radius) radius Q R)
    (hrisk : A.hellingerPublicRisk exponent (benchmarkSignal N radius) radius ≤ ε) :
    (⌊(2 : ℝ) ^ (1 / exponent) *
        ((N : ℝ) / radius ^ 2) ^ (1 / (3 * exponent))⌋₊ : ℝ) / 8 < (Q : ℝ) ∨
      min ((N : ℝ) / 16384)
        ((N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * ε)) ≤ (R : ℝ) := by
  have hb := benchmarkSignal_bounds N radius hN hr0 hr1
  have halt := signalCalibrated_observed_public_class_lower_any_vocabulary N V
    (benchmarkSignal N radius) radius ε exponent hNeven hb.1 hb.2.1 hr0.le hr1
    hε0 hε1 he hV hb.2.2 A Q R hadm hrisk
  rwa [benchmarkSignal_query_power N radius exponent hN hr0,
    benchmarkSignal_round_power N radius ε hN hr0] at halt

end ForestSampling
