import ForestSampling.ArbitraryVocabularyLower

set_option autoImplicit false
open Filter Topology

namespace ForestSampling

/-- Independent-radius calibration for the complete commit-feedback
protocol, at the actually constructed benchmark hard family. -/
theorem benchmark_observed_target_error_power_alternative (N V : ℕ) (radius ε exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hr0 : 0 < radius) (hr1 : radius ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ)) (he : 1 < exponent)
    (hV : 1 < (V : ℝ) * benchmarkSignal N radius) :
    let P := benchmarkParameters N V radius exponent hNeven hN hr0 hr1 he hV
    ∀ (A : RandomizedObservedSamplerData N (HardVocabulary P.bankSize P.backgroundSize)) (Q R : ℕ),
      (∀ I, A.sampler.WithinOracleBudgets (P.hardFamily I).oracle Q R) →
      (∀ I, A.RiskMeasurableAt (P.hardFamily I)) →
      InstanceFamily.observedWorstCaseRisk P.hardFamily A ≤ ε →
      (2 : ℝ) ^ (1 / exponent) * ((N : ℝ) / radius ^ 2) ^ (1 / (3 * exponent)) / 16 <
          (Q : ℝ) ∨
        min ((N : ℝ) / 16384)
          ((N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * ε)) ≤ (R : ℝ) := by
  intro P A Q R hbudgets hmeas hrisk
  have hb := benchmarkSignal_bounds N radius hN hr0 hr1
  rcases observed_signalCalibrated_alternative N V (benchmarkSignal N radius) exponent
    hNeven hb.1 hb.2.1 he hV A Q R hbudgets hmeas ε hε0 hε1 hrisk with hq | hr
  · left
    have hf := calibratedBank_half_power_lt (benchmarkSignal N radius) exponent
      hb.1 (by linarith [hb.2.1]) he
    rw [benchmarkSignal_query_power N radius exponent hN hr0] at hf
    linarith
  · right
    rwa [benchmarkSignal_round_power N radius ε hN hr0] at hr

/-- The finite independent-radius lower bound over the full public class
on any finite vocabulary. Relabeling and commit feedback are both retained. -/
theorem benchmark_observed_public_class_lower_any_vocabulary (N : ℕ) (V : Type)
    [Fintype V] [DecidableEq V] [Nonempty V] (radius ε exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hr0 : 0 < radius) (hr1 : radius ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ)) (he : 1 < exponent)
    (hV : 1 < (Fintype.card V : ℝ) * benchmarkSignal N radius)
    (A : RandomizedObservedSamplerData N V) (Q R : ℕ)
    (hadm : A.HellingerPublicAdmissible exponent (benchmarkSignal N radius) radius Q R)
    (hrisk : A.hellingerPublicRisk exponent (benchmarkSignal N radius) radius ≤ ε) :
    (2 : ℝ) ^ (1 / exponent) * ((N : ℝ) / radius ^ 2) ^ (1 / (3 * exponent)) / 16 <
        (Q : ℝ) ∨
      min ((N : ℝ) / 16384)
        ((N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * ε)) ≤ (R : ℝ) := by
  let P := benchmarkParameters N (Fintype.card V) radius exponent hNeven hN hr0 hr1 he hV
  letI := P.vocabularyNonempty
  letI := P.instanceIndex_nonempty
  let e : HardVocabulary P.bankSize P.backgroundSize ≃ V :=
    Fintype.equivOfCardEq P.hardVocabulary_card
  let B := A.relabel e.symm
  have hincluded := benchmarkParameters_finiteIncluded N (Fintype.card V) radius exponent
    hNeven hN hr0 hr1 he hV
  have hclass : ∀ I, HellingerPublicClass exponent (benchmarkSignal N radius) radius
      (P.hardFamily I) := fun I ↦ RandomizedSamplerData.publicClass_of_finiteIncluded
        P.hardFamily (P.hardFamilyRanking hV) exponent (benchmarkSignal N radius) radius
        hincluded I
  have htransport : ∀ I, HellingerPublicClass exponent (benchmarkSignal N radius) radius
      (VocabularyEquivalence.samplingInstance e (P.hardFamily I)) := by
    intro I
    exact VocabularyEquivalence.publicClass e (P.hardFamily I) exponent
      (benchmarkSignal N radius) radius (hclass I)
  apply benchmark_observed_target_error_power_alternative N (Fintype.card V) radius ε exponent
    hNeven hN hr0 hr1 hε0 hε1 he hV B Q R
  · intro I
    exact ObservedSampler.withinOracleBudgets_relabel_symm e A.sampler
      (P.hardFamily I).oracle Q R
      (hadm (VocabularyEquivalence.samplingInstance e (P.hardFamily I)) (htransport I)).1
  · intro I
    exact (A.riskMeasurableAt_relabel_symm_iff e (P.hardFamily I)
      (VocabularyEquivalence.samplingInstance e (P.hardFamily I)) rfl rfl).mpr
      (hadm (VocabularyEquivalence.samplingInstance e (P.hardFamily I)) (htransport I)).2
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨I, rfl⟩
    change (A.relabel e.symm).risk (P.hardFamily I) ≤ ε
    rw [A.risk_relabel_symm e (P.hardFamily I)
      (VocabularyEquivalence.samplingInstance e (P.hardFamily I)) rfl rfl]
    exact (A.risk_le_hellingerPublicRisk exponent (benchmarkSignal N radius) radius
      Q R hadm _ (htransport I)).trans hrisk

/-- At fixed positive radius and accuracy, literal vocabulary growth
removes the finite minimum on a genuine tail of sequence lengths. -/
theorem benchmark_observed_public_class_lower_any_vocabulary_eventually
    (Vocabulary : ℕ → Type) [∀ N, Fintype (Vocabulary N)] [∀ N, DecidableEq (Vocabulary N)]
    [∀ N, Nonempty (Vocabulary N)] (radius ε exponent growth : ℝ) (error : ℕ → ℝ)
    (hr0 : 0 < radius) (hr1 : radius ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ)) (he : 1 < exponent)
    (hg : (1 / 3 : ℝ) < growth) (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop,
      (Fintype.card (Vocabulary N) : ℝ) = (N : ℝ) ^ (growth + error N)) :
    ∀ᶠ N in atTop, ∀ hNeven : Even N,
      ∀ (A : RandomizedObservedSamplerData N (Vocabulary N)) (Q R : ℕ),
        A.HellingerPublicAdmissible exponent (benchmarkSignal N radius) radius Q R →
        A.hellingerPublicRisk exponent (benchmarkSignal N radius) radius ≤ ε →
        (2 : ℝ) ^ (1 / exponent) * ((N : ℝ) / radius ^ 2) ^ (1 / (3 * exponent)) / 16 <
            (Q : ℝ) ∨
          (N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * ε) ≤ (R : ℝ) := by
  have hspread := benchmark_vocabulary_spread_eventually (fun N ↦ Fintype.card (Vocabulary N))
    radius growth error hr0 hg herror hvocab
  filter_upwards [hspread, benchmark_round_min_eventually radius ε hε0,
    eventually_ge_atTop (1 : ℕ)] with N hV hmin hN
  intro hNeven A Q R hadm hrisk
  have halt := benchmark_observed_public_class_lower_any_vocabulary N (Vocabulary N)
    radius ε exponent hNeven hN hr0 hr1 hε0 hε1 he hV A Q R hadm hrisk
  rwa [hmin] at halt

end ForestSampling
