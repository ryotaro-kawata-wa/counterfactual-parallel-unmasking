import ForestSampling.ObservedVocabularyTransport
import ForestSampling.VocabularyModelTransport
import ForestSampling.ObservedPublicClassLower

set_option autoImplicit false
open Filter Topology

namespace ForestSampling

/-- The main lower resource alternative for an arbitrary finite public
vocabulary, with every commit-row feedback available to the controller.
The hard family, its class membership, and the relabeling of the actual
controller are constructed within the proof. -/
theorem main_observed_public_class_lower_any_vocabulary (N : ℕ) (V : Type)
    [Fintype V] [DecidableEq V] [Nonempty V] (ε exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ))
    (he : 1 < exponent)
    (hV : 1 < (Fintype.card V : ℝ) * benchmarkSignal N (ε / 2))
    (A : RandomizedObservedSamplerData N V) (Q R : ℕ)
    (hadm : A.HellingerPublicAdmissible exponent (benchmarkSignal N (ε / 2)) (ε / 2) Q R)
    (hrisk : A.hellingerPublicRisk exponent (benchmarkSignal N (ε / 2)) (ε / 2) ≤ ε) :
    ((N : ℝ) / ε ^ 2) ^ (1 / (3 * exponent)) / 16 < (Q : ℝ) ∨
      (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) / 12582912 ≤ (R : ℝ) := by
  let P := benchmarkParameters N (Fintype.card V) (ε / 2) exponent hNeven hN
    (by positivity) (by linarith) he hV
  letI := P.vocabularyNonempty
  letI := P.instanceIndex_nonempty
  let e : HardVocabulary P.bankSize P.backgroundSize ≃ V :=
    Fintype.equivOfCardEq P.hardVocabulary_card
  let B := A.relabel e.symm
  have hincluded := benchmarkParameters_finiteIncluded N (Fintype.card V) (ε / 2) exponent
    hNeven hN (by positivity) (by linarith) he hV
  have hclass : ∀ I, HellingerPublicClass exponent (benchmarkSignal N (ε / 2)) (ε / 2)
      (P.hardFamily I) := fun I ↦ RandomizedSamplerData.publicClass_of_finiteIncluded
        P.hardFamily (P.hardFamilyRanking hV) exponent (benchmarkSignal N (ε / 2)) (ε / 2)
        hincluded I
  have htransport : ∀ I, HellingerPublicClass exponent (benchmarkSignal N (ε / 2)) (ε / 2)
      (VocabularyEquivalence.samplingInstance e (P.hardFamily I)) := by
    intro I
    exact VocabularyEquivalence.publicClass e (P.hardFamily I) exponent
      (benchmarkSignal N (ε / 2)) (ε / 2) (hclass I)
  apply main_observed_target_error_power_alternative N (Fintype.card V) ε exponent
    hNeven hN hε0 hε1 he hV B Q R
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
    exact (A.risk_le_hellingerPublicRisk exponent (benchmarkSignal N (ε / 2)) (ε / 2)
      Q R hadm _ (htransport I)).trans hrisk

/-- Literal eventual vocabulary growth implies the main lower bound for
arbitrary public token types at every sufficiently large even length.
This is a uniform per-length alternative, allowing which resource is large
to vary with the controller and the sequence length. -/
theorem main_observed_public_class_lower_any_vocabulary_eventually
    (Vocabulary : ℕ → Type) [∀ N, Fintype (Vocabulary N)] [∀ N, DecidableEq (Vocabulary N)]
    [∀ N, Nonempty (Vocabulary N)] (ε exponent growth : ℝ) (error : ℕ → ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ)) (he : 1 < exponent)
    (hg : (1 / 3 : ℝ) < growth) (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop,
      (Fintype.card (Vocabulary N) : ℝ) = (N : ℝ) ^ (growth + error N)) :
    ∀ᶠ N in atTop, ∀ hNeven : Even N,
      ∀ (A : RandomizedObservedSamplerData N (Vocabulary N)) (Q R : ℕ),
        A.HellingerPublicAdmissible exponent (benchmarkSignal N (ε / 2)) (ε / 2) Q R →
        A.hellingerPublicRisk exponent (benchmarkSignal N (ε / 2)) (ε / 2) ≤ ε →
        ((N : ℝ) / ε ^ 2) ^ (1 / (3 * exponent)) / 16 < (Q : ℝ) ∨
          (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) / 12582912 ≤ (R : ℝ) := by
  have hspread := benchmark_vocabulary_spread_eventually (fun N ↦ Fintype.card (Vocabulary N))
    (ε / 2) growth error (by positivity) hg herror hvocab
  filter_upwards [hspread, eventually_ge_atTop (1 : ℕ)] with N hV hN
  intro hNeven A Q R hadm hrisk
  exact main_observed_public_class_lower_any_vocabulary N (Vocabulary N) ε exponent
    hNeven hN hε0 hε1 he hV A Q R hadm hrisk

end ForestSampling
