import ForestSampling.ObservedLower
import ForestSampling.PublicClassLower

set_option autoImplicit false
open Filter Topology

namespace ForestSampling

universe u

namespace RandomizedObservedSamplerData

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Public admissibility for the manuscript's full observation protocol.
Commit probability rows are available without an extra charged probe. -/
def HellingerPublicAdmissible (A : RandomizedObservedSamplerData N V)
    (exponent signal radius : ℝ) (Q R : ℕ) : Prop :=
  ∀ I, HellingerPublicClass exponent signal radius I →
    A.sampler.WithinOracleBudgets I.oracle Q R ∧ A.RiskMeasurableAt I

/-- The actual public supremum of seed-averaged TV risk, evaluated with
commit feedback retained by the controller. -/
noncomputable def hellingerPublicRisk (A : RandomizedObservedSamplerData N V)
    (exponent signal radius : ℝ) : ℝ :=
  InstanceFamily.observedWorstCaseRisk (hellingerPublicFamily N V exponent signal radius) A

/-- Every member of the full public class lies below the same supremum.
Risk boundedness and measurability are transferred by exact simulation. -/
theorem risk_le_hellingerPublicRisk (A : RandomizedObservedSamplerData N V)
    (exponent signal radius : ℝ) (Q R : ℕ)
    (hadm : A.HellingerPublicAdmissible exponent signal radius Q R)
    (I : SamplingInstance N V) (hI : HellingerPublicClass exponent signal radius I) :
    A.risk I ≤ A.hellingerPublicRisk exponent signal radius := by
  let F := hellingerPublicFamily N V exponent signal radius
  have hmeas : ∀ J, A.compile.RiskMeasurableAt (F J) := by
    intro J
    exact (A.riskMeasurableAt_compile_iff (F J)).mpr (hadm J.1 J.2).2
  calc
    A.risk I = A.compile.risk I := (A.risk_compile I).symm
    _ ≤ InstanceFamily.worstCaseRisk F A.compile :=
      InstanceFamily.risk_le_worstCaseRisk F A.compile hmeas ⟨I, hI⟩
    _ = _ := InstanceFamily.worstCaseRisk_compile F A

end RandomizedObservedSamplerData

/-- The main explicit lower powers for arbitrary full-observation public
controllers on the canonical vocabulary labeling. The hard-family class
membership and the feedback simulation are both proved, not assumed. -/
theorem main_observed_public_class_lower (N V : ℕ) (ε exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ))
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * benchmarkSignal N (ε / 2)) :
    let P := benchmarkParameters N V (ε / 2) exponent hNeven hN
      (by positivity) (by linarith) he hV
    letI := P.vocabularyNonempty
    ∀ (A : RandomizedObservedSamplerData N (HardVocabulary P.bankSize P.backgroundSize)) (Q R : ℕ),
      A.HellingerPublicAdmissible exponent (benchmarkSignal N (ε / 2)) (ε / 2) Q R →
      A.hellingerPublicRisk exponent (benchmarkSignal N (ε / 2)) (ε / 2) ≤ ε →
      ((N : ℝ) / ε ^ 2) ^ (1 / (3 * exponent)) / 16 < (Q : ℝ) ∨
        (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) / 12582912 ≤ (R : ℝ) := by
  intro P
  let := P.vocabularyNonempty
  intro A Q R hadm hrisk
  let := P.instanceIndex_nonempty
  have hincluded := benchmarkParameters_finiteIncluded N V (ε / 2) exponent
    hNeven hN (by positivity) (by linarith) he hV
  have hclass : ∀ I, HellingerPublicClass exponent (benchmarkSignal N (ε / 2)) (ε / 2)
      (P.hardFamily I) := fun I ↦ RandomizedSamplerData.publicClass_of_finiteIncluded
        P.hardFamily (P.hardFamilyRanking hV) exponent (benchmarkSignal N (ε / 2)) (ε / 2)
        hincluded I
  apply main_observed_target_error_power_alternative N V ε exponent hNeven hN hε0 hε1 he hV
    A Q R (fun I ↦ (hadm (P.hardFamily I) (hclass I)).1)
      (fun I ↦ (hadm (P.hardFamily I) (hclass I)).2)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨I, rfl⟩
  exact (A.risk_le_hellingerPublicRisk exponent (benchmarkSignal N (ε / 2)) (ε / 2)
    Q R hadm (P.hardFamily I) (hclass I)).trans hrisk

/-- The full-observation main lower theorem for every sufficiently large
even length under the literal public vocabulary-growth condition. -/
theorem main_observed_public_class_lower_eventually (vocabulary : ℕ → ℕ)
    (ε exponent growth : ℝ) (error : ℕ → ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ)) (he : 1 < exponent)
    (hg : (1 / 3 : ℝ) < growth) (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (vocabulary N : ℝ) = (N : ℝ) ^ (growth + error N)) :
    ∀ᶠ N in atTop,
      ∃ hN : 1 ≤ N, ∃ hV : 1 < (vocabulary N : ℝ) * benchmarkSignal N (ε / 2),
      ∀ hNeven : Even N,
      let P := benchmarkParameters N (vocabulary N) (ε / 2) exponent hNeven hN
        (by positivity) (by linarith) he hV
      letI := P.vocabularyNonempty
      ∀ (A : RandomizedObservedSamplerData N (HardVocabulary P.bankSize P.backgroundSize)) (Q R : ℕ),
        A.HellingerPublicAdmissible exponent (benchmarkSignal N (ε / 2)) (ε / 2) Q R →
        A.hellingerPublicRisk exponent (benchmarkSignal N (ε / 2)) (ε / 2) ≤ ε →
        ((N : ℝ) / ε ^ 2) ^ (1 / (3 * exponent)) / 16 < (Q : ℝ) ∨
          (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) / 12582912 ≤ (R : ℝ) := by
  have hspread := benchmark_vocabulary_spread_eventually vocabulary (ε / 2) growth error
    (by positivity) hg herror hvocab
  filter_upwards [hspread, eventually_ge_atTop (1 : ℕ)] with N hV hN
  exact ⟨hN, hV, fun hNeven ↦ main_observed_public_class_lower N (vocabulary N) ε exponent
    hNeven hN hε0 hε1 he hV⟩

end ForestSampling
