import ForestSampling.LowerVocabularyGrowth

set_option autoImplicit false

open Filter Topology

namespace ForestSampling

universe u

/-- The public Hellinger/TV class at the finite benchmark constants.
The forest and strict target positivity are supplied by `ForestModel`.
The ranking is existential, so it is not information given to the sampler. -/
def HellingerPublicClass {N : ℕ} {V : Type u}
    [Fintype V] [DecidableEq V] [Nonempty V]
    (exponent signal radius : ℝ) (I : SamplingInstance N V) : Prop :=
  1 < exponent ∧ I.model.TailResponseRegular 1 1 ∧
    I.model.EdgeNondegenerate signal ∧
    (∃ ranking : MarginalRanking I.model, FiniteRankFrequency I.model ranking exponent 1) ∧
    I.oracle.Accurate I.model radius

/-- Every target/oracle pair satisfying the public class predicates is
included. This family is not restricted to the matching construction. -/
def hellingerPublicFamily (N : ℕ) (V : Type u)
    [Fintype V] [DecidableEq V] [Nonempty V] (exponent signal radius : ℝ) :
    {I : SamplingInstance N V // HellingerPublicClass exponent signal radius I} →
      SamplingInstance N V := Subtype.val

namespace RandomizedSamplerData

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Public admissibility imposes pathwise bounds for each actual frozen
oracle and measurability of the unchanged seed-averaged TV risk. -/
def HellingerPublicAdmissible (A : RandomizedSamplerData N V)
    (exponent signal radius : ℝ) (Q R : ℕ) : Prop :=
  ∀ I, HellingerPublicClass exponent signal radius I →
    A.sampler.WithinOracleBudgets I.oracle Q R ∧ A.RiskMeasurableAt I

/-- Worst-case seed-averaged TV risk over the entire public class. -/
noncomputable def hellingerPublicRisk (A : RandomizedSamplerData N V)
    (exponent signal radius : ℝ) : ℝ :=
  InstanceFamily.worstCaseRisk (hellingerPublicFamily N V exponent signal radius) A

/-- An equivalent convenient pointwise form of the uniform public guarantee. -/
def UniformHellingerGuarantee (A : RandomizedSamplerData N V)
    (exponent signal radius : ℝ) (Q R : ℕ) (ε : ℝ) : Prop :=
  ∀ I, HellingerPublicClass exponent signal radius I →
    A.sampler.WithinOracleBudgets I.oracle Q R ∧ A.RiskMeasurableAt I ∧ A.risk I ≤ ε

/-- A bound on the actual public supremum gives the uniform per-instance
risk bounds used for restriction, with the same sampler and seed measure. -/
theorem uniformHellingerGuarantee_of_publicRisk (A : RandomizedSamplerData N V)
    (exponent signal radius : ℝ) (Q R : ℕ) (ε : ℝ)
    (hadm : A.HellingerPublicAdmissible exponent signal radius Q R)
    (hrisk : A.hellingerPublicRisk exponent signal radius ≤ ε) :
    A.UniformHellingerGuarantee exponent signal radius Q R ε := by
  intro I hI
  refine ⟨(hadm I hI).1, (hadm I hI).2, ?_⟩
  exact (InstanceFamily.risk_le_worstCaseRisk
    (hellingerPublicFamily N V exponent signal radius) A
    (fun J ↦ (hadm J.1 J.2).2) ⟨I, hI⟩).trans hrisk

/-- A proved finite family inclusion supplies the class predicate for every
hidden instance, without adding membership as an independent premise. -/
theorem publicClass_of_finiteIncluded {ι : Type u}
    (F : ι → SamplingInstance N V) (ranking : ∀ i, MarginalRanking (F i).model)
    (exponent signal radius : ℝ)
    (hincluded : FiniteHardFamilyIncluded F ranking exponent signal radius) (i : ι) :
    HellingerPublicClass exponent signal radius (F i) := by
  have hi := hincluded.2 i
  exact ⟨hincluded.1, hi.1, hi.2.1, ⟨ranking i, hi.2.2.1⟩, hi.2.2.2⟩

/-- Restrict a uniform public sampler to any proved contained finite family.
Only the index set changes; the executable sampler and seed law do not. -/
def UniformHellingerGuarantee.restrict {A : RandomizedSamplerData N V}
    {exponent signal radius ε : ℝ} {Q R : ℕ}
    (h : A.UniformHellingerGuarantee exponent signal radius Q R ε)
    {ι : Type u} (F : ι → SamplingInstance N V)
    (ranking : ∀ i, MarginalRanking (F i).model)
    (hincluded : FiniteHardFamilyIncluded F ranking exponent signal radius) :
    InstanceFamily.OracleBudgetedSampler F Q R :=
  ⟨A, (fun i ↦ (h (F i) (publicClass_of_finiteIncluded F ranking exponent signal radius hincluded i)).1),
    fun i ↦ (h (F i) (publicClass_of_finiteIncluded F ranking exponent signal radius hincluded i)).2.1⟩

/-- The uniform public risk guarantee survives restriction to a nonempty
contained family under the unchanged seed-averaged risk definition. -/
theorem UniformHellingerGuarantee.restrictedRisk_le {A : RandomizedSamplerData N V}
    {exponent signal radius ε : ℝ} {Q R : ℕ}
    (h : A.UniformHellingerGuarantee exponent signal radius Q R ε)
    {ι : Type u} [Nonempty ι] (F : ι → SamplingInstance N V)
    (ranking : ∀ i, MarginalRanking (F i).model)
    (hincluded : FiniteHardFamilyIncluded F ranking exponent signal radius) :
    InstanceFamily.worstCaseRisk F (h.restrict F ranking hincluded).1 ≤ ε := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨i, rfl⟩
  exact (h (F i) (publicClass_of_finiteIncluded F ranking exponent signal radius hincluded i)).2.2

end RandomizedSamplerData


/-- The independently calibrated public class inherits the exact finite
benchmark lower bound, including its round minimum. -/
theorem benchmark_public_class_lower (N V : ℕ) (radius ε exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hr0 : 0 < radius) (hr1 : radius ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ))
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * benchmarkSignal N radius) :
    let P := benchmarkParameters N V radius exponent hNeven hN hr0 hr1 he hV
    letI := P.vocabularyNonempty
    ∀ (A : RandomizedSamplerData N (HardVocabulary P.bankSize P.backgroundSize)) (Q R : ℕ),
      A.HellingerPublicAdmissible exponent (benchmarkSignal N radius) radius Q R →
      A.hellingerPublicRisk exponent (benchmarkSignal N radius) radius ≤ ε →
      (2 : ℝ) ^ (1 / exponent) * ((N : ℝ) / radius ^ 2) ^ (1 / (3 * exponent)) / 16 <
          (Q : ℝ) ∨
        min ((N : ℝ) / 16384)
          ((N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * ε)) ≤ (R : ℝ) := by
  intro P
  let := P.vocabularyNonempty
  intro A Q R hadm hrisk
  let := P.instanceIndex_nonempty
  have h := A.uniformHellingerGuarantee_of_publicRisk exponent
    (benchmarkSignal N radius) radius Q R ε hadm hrisk
  have hincluded := benchmarkParameters_finiteIncluded N V radius exponent
    hNeven hN hr0 hr1 he hV
  let restricted := h.restrict P.hardFamily (P.hardFamilyRanking hV) hincluded
  exact benchmark_target_error_power_alternative N V radius exponent hNeven hN hr0 hr1 he hV Q R
    restricted ε hε0 hε1 (h.restrictedRisk_le P.hardFamily (P.hardFamilyRanking hV) hincluded)

/-- The independent-radius fixed-accuracy lower specialization holds over
the full public class, with the finite minimum removed on an actual tail. -/
theorem benchmark_public_class_lower_eventually (vocabulary : ℕ → ℕ)
    (radius ε exponent growth : ℝ) (error : ℕ → ℝ)
    (hr0 : 0 < radius) (hr1 : radius ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ)) (he : 1 < exponent)
    (hg : (1 / 3 : ℝ) < growth) (herror : Tendsto error atTop (𝓝 0))
    (hvocab : ∀ᶠ N in atTop, (vocabulary N : ℝ) = (N : ℝ) ^ (growth + error N)) :
    ∀ᶠ N in atTop,
      ∃ hN : 1 ≤ N, ∃ hV : 1 < (vocabulary N : ℝ) * benchmarkSignal N radius,
      ∀ hNeven : Even N,
      let P := benchmarkParameters N (vocabulary N) radius exponent hNeven hN hr0 hr1 he hV
      letI := P.vocabularyNonempty
      ∀ (A : RandomizedSamplerData N (HardVocabulary P.bankSize P.backgroundSize)) (Q R : ℕ),
        A.HellingerPublicAdmissible exponent (benchmarkSignal N radius) radius Q R →
        A.hellingerPublicRisk exponent (benchmarkSignal N radius) radius ≤ ε →
        (2 : ℝ) ^ (1 / exponent) * ((N : ℝ) / radius ^ 2) ^ (1 / (3 * exponent)) / 16 <
            (Q : ℝ) ∨
          (N : ℝ) ^ (1 / 3 : ℝ) * radius ^ (4 / 3 : ℝ) / (3145728 * ε) ≤ (R : ℝ) := by
  have hspread := benchmark_vocabulary_spread_eventually vocabulary radius growth error
    hr0 hg herror hvocab
  filter_upwards [hspread, benchmark_round_min_eventually radius ε hε0,
    eventually_ge_atTop (1 : ℕ)] with N hV hmin hN
  refine ⟨hN, hV, ?_⟩
  intro hNeven P
  let := P.vocabularyNonempty
  intro A Q R hadm hrisk
  have halt := benchmark_public_class_lower N (vocabulary N) radius ε exponent
    hNeven hN hr0 hr1 hε0 hε1 he hV A Q R hadm hrisk
  rwa [hmin] at halt

/-- The explicit main lower scaling now applies to samplers whose budgets
and TV-risk bound hold over every member of the public class. The benchmark
family's membership is discharged by its concrete RT/UEN/RF/A2 proof. -/
theorem main_public_class_lower (N V : ℕ) (ε exponent : ℝ)
    (hNeven : Even N) (hN : 1 ≤ N) (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ))
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * benchmarkSignal N (ε / 2)) :
    let P := benchmarkParameters N V (ε / 2) exponent hNeven hN
      (by positivity) (by linarith) he hV
    letI := P.vocabularyNonempty
    ∀ (A : RandomizedSamplerData N (HardVocabulary P.bankSize P.backgroundSize)) (Q R : ℕ),
      A.HellingerPublicAdmissible exponent (benchmarkSignal N (ε / 2)) (ε / 2) Q R →
      A.hellingerPublicRisk exponent (benchmarkSignal N (ε / 2)) (ε / 2) ≤ ε →
      ((N : ℝ) / ε ^ 2) ^ (1 / (3 * exponent)) / 16 < (Q : ℝ) ∨
        (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) / 12582912 ≤ (R : ℝ) := by
  intro P
  let := P.vocabularyNonempty
  intro A Q R hadm hrisk
  let := P.instanceIndex_nonempty
  have h := A.uniformHellingerGuarantee_of_publicRisk exponent
    (benchmarkSignal N (ε / 2)) (ε / 2) Q R ε hadm hrisk
  have hincluded := benchmarkParameters_finiteIncluded N V (ε / 2) exponent
    hNeven hN (by positivity) (by linarith) he hV
  let restricted := h.restrict P.hardFamily (P.hardFamilyRanking hV) hincluded
  exact main_target_error_power_alternative N V ε exponent hNeven hN hε0 hε1 he hV Q R
    restricted (h.restrictedRisk_le P.hardFamily (P.hardFamilyRanking hV) hincluded)

/-- The public-class main lower theorem for all sufficiently large even
lengths under the literal vocabulary-growth assumption. Vocabulary labels
are the public bank-plus-background type of cardinal `vocabulary N`. -/
theorem main_public_class_lower_eventually (vocabulary : ℕ → ℕ)
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
      ∀ (A : RandomizedSamplerData N (HardVocabulary P.bankSize P.backgroundSize)) (Q R : ℕ),
        A.HellingerPublicAdmissible exponent (benchmarkSignal N (ε / 2)) (ε / 2) Q R →
        A.hellingerPublicRisk exponent (benchmarkSignal N (ε / 2)) (ε / 2) ≤ ε →
        ((N : ℝ) / ε ^ 2) ^ (1 / (3 * exponent)) / 16 < (Q : ℝ) ∨
          (N : ℝ) ^ (1 / 3 : ℝ) * ε ^ (1 / 3 : ℝ) / 12582912 ≤ (R : ℝ) := by
  have hspread := benchmark_vocabulary_spread_eventually vocabulary (ε / 2) growth error
    (by positivity) hg herror hvocab
  filter_upwards [hspread, eventually_ge_atTop (1 : ℕ)] with N hV hN
  exact ⟨hN, hV, fun hNeven ↦ main_public_class_lower N (vocabulary N) ε exponent
    hNeven hN hε0 hε1 he hV⟩

end ForestSampling
