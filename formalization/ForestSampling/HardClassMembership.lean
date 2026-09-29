import ForestSampling.HardFiniteCalibration
import ForestSampling.HardRankFrequency

set_option autoImplicit false

namespace ForestSampling
namespace HardMatching

variable {N K B : ℕ} [Nonempty (HardVocabulary K B)]

/-- The concrete finite hard-family inclusion proposition: every matching
and private trigger assignment has the actual RT, UEN, finite RF, and A2
properties, with an explicitly constructed marginal ranking. -/
theorem finiteHardFamilyIncluded (P : HardLocalParameters K B)
    (exponent signal radius : ℝ) (he : 1 < exponent)
    (hs0 : 0 < signal) (hs : signal ≤ P.edgeCoupling)
    (hspread : 1 < ((K + B : ℕ) : ℝ) * P.triggerMass)
    (hbank : P.triggerMass ≤ (K : ℝ) ^ (-exponent))
    (hr0 : 0 ≤ radius) (hr1 : radius ≤ 1)
    (hscale : P.edgeCoupling ^ 2 * P.triggerMass ≤ radius ^ 2 / (2 * (N : ℝ))) :
    FiniteHardFamilyIncluded (family P : InstanceIndex N K → SamplingInstance N (HardVocabulary K B))
      (fun I ↦ marginalRanking P I.1 I.2 hspread) exponent signal radius := by
  refine ⟨he, ?_⟩
  intro I
  exact ⟨model_tailResponseRegular P I.1 I.2,
    model_edgeNondegenerate P I.1 I.2 signal hs0 hs,
    model_finiteRankFrequency P I.1 I.2 exponent (by linarith) hspread hbank,
    model_oracleAccurate P I.1 I.2 radius hr0 hr1 hscale⟩

end HardMatching

namespace NonlinearMatchingParameters
variable {N : ℕ}

/-- The public vocabulary cardinal is exactly the bank plus its background. -/
theorem bank_add_background_eq_vocab (P : NonlinearMatchingParameters N) :
    P.bankSize + P.backgroundSize = P.vocabSize :=
  Nat.add_sub_of_le P.bank_lt_vocab.le

/-- The actual common marginal ranking for every instance in the current
finite hard family. No ordering hypothesis on hidden marginals is assumed. -/
noncomputable def hardFamilyRanking (P : NonlinearMatchingParameters N)
    (hspread : 1 < (P.vocabSize : ℝ) * P.triggerMass)
    (I : HardMatching.InstanceIndex N P.bankSize) : MarginalRanking (P.hardFamily I).model :=
  HardMatching.marginalRanking P.toHardLocal I.1 I.2
    (by rw [P.bank_add_background_eq_vocab]; exact hspread)

/-- Class inclusion for the current nonlinear parameter object, using the
public vocabulary cardinal and the manuscript's finite scalar inequalities. -/
theorem hardFamily_finiteIncluded (P : NonlinearMatchingParameters N)
    [Nonempty (HardVocabulary P.bankSize P.backgroundSize)]
    (exponent signal radius : ℝ) (he : 1 < exponent)
    (hs0 : 0 < signal) (hs : signal ≤ P.edgeCoupling)
    (hspread : 1 < (P.vocabSize : ℝ) * P.triggerMass)
    (hbank : P.triggerMass ≤ (P.bankSize : ℝ) ^ (-exponent))
    (hr0 : 0 ≤ radius) (hr1 : radius ≤ 1)
    (hscale : P.edgeCoupling ^ 2 * P.triggerMass ≤ radius ^ 2 / (2 * (N : ℝ))) :
    FiniteHardFamilyIncluded P.hardFamily (P.hardFamilyRanking hspread) exponent signal radius :=
  HardMatching.finiteHardFamilyIncluded P.toHardLocal exponent signal radius he hs0 hs
    (by rw [P.bank_add_background_eq_vocab]; exact hspread) hbank hr0 hr1 hscale

end NonlinearMatchingParameters

/-- The signal-calibrated integer witness is an actual contained finite
family at the declared public parameters. Vocabulary growth is a separate
asymptotic assumption and is not included in this finite statement. -/
theorem signalCalibratedParameters_finiteIncluded (N V : ℕ) (signal exponent radius : ℝ)
    (hN : Even N) (hs0 : 0 < signal) (hs1 : signal ≤ (1 / 2 : ℝ))
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * signal)
    (hr0 : 0 ≤ radius) (hr1 : radius ≤ 1)
    (hscale : signal ^ 3 ≤ radius ^ 2 / (2 * (N : ℝ))) :
    let P := signalCalibratedParameters N V signal exponent hN hs0 hs1 he hV
    letI : Nonempty (HardVocabulary P.bankSize P.backgroundSize) :=
      ⟨Sum.inr ⟨0, P.backgroundSize_pos⟩⟩
    FiniteHardFamilyIncluded P.hardFamily (P.hardFamilyRanking hV) exponent signal radius := by
  intro P
  let : Nonempty (HardVocabulary P.bankSize P.backgroundSize) :=
    ⟨Sum.inr ⟨0, P.backgroundSize_pos⟩⟩
  apply P.hardFamily_finiteIncluded exponent signal radius he hs0 le_rfl hV
    (signalCalibratedParameters_rank N V signal exponent hN hs0 hs1 he hV) hr0 hr1
  change signal ^ 2 * signal ≤ _
  convert hscale using 1 <;> ring

end ForestSampling
