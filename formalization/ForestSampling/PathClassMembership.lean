import ForestSampling.PathNondegenerate
import ForestSampling.PathRankFrequency
import ForestSampling.PathInformation

set_option autoImplicit false

namespace ForestSampling
namespace PathClass

variable {B : ℕ}

namespace Parameters

/-- The edge signal is determined entirely by the binary type parameter;
changing only the number of background tokens leaves it unchanged. -/
theorem edgeSignal_eq_of_parameter {B' : ℕ} (P : Parameters B) (Q : Parameters B')
    (hp : P.p = Q.p) : P.edgeSignal = Q.edgeSignal := by
  simp only [edgeSignal, response, scaledOdds, otherOddsA, otherOddsB, hp]

theorem model_edgeNondegenerate_of_le (P : Parameters B) (n : ℕ) (signal : ℝ)
    (hs : 0 < signal) (hsmall : signal ≤ P.edgeSignal) :
    (P.model n).EdgeNondegenerate signal := by
  have hh := P.model_edgeNondegenerate n
  exact ⟨hs, hsmall.trans hh.2.1, fun _ _ hij z ↦ hsmall.trans (hh.2.2 hij z)⟩

/-- The actual exact conditional oracle has zero row error and therefore
satisfies A2 for every admissible requested oracle radius. -/
theorem model_exactOracle_accurate (P : Parameters B) (n : ℕ) (radius : ℝ)
    (hr0 : 0 ≤ radius) (hr1 : radius ≤ 1) :
    (FrozenOracle.exact (P.model n)).Accurate (P.model n) radius :=
  FrozenOracle.exact_accurate _ (by omega) hr0 hr1

end Parameters

/-- Uniform finite form of the comparison construction's verified class
inclusion and TC claim. A single positive signal and information constant
work for every vocabulary size at least three and every nonempty length.
The separate DTC and effective-TC claims are not part of this theorem. -/
theorem uniform_path_class_and_totalCorrelation (exponent : ℝ) (he : 1 < exponent) :
    ∃ signal c : ℝ, 0 < signal ∧ signal ≤ 1 ∧ 0 < c ∧
      ∀ (B n : ℕ) (hB : 0 < B) (radius : ℝ), 0 ≤ radius → radius ≤ 1 →
      let P := fromExponent B exponent he hB
      (P.model n).TailResponseRegular 1 1 ∧
      (P.model n).EdgeNondegenerate signal ∧
      FiniteRankFrequency (P.model n) (P.marginalRanking n) exponent 1 ∧
      (FrozenOracle.exact (P.model n)).Accurate (P.model n) radius ∧
      FinDist.totalCorrelation (P.model n).target = n * c := by
  let P₀ := fromExponent 1 exponent he (by omega)
  refine ⟨P₀.edgeSignal, P₀.typeInformation, P₀.edgeSignal_pos,
    P₀.edgeSignal_le_one, P₀.typeInformation_pos, ?_⟩
  intro B n hB radius hr0 hr1 P
  have hs : P.edgeSignal = P₀.edgeSignal := P.edgeSignal_eq_of_parameter P₀ rfl
  have hc : P.typeInformation = P₀.typeInformation := P.typeInformation_eq_of_parameter P₀ rfl
  refine ⟨P.model_tailResponseRegular n, ?_, ?_, P.model_exactOracle_accurate n radius hr0 hr1, ?_⟩
  · rw [← hs]
    exact P.model_edgeNondegenerate n
  · exact fromExponent_finiteRankFrequency n B exponent he hB
  · change FinDist.totalCorrelation (P.target (n + 1)) = _
    rw [P.target_totalCorrelation, hc]

end PathClass
end ForestSampling
