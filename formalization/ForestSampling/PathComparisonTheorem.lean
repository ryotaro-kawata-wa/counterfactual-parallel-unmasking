import ForestSampling.PathClassMembership
import ForestSampling.PathDTC

set_option autoImplicit false

namespace ForestSampling
namespace PathClass

/-- The comparison proposition's actual finite path witness, with a
single positive signal and two positive information constants for every
vocabulary size. The exact identities imply both linear-order claims;
the separate effective-TC corollary is not assumed here. -/
theorem uniform_path_class_and_information (exponent : ℝ) (he : 1 < exponent) :
    ∃ signal c c' : ℝ, 0 < signal ∧ signal ≤ 1 ∧ 0 < c ∧ 0 < c' ∧
      ∀ (B n : ℕ) (hB : 0 < B) (radius : ℝ), 0 ≤ radius → radius ≤ 1 →
      let P := fromExponent B exponent he hB
      (P.model (n + 1)).TailResponseRegular 1 1 ∧
      (P.model (n + 1)).EdgeNondegenerate signal ∧
      FiniteRankFrequency (P.model (n + 1)) (P.marginalRanking (n + 1)) exponent 1 ∧
      (FrozenOracle.exact (P.model (n + 1))).Accurate (P.model (n + 1)) radius ∧
      FinDist.totalCorrelation (P.model (n + 1)).target = (n + 1 : ℕ) * c ∧
      FinDist.dualTotalCorrelation (P.model (n + 1)).target = c + n * c' := by
  let P₀ := fromExponent 1 exponent he (by omega)
  refine ⟨P₀.edgeSignal, P₀.typeInformation, P₀.typeConditionalInformation,
    P₀.edgeSignal_pos, P₀.edgeSignal_le_one, P₀.typeInformation_pos,
    P₀.typeConditionalInformation_pos, ?_⟩
  intro B n hB radius hr0 hr1 P
  have hs : P.edgeSignal = P₀.edgeSignal := P.edgeSignal_eq_of_parameter P₀ rfl
  have hc : P.typeInformation = P₀.typeInformation := P.typeInformation_eq_of_parameter P₀ rfl
  have hc' : P.typeConditionalInformation = P₀.typeConditionalInformation :=
    P.typeConditionalInformation_eq_of_parameter P₀ rfl
  refine ⟨P.model_tailResponseRegular (n + 1), ?_, ?_,
    P.model_exactOracle_accurate (n + 1) radius hr0 hr1, ?_, ?_⟩
  · rw [← hs]
    exact P.model_edgeNondegenerate (n + 1)
  · exact fromExponent_finiteRankFrequency (n + 1) B exponent he hB
  · change FinDist.totalCorrelation (P.target (n + 1 + 1)) = _
    rw [P.target_totalCorrelation, hc]
  · change FinDist.dualTotalCorrelation (P.target (n + 2)) = _
    rw [P.target_dualTotalCorrelation, hc, hc']

/-- Explicit two-sided linear bounds for every path length at least
three; both constants are uniform in the background vocabulary size. -/
theorem Parameters.information_linear_bounds {B : ℕ} (P : Parameters B) (n : ℕ) :
    ((n + 3 : ℕ) : ℝ) * (P.typeInformation / 2) ≤
        FinDist.totalCorrelation (P.target (n + 3)) ∧
    FinDist.totalCorrelation (P.target (n + 3)) ≤
        ((n + 3 : ℕ) : ℝ) * P.typeInformation ∧
    ((n + 3 : ℕ) : ℝ) * (min P.typeInformation P.typeConditionalInformation / 2) ≤
        FinDist.dualTotalCorrelation (P.target (n + 3)) ∧
    FinDist.dualTotalCorrelation (P.target (n + 3)) ≤
        ((n + 3 : ℕ) : ℝ) * max P.typeInformation P.typeConditionalInformation := by
  rw [show n + 3 = (n + 2) + 1 by omega, P.target_totalCorrelation]
  rw [show n + 2 + 1 = (n + 1) + 2 by omega, P.target_dualTotalCorrelation]
  have hc := P.typeInformation_pos
  have hc' := P.typeConditionalInformation_pos
  have hmin0 : 0 ≤ min P.typeInformation P.typeConditionalInformation := le_min hc.le hc'.le
  have hmin1 := min_le_left P.typeInformation P.typeConditionalInformation
  have hmin2 := min_le_right P.typeInformation P.typeConditionalInformation
  have hmax1 := le_max_left P.typeInformation P.typeConditionalInformation
  have hmax2 := le_max_right P.typeInformation P.typeConditionalInformation
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hminmul := mul_le_mul_of_nonneg_left hmin2 (by positivity : (0 : ℝ) ≤ n + 1)
  have hmaxmul := mul_le_mul_of_nonneg_left hmax2 (by positivity : (0 : ℝ) ≤ n + 1)
  push_cast
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end PathClass
end ForestSampling
