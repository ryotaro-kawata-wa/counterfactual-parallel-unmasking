import ForestSampling.PathEffectiveTCLower
import ForestSampling.PathBenchmarkMembership

set_option autoImplicit false

namespace ForestSampling.PathClass
noncomputable section

/-- Explicit linear lower and upper bounds for the actual independently
masked path information integral, valid from six vertices onward. -/
theorem Parameters.effectiveTC_linear_bounds {B : ℕ} (P : Parameters B)
    (n : ℕ) (hn : 5 ≤ n) :
    (n+1 : ℝ) * (P.adjacentInformationConstant * Real.exp (-4) / 4) ≤
        MaskedInformation.effectiveTC (P.target (n+1)) (P.target_positive _) ∧
    MaskedInformation.effectiveTC (P.target (n+1)) (P.target_positive _) ≤
        (n+1 : ℝ) * (2 * Real.log 2) := by
  constructor
  · have hb := P.effectiveTC_ge_adjacent n
    have hcast : ((n+1-3 : ℕ) : ℝ) = (n : ℝ)-2 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hscale : (n+1 : ℝ) ≤ 2 * ((n+1-3 : ℕ) : ℝ) := by
      rw [hcast]
      have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hc : 0 ≤ P.adjacentInformationConstant * Real.exp (-4) / 4 := by
      exact div_nonneg (mul_nonneg P.adjacentInformationConstant_pos.le (Real.exp_pos _).le) (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hscale hc
    nlinarith only [hm,hb]
  · have hh := P.effectiveTC_le n
    nlinarith only [hh]

/-- The comparison corollary with both constants fixed before path length
and vocabulary: effective TC is Theta(N) for the exact manuscript path.
All bounds concern the actual independent erasure law and ordered pair CMI. -/
theorem uniform_effectiveTC_linear_bounds (exponent : ℝ) (he : 1 < exponent) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ (B n : ℕ) (hB : 0 < B), 5 ≤ n →
        let P := fromExponent B exponent he hB
        (n+1 : ℝ) * lower ≤ MaskedInformation.effectiveTC (P.target (n+1)) (P.target_positive _) ∧
        MaskedInformation.effectiveTC (P.target (n+1)) (P.target_positive _) ≤ (n+1 : ℝ) * upper := by
  let P₀ := fromExponent 1 exponent he (by norm_num)
  refine ⟨P₀.adjacentInformationConstant * Real.exp (-4) / 4, 2 * Real.log 2,
    EffectiveTCIntegral.lower_constant_pos P₀.adjacentInformationConstant_pos,
    mul_pos (by norm_num) (Real.log_pos (by norm_num)), ?_⟩
  intro B n hB hn P
  have heq : P.adjacentInformationConstant = P₀.adjacentInformationConstant :=
    P.adjacentInformationConstant_eq_of_parameter P₀ rfl
  simpa only [heq] using P.effectiveTC_linear_bounds n hn

end
end ForestSampling.PathClass
