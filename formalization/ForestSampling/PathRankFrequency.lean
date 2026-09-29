import ForestSampling.PathClass
import ForestSampling.PaperStatements

set_option autoImplicit false

namespace ForestSampling
namespace PathClass

variable {B : ℕ}

/-- The comparison vocabulary is ordered explicitly as the first token,
the second token, and then the background labels. -/
def rankEquiv : Token B ≃ Fin (Fintype.card (Token B)) :=
  (Equiv.optionCongr (finSuccEquiv B).symm).trans
    ((finSuccEquiv (B + 1)).symm.trans (finCongr (by simp [Token])))

@[simp] theorem rankEquiv_first_val :
    (rankEquiv (none : Token B)).val = 0 := rfl

@[simp] theorem rankEquiv_second_val :
    (rankEquiv (some none : Token B)).val = 1 := rfl

@[simp] theorem rankEquiv_background_val (a : Fin B) :
    (rankEquiv (some (some a) : Token B)).val = a.val + 2 := rfl

namespace Parameters

noncomputable section

theorem backgroundMass_le_second (P : Parameters B) : P.p / (2 * B) ≤ P.p / 2 := by
  apply div_le_div_of_nonneg_left P.p_pos.le (by norm_num : (0 : ℝ) < 2)
  have hh : (1 : ℝ) ≤ B := by exact_mod_cast P.background_pos
  linarith

theorem tokenMass_le_first (P : Parameters B) (a : Token B) : P.tokenMass a ≤ 1 - P.p := by
  cases a with
  | none => exact le_rfl
  | some a =>
      cases a with
      | none => simp only [tokenMass]; linarith [P.p_lt_half]
      | some a => exact P.backgroundMass_le_second.trans (by linarith [P.p_lt_half])

/-- The ranking's monotonicity is proved from the actual path marginal;
it is not an additional assumption on the comparison model. -/
def marginalRanking (P : Parameters B) (n : ℕ) : MarginalRanking (P.model n) where
  token _ := rankEquiv.symm
  token_bijective _ := rankEquiv.symm.bijective
  nonincreasing := by
    intro i k l hkl
    rw [model_marginal]
    obtain ⟨a, rfl⟩ := rankEquiv.surjective k
    obtain ⟨b, rfl⟩ := rankEquiv.surjective l
    simp only [Equiv.symm_apply_apply, marginal_apply]
    cases a with
    | none => exact P.tokenMass_le_first b
    | some a =>
      cases a with
      | none =>
        cases b with
        | none => have hh : (1 : ℕ) ≤ 0 := hkl; omega
        | some b =>
          cases b with
          | none => exact le_rfl
          | some b => exact P.backgroundMass_le_second
      | some a =>
        cases b with
        | none => have hh : a.val + 2 ≤ 0 := hkl; omega
        | some b =>
          cases b with
          | none => have hh : a.val + 2 ≤ 1 := hkl; omega
          | some b => exact le_rfl

/-- The explicit path model satisfies the finite RF envelope with constant
one whenever its second-token parameter obeys the prescribed power bound. -/
theorem model_finiteRankFrequency (P : Parameters B) (n : ℕ) (exponent : ℝ)
    (hp : P.p ≤ (2 : ℝ) ^ (-exponent)) :
    FiniteRankFrequency (P.model n) (P.marginalRanking n) exponent 1 := by
  intro i k
  rw [model_marginal]
  change P.marginal (rankEquiv.symm k) ≤ _
  obtain ⟨a, rfl⟩ := rankEquiv.surjective k
  simp only [Equiv.symm_apply_apply, marginal_apply, one_mul]
  cases a with
  | none =>
      simp only [rankEquiv_first_val, zero_add, Nat.cast_one, Real.one_rpow, tokenMass]
      have hf : 0 ≤ 1 / (Fintype.card (Token B) : ℝ) := by positivity
      linarith [P.p_pos]
  | some a =>
      cases a with
      | none =>
          simp only [rankEquiv_second_val, tokenMass]
          norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
          have hf : 0 ≤ 1 / (Fintype.card (Token B) : ℝ) := by positivity
          linarith [P.p_pos]
      | some a =>
          have hh := P.backgroundMass_le_uniform
          simp only [Fintype.card_option, Fintype.card_fin] at *
          exact hh.trans (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _))

end
end Parameters

/-- The actual parameter choice in the comparison proposition supplies
the RF condition, with no vocabulary-growth or approximation premise. -/
theorem fromExponent_finiteRankFrequency (n B : ℕ) (exponent : ℝ)
    (he : 1 < exponent) (hB : 0 < B) :
    FiniteRankFrequency ((fromExponent B exponent he hB).model n)
      ((fromExponent B exponent he hB).marginalRanking n) exponent 1 :=
  Parameters.model_finiteRankFrequency _ _ _ le_rfl

end PathClass
end ForestSampling
