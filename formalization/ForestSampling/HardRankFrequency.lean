import ForestSampling.HardMatching

set_option autoImplicit false

namespace ForestSampling
namespace HardLocalParameters

variable {K B : ℕ}

/-- The public labels enumerate bank tokens first, followed by background
labels, without changing the finite vocabulary. -/
def rankEquiv : HardVocabulary K B ≃ Fin (Fintype.card (HardVocabulary K B)) :=
  finSumFinEquiv.trans (finCongr (by simp [HardVocabulary]))

@[simp] theorem rankEquiv_bank_val (a : Fin K) :
    (rankEquiv (Sum.inl a : HardVocabulary K B)).val = a.val := rfl

@[simp] theorem rankEquiv_background_val (a : Fin B) :
    (rankEquiv (Sum.inr a : HardVocabulary K B)).val = K + a.val := rfl

/-- The vocabulary-spread condition places background mass below each bank
mass. This establishes the actual ordering, rather than assuming a ranking. -/
theorem backgroundMass_le_trigger (P : HardLocalParameters K B)
    (hspread : 1 < ((K + B : ℕ) : ℝ) * P.triggerMass) :
    (1 - (K : ℝ) * P.triggerMass) / B ≤ P.triggerMass := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr P.background_nonempty)).mpr
  push_cast at hspread
  nlinarith

/-- The vocabulary-floor term controls the entire background in the finite
rank-frequency envelope. No vocabulary-growth assumption is used. -/
theorem backgroundMass_le_uniform (P : HardLocalParameters K B)
    (hspread : 1 < ((K + B : ℕ) : ℝ) * P.triggerMass) :
    (1 - (K : ℝ) * P.triggerMass) / B ≤ 1 / ((K + B : ℕ) : ℝ) := by
  have hB : (0 : ℝ) < B := Nat.cast_pos.mpr P.background_nonempty
  have hV : (0 : ℝ) < ((K + B : ℕ) : ℝ) := by push_cast; positivity
  apply (div_le_div_iff₀ hB hV).mpr
  have hmul := mul_nonneg (Nat.cast_nonneg (α := ℝ) K) (le_of_lt (sub_pos.mpr hspread))
  push_cast at *
  nlinarith

end HardLocalParameters
namespace HardMatching

variable {N K B : ℕ}

noncomputable section

/-- The explicit bank-first marginal ranking is justified by the actual
matching target's common marginal and the vocabulary-spread condition. -/
def marginalRanking (P : HardLocalParameters K B) (M : PerfectMatching N)
    (trigger : Position N → Fin K)
    (hspread : 1 < ((K + B : ℕ) : ℝ) * P.triggerMass) :
    MarginalRanking (model P M trigger) where
  token _ := HardLocalParameters.rankEquiv.symm
  token_bijective _ := HardLocalParameters.rankEquiv.symm.bijective
  nonincreasing := by
    intro i k l hkl
    rw [model_marginal]
    obtain ⟨a, rfl⟩ := HardLocalParameters.rankEquiv.surjective k
    obtain ⟨b, rfl⟩ := HardLocalParameters.rankEquiv.surjective l
    simp only [Equiv.symm_apply_apply, HardLocalParameters.commonMarginal_apply]
    cases a with
    | inl a =>
      cases b with
      | inl b => exact le_rfl
      | inr b => exact P.backgroundMass_le_trigger hspread
    | inr a =>
      cases b with
      | inl b =>
        have hh : K + a.val ≤ b.val := hkl
        omega
      | inr b => exact le_rfl

/-- The concrete matching family satisfies the finite rank-frequency
inequality with constant one. The only additional inputs are exactly the
finite spread and bank-mass assumptions from the manuscript. -/
theorem model_finiteRankFrequency (P : HardLocalParameters K B)
    (M : PerfectMatching N) (trigger : Position N → Fin K)
    (exponent : ℝ) (hexponent : 0 ≤ exponent)
    (hspread : 1 < ((K + B : ℕ) : ℝ) * P.triggerMass)
    (hbank : P.triggerMass ≤ (K : ℝ) ^ (-exponent)) :
    FiniteRankFrequency (model P M trigger)
      (marginalRanking P M trigger hspread) exponent 1 := by
  intro i k
  rw [model_marginal]
  change P.commonMarginal (HardLocalParameters.rankEquiv.symm k) ≤ _
  obtain ⟨a, rfl⟩ := HardLocalParameters.rankEquiv.surjective k
  simp only [Equiv.symm_apply_apply, HardLocalParameters.commonMarginal_apply, one_mul]
  cases a with
  | inl a =>
    have hpow : (K : ℝ) ^ (-exponent) ≤ ((a.val + 1 : ℕ) : ℝ) ^ (-exponent) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity)
      · exact_mod_cast (show a.val + 1 ≤ K by omega)
      · linarith
    change P.triggerMass ≤ ((a.val + 1 : ℕ) : ℝ) ^ (-exponent) + _
    exact (hbank.trans hpow).trans (le_add_of_nonneg_right (by positivity))
  | inr a =>
    have hh := P.backgroundMass_le_uniform hspread
    simp only [Fintype.card_sum, Fintype.card_fin] at *
    change (1 - (K : ℝ) * P.triggerMass) / B ≤ _
    exact hh.trans (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _))

end
end HardMatching
end ForestSampling
