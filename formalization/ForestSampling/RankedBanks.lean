import ForestSampling.ScreeningPreprocess
import ForestSampling.PaperStatements

set_option autoImplicit false

namespace ForestSampling
namespace Screening

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The scalar inversion used to convert a positive rank-frequency
mass lower bound into an upper bound on the token's one-based rank. -/
theorem rank_le_of_power_mass (x exponent C t : ℝ) (hx : 0 < x)
    (he : 0 < exponent) (ht : 0 < t)
    (hmass : t / 4 ≤ C * x ^ (-exponent)) :
    x ≤ (4 * C / t) ^ (1 / exponent) := by
  have hxp : 0 < x ^ exponent := Real.rpow_pos_of_pos hx _
  have hdiv : t / 4 ≤ C / x ^ exponent := by
    simpa only [Real.rpow_neg hx.le, div_eq_mul_inv] using hmass
  have hmul := (le_div_iff₀ hxp).mp hdiv
  have hp : x ^ exponent ≤ 4 * C / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hh := Real.rpow_le_rpow hxp.le hp (show 0 ≤ 1 / exponent by positivity)
  rw [← Real.rpow_mul hx.le] at hh
  have heq : exponent * (1 / exponent) = 1 := by field_simp
  simpa only [heq, Real.rpow_one] using hh

/-- The buffered observable bank obeys the manuscript's finite RF size
bound. Its tokens are mapped injectively to their actual marginal ranks;
no sorting or cardinality premise is assumed about the noisy bank. -/
theorem tokenBank_card_le_floor (M : ForestModel N V) (O : FrozenOracle N V)
    (ranking : MarginalRanking M) (exponent C t ε : ℝ)
    (he : 0 < exponent) (hC : 1 ≤ C)
    (hRF : FiniteRankFrequency M ranking exponent C)
    (hfloor : 4 * max ε (C / (Fintype.card V : ℝ)) ≤ t)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (i : Position N) :
    (tokenBank O t ε i).card ≤ ⌊(4 * C / t) ^ (1 / exponent)⌋₊ := by
  classical
  have hv : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hC0 : 0 < C := by linarith
  have ht : 0 < t := lt_of_lt_of_le (by positivity : 0 < 4 * (C / (Fintype.card V : ℝ)))
    ((mul_le_mul_of_nonneg_left (le_max_right ε _) (by norm_num)).trans hfloor)
  have heps : 4 * ε ≤ t :=
    (mul_le_mul_of_nonneg_left (le_max_left ε _) (by norm_num)).trans hfloor
  have hfreq : C / (Fintype.card V : ℝ) ≤ t / 4 := by
    have hh := (mul_le_mul_of_nonneg_left (le_max_right ε _) (show (0 : ℝ) ≤ 4 by norm_num)).trans hfloor
    linarith
  let e : Fin (Fintype.card V) ≃ V := Equiv.ofBijective (ranking.token i) (ranking.token_bijective i)
  have hrank : ∀ a ∈ tokenBank O t ε i,
      (((e.symm a).val + 1 : ℕ) : ℝ) ≤ (4 * C / t) ^ (1 / exponent) := by
    intro a ha
    have hmass := bank_member_mass_le M O t ε heps hrows i a ha
    have hbound := hRF i (e.symm a)
    have heq : ranking.token i (e.symm a) = a := e.apply_symm_apply a
    rw [heq] at hbound
    apply rank_le_of_power_mass _ exponent C t (by positivity) he ht
    have hfloor' : C * (1 / (Fintype.card V : ℝ)) ≤ t / 4 := by
      simpa only [mul_one_div] using hfreq
    nlinarith
  let ranks := (tokenBank O t ε i).image (fun a ↦ (e.symm a).val)
  have hcard : ranks.card = (tokenBank O t ε i).card :=
    Finset.card_image_of_injective _ (Fin.val_injective.comp e.symm.injective)
  rw [← hcard]
  calc
    ranks.card ≤ (Finset.range ⌊(4 * C / t) ^ (1 / exponent)⌋₊).card := by
      apply Finset.card_le_card
      intro k hk
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      have hf : (e.symm a).val + 1 ≤ ⌊(4 * C / t) ^ (1 / exponent)⌋₊ :=
        Nat.le_floor (hrank a ha)
      exact Finset.mem_range.mpr (by omega)
    _ = _ := Finset.card_range _

/-- The actual shared packed-column bank maximum has the same finite
rank-frequency bound, including the empty-position and empty-bank cases. -/
theorem bankMax_le_rank_bound [LinearOrder V] (M : ForestModel N V)
    (O : FrozenOracle N V) (ranking : MarginalRanking M) (exponent C t ε : ℝ)
    (he : 0 < exponent) (hC : 1 ≤ C)
    (hRF : FiniteRankFrequency M ranking exponent C)
    (hfloor : 4 * max ε (C / (Fintype.card V : ℝ)) ≤ t)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε) :
    (Banks.ofOracle O t ε (standardFloor_complement_bound ε C t hC hfloor)).maxSize ≤
      ⌊(4 * C / t) ^ (1 / exponent)⌋₊ := by
  apply Finset.sup_le
  intro i _
  exact tokenBank_card_le_floor M O ranking exponent C t ε he hC hRF hfloor hrows i

end Screening
end ForestSampling
