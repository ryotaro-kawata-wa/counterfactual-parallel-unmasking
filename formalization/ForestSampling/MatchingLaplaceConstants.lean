import Mathlib

set_option autoImplicit false

namespace ForestSampling
namespace MatchingLaplaceConstants

/-- The Bernoulli deficit appearing in the matching Laplace transform lies
in `[0,1]` for every nonnegative Laplace parameter. -/
theorem deficit_bounds {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ 1 - Real.exp (-s) ∧ 1 - Real.exp (-s) ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs))
  · linarith [Real.exp_nonneg (-s)]

/-- Abstract scalar endgame for `m` exposures with partner-success floor
`r/n`. The integer lower bounds retain the paper's finite constant 32. -/
theorem exposure_power_le_exp (k n m r : ℕ)
    (hk : 1 ≤ k) (hn : 0 < n) (hrn : r ≤ n)
    (hkm : k ≤ 8 * m) (hkr : k ≤ 4 * r)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (1 - a * (r : ℝ) / (n : ℝ)) ^ m ≤
      Real.exp (-(a * ((k - 1 : ℕ) : ℝ) ^ 2 / (32 * (n : ℝ)))) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrreal : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
  have har : a * (r : ℝ) ≤ (n : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right ha1 (Nat.cast_nonneg r)
    linarith
  have hbase : 0 ≤ 1 - a * (r : ℝ) / (n : ℝ) := by
    have hfrac := (div_le_one hnreal).mpr har
    linarith
  have htan : 1 - a * (r : ℝ) / (n : ℝ) ≤
      Real.exp (-(a * (r : ℝ) / (n : ℝ))) := by
    linarith [Real.add_one_le_exp (-(a * (r : ℝ) / (n : ℝ)))]
  have hk8 : (k : ℝ) ≤ 8 * (m : ℝ) := by exact_mod_cast hkm
  have hk4 : (k : ℝ) ≤ 4 * (r : ℝ) := by exact_mod_cast hkr
  have hmul := mul_le_mul hk8 hk4 (Nat.cast_nonneg k) (by positivity : (0 : ℝ) ≤ 8 * m)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hprod : ((k - 1 : ℕ) : ℝ) ^ 2 ≤ 32 * (m : ℝ) * (r : ℝ) := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    nlinarith
  calc
    (1 - a * (r : ℝ) / (n : ℝ)) ^ m ≤
        (Real.exp (-(a * (r : ℝ) / (n : ℝ)))) ^ m :=
      pow_le_pow_left₀ hbase htan m
    _ = Real.exp ((m : ℝ) * (-(a * (r : ℝ) / (n : ℝ)))) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-(a * ((k - 1 : ℕ) : ℝ) ^ 2 / (32 * (n : ℝ)))) := by
      apply Real.exp_le_exp.mpr
      apply le_of_sub_nonneg
      have heq : -(a * ((k - 1 : ℕ) : ℝ) ^ 2 / (32 * (n : ℝ))) -
          (m : ℝ) * (-(a * (r : ℝ) / (n : ℝ))) =
          a * (32 * (m : ℝ) * (r : ℝ) - ((k - 1 : ℕ) : ℝ) ^ 2) /
            (32 * (n : ℝ)) := by ring
      rw [heq]
      exact div_nonneg (mul_nonneg ha0 (sub_nonneg.mpr hprod)) (by positivity)

/-- The paper's near-half partition and quarter exposure count supply the
integer conditions of the abstract scalar estimate, including k=4,...,7. -/
theorem quarter_exposure_bounds (k n : ℕ) (hk : 4 ≤ k) (hkn : k ≤ n) :
    k ≤ 8 * (k / 4) ∧
      k ≤ 4 * ((k + 1) / 2 - k / 4) ∧
      (k + 1) / 2 - k / 4 ≤ n := by omega

/-- Direct form of the large-batch Laplace endgame in the current manuscript. -/
theorem quarter_exposure_power_le_exp (k n : ℕ) (hk : 4 ≤ k) (hkn : k ≤ n)
    (s : ℝ) (hs : 0 ≤ s) :
    (1 - (1 - Real.exp (-s)) * (((k + 1) / 2 - k / 4 : ℕ) : ℝ) / (n : ℝ)) ^ (k / 4) ≤
      Real.exp (-((1 - Real.exp (-s)) * ((k - 1 : ℕ) : ℝ) ^ 2 / (32 * (n : ℝ)))) := by
  obtain ⟨hm, hr, hrn⟩ := quarter_exposure_bounds k n hk hkn
  obtain ⟨ha0, ha1⟩ := deficit_bounds hs
  exact exposure_power_le_exp k n (k / 4) ((k + 1) / 2 - k / 4)
    (by omega) (by omega) hrn hm hr (1 - Real.exp (-s)) ha0 ha1

/-- For batches of size two or three, exposing one selected endpoint is
already sufficient for the weaker constant-32 exponential estimate. -/
theorem small_batch_factor_le_exp (k n : ℕ) (hk0 : 2 ≤ k) (hk1 : k ≤ 3)
    (hkn : k ≤ n) (a : ℝ) (ha : 0 ≤ a) :
    1 - a * ((k - 1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ) ≤
      Real.exp (-(a * ((k - 1 : ℕ) : ℝ) ^ 2 / (32 * (n : ℝ)))) := by
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnm : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hkcast : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k - 1 by omega)
  have hkcast' : ((k - 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show k - 1 ≤ 2 by omega)
  have hnsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hratio : ((k - 1 : ℕ) : ℝ) ^ 2 / (32 * (n : ℝ)) ≤
      ((k - 1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hnm).mpr
    rw [hnsub]
    have hsquare : ((k - 1 : ℕ) : ℝ) ^ 2 ≤ 2 * ((k - 1 : ℕ) : ℝ) := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hsquare (by positivity : (0 : ℝ) ≤ n)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hratio ha
  have ht := Real.add_one_le_exp (-(a * ((k - 1 : ℕ) : ℝ) ^ 2 / (32 * (n : ℝ))))
  have heq : a * (((k - 1 : ℕ) : ℝ) ^ 2 / (32 * (n : ℝ))) =
      a * ((k - 1 : ℕ) : ℝ) ^ 2 / (32 * (n : ℝ)) := by ring
  rw [heq] at hm
  have heq' : a * (((k - 1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)) =
      a * ((k - 1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ) := by ring
  rw [heq'] at hm
  linarith

end MatchingLaplaceConstants
end ForestSampling
