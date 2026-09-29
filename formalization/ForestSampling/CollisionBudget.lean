import ForestSampling.FiniteProbability

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace CollisionBudget

/-!
# Quantitative final steps of disclosure and collision concentration

These are checked analytic consequences of explicit probability estimates.
They do not establish the survivor invariant or the matching-process Laplace
estimate supplying the hypotheses. Keeping those inputs visible prevents a
conditional calculation from being confused with the main adaptive theorem.
-/

/-- The adaptive failed-test hazard recurrence recovers the unconditional
`k / K` disclosure bound. The conditional hazard is allowed to increase after
failed candidates are removed. -/
theorem disclosure_recurrence_bound (K : ℕ) (hK : 0 < K) (p : ℕ → ℝ)
    (hzero : p 0 ≤ 0)
    (hstep : ∀ k < K, p (k + 1) ≤ p k + (1 - p k) / ((K - k : ℕ) : ℝ)) :
    ∀ k ≤ K, p k ≤ (k : ℝ) / (K : ℝ) := by
  intro k
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    intro hk
    have hkle : k ≤ K := by omega
    have hklt : k < K := by omega
    have hprev := ih hkle
    have hden : (0 : ℝ) < ((K - k : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hklt
    have hden1 : (1 : ℝ) ≤ ((K - k : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ K - k by omega)
    have hKreal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    have hmono : p k + (1 - p k) / ((K - k : ℕ) : ℝ) ≤
        (k : ℝ) / (K : ℝ) + (1 - (k : ℝ) / (K : ℝ)) / ((K - k : ℕ) : ℝ) := by
      apply (le_of_sub_nonneg ?_)
      have hm := mul_nonneg (sub_nonneg.mpr hprev) (sub_nonneg.mpr hden1)
      apply (nonneg_of_mul_nonneg_right ?_ hden)
      have heq :
          ((k : ℝ) / (K : ℝ) + (1 - (k : ℝ) / (K : ℝ)) / ((K - k : ℕ) : ℝ) -
            (p k + (1 - p k) / ((K - k : ℕ) : ℝ))) * ((K - k : ℕ) : ℝ) =
          ((k : ℝ) / (K : ℝ) - p k) * (((K - k : ℕ) : ℝ) - 1) := by
        field_simp
        ring
      rw [mul_comm, heq]
      exact hm
    calc
      p (k + 1) ≤ p k + (1 - p k) / ((K - k : ℕ) : ℝ) := hstep k hklt
      _ ≤ (k : ℝ) / (K : ℝ) +
          (1 - (k : ℝ) / (K : ℝ)) / ((K - k : ℕ) : ℝ) := hmono
      _ = ((k + 1 : ℕ) : ℝ) / (K : ℝ) := by
        rw [Nat.cast_sub hkle, Nat.cast_add, Nat.cast_one]
        have hdiff : (K : ℝ) - (k : ℝ) ≠ 0 := by
          exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hklt))
        field_simp

/-- A small expected disclosure and an exponential compensation estimate
force a collision tail. The activity condition is required only when
query disclosure is at most its designated threshold. -/
theorem tail_of_compensated_laplace {Ω : Type*} [Fintype Ω]
    (p : FinDist Ω) (D Z A : Ω → ℝ) (d x : ℝ)
    (hd : 0 < d) (hD : ∀ w, 0 ≤ D w)
    (hmean : (∑ w, p w * D w) ≤ d / 2)
    (hactivity : ∀ w, D w ≤ d → 128 * x ≤ A w)
    (hlaplace : (∑ w, p w * Real.exp (-Z w + A w / 64)) ≤ 1) :
    (1 / 2 : ℝ) - Real.exp (-x) ≤ p.eventMass (fun w ↦ x ≤ Z w) := by
  classical
  have hpoint : ∀ w, 1 ≤ D w / d + (if x ≤ Z w then 1 else 0) +
      Real.exp (-x) * Real.exp (-Z w + A w / 64) := by
    intro w
    have hDdiv : 0 ≤ D w / d := div_nonneg (hD w) hd.le
    have hexp : 0 ≤ Real.exp (-x) * Real.exp (-Z w + A w / 64) := by positivity
    by_cases hgood : D w ≤ d
    · by_cases hZ : x ≤ Z w
      · rw [if_pos hZ]
        linarith
      · rw [if_neg hZ]
        have hA := hactivity w hgood
        have he : 1 ≤ Real.exp (-x) * Real.exp (-Z w + A w / 64) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp_iff.mpr
          linarith
        linarith
    · have hlarge : 1 ≤ D w / d := (le_div_iff₀ hd).mpr (by linarith)
      split <;> linarith
  have havg := Finset.sum_le_sum (s := (Finset.univ : Finset Ω))
    (fun w _ ↦ mul_le_mul_of_nonneg_left (hpoint w) (p.nonneg w))
  simp only [mul_one, mul_add] at havg
  rw [p.sum_mass, Finset.sum_add_distrib, Finset.sum_add_distrib] at havg
  have hDsum : (∑ w, p w * (D w / d)) = (∑ w, p w * D w) / d := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w _
    ring
  have hIsum : (∑ w, p w * (if x ≤ Z w then 1 else 0)) =
      p.eventMass (fun w ↦ x ≤ Z w) := by
    simp [FinDist.eventMass, mul_ite]
  have hEsum : (∑ w, p w * (Real.exp (-x) * Real.exp (-Z w + A w / 64))) =
      Real.exp (-x) * ∑ w, p w * Real.exp (-Z w + A w / 64) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [hDsum, hIsum, hEsum] at havg
  have hDhalf : (∑ w, p w * D w) / d ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hEbound := mul_le_mul_of_nonneg_left hlaplace (Real.exp_nonneg (-x))
  linarith

/-- The numerical slack used by the manuscript's constant-probability tail. -/
theorem exp_neg_le_quarter {x : ℝ} (hx : 2 ≤ x) : Real.exp (-x) ≤ (1 / 4 : ℝ) := by
  have hone : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have htwo : 4 ≤ Real.exp 2 := by
    have heq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [heq]
    nlinarith [sq_nonneg (Real.exp 1 - 2)]
  have hex : 4 ≤ Real.exp x := htwo.trans (Real.exp_le_exp.mpr hx)
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hm := mul_le_mul_of_nonneg_right hex (Real.exp_nonneg (-x))
  rw [hcancel] at hm
  linarith

/-- The finite constant `1/4` in `app:prop:collision-lower-tail`, conditional
on the explicit disclosure, ledger/activity, and Laplace estimates. -/
theorem collision_tail_of_laplace_and_activity {Ω : Type*} [Fintype Ω]
    (p : FinDist Ω) (D Z A : Ω → ℝ) (N R : ℕ)
    (hR0 : 1 ≤ R) (hRN : R ≤ N / 16384)
    (hD : ∀ w, 0 ≤ D w)
    (hmean : (∑ w, p w * D w) ≤ (N : ℝ) / 8)
    (hactivity : ∀ w, D w ≤ (N : ℝ) / 4 →
      (N : ℝ) / (64 * (R : ℝ)) ≤ A w)
    (hlaplace : (∑ w, p w * Real.exp (-Z w + A w / 64)) ≤ 1) :
    (1 / 4 : ℝ) ≤ p.eventMass (fun w ↦ (N : ℝ) / (8192 * (R : ℝ)) ≤ Z w) := by
  classical
  have hR : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hNR : 16384 * R ≤ N := by omega
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hx : (2 : ℝ) ≤ (N : ℝ) / (8192 * (R : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hNRreal : (16384 : ℝ) * (R : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNR
    linarith
  have htail := tail_of_compensated_laplace p D Z A ((N : ℝ) / 4)
    ((N : ℝ) / (8192 * (R : ℝ))) (by positivity) hD
    (by linarith) (fun w hw ↦ by
      have hh := hactivity w hw
      have heq : 128 * ((N : ℝ) / (8192 * (R : ℝ))) =
          (N : ℝ) / (64 * (R : ℝ)) := by ring
      rwa [heq]) hlaplace
  have hexp := exp_neg_le_quarter hx
  linarith

end CollisionBudget
end ForestSampling
