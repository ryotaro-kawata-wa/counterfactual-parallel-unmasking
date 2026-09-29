import ForestSampling.PathClass

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace PathClass
namespace Parameters

variable {B : ℕ}

noncomputable section

/-- The full-vocabulary row with type-A mass `theta` and the construction's
fixed within-type-B emissions. This retains every background token. -/
def typeMixture (P : Parameters B) (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    FinDist (Token B) where
  mass
    | none => θ
    | some none => (1 - θ) / 2
    | some (some _) => (1 - θ) / (2 * B)
  nonneg := by
    intro a
    cases a with
    | none => exact hθ
    | some a => cases a <;> dsimp <;> positivity
  sum_mass := by
    simp only [Fintype.sum_option, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hB : (B : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr P.background_pos)
    field_simp
    ring

/-- Fixed disjoint emissions preserve TV exactly, so the full-vocabulary
distance equals the difference of the two type-A probabilities. -/
theorem tv_typeMixture (P : Parameters B) (θ φ : ℝ)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (hφ : 0 ≤ φ) (hφone : φ ≤ 1) :
    FinDist.tv (P.typeMixture θ hθ hθone) (P.typeMixture φ hφ hφone) = |θ - φ| := by
  have hB : (0 : ℝ) < B := Nat.cast_pos.mpr P.background_pos
  have hsecond : (1 - θ) / 2 - (1 - φ) / 2 = -(θ - φ) / 2 := by ring
  have hbackground : (1 - θ) / (2 * B) - (1 - φ) / (2 * B) =
      -(θ - φ) / (2 * B) := by ring
  simp only [FinDist.tv, typeMixture, FinDist.mass_mk, Fintype.sum_option,
    hsecond, hbackground, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hB),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

def oddsRow (P : Parameters B) (r : ℝ) (hr : 0 ≤ r) : FinDist (Token B) :=
  P.typeMixture (r / (1 + r)) (div_nonneg hr (by positivity))
    ((div_le_one (by positivity : 0 < 1 + r)).mpr (by linarith))

theorem tv_oddsRow (P : Parameters B) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    FinDist.tv (P.oddsRow r hr) (P.oddsRow s hs) = |r / (1 + r) - s / (1 + s)| :=
  P.tv_typeMixture _ _ _ _ _ _

/-- Normalizing any positive weights that depend on the token only through
its type produces the stated odds row, including the fixed emissions. -/
theorem normalized_type_weights (P : Parameters B) (f : Bool → ℝ)
    (hf : ∀ s, 0 < f s) :
    FinDist.ofPositiveWeights (fun a ↦ P.marginal a * f (tokenType a))
        (fun a ↦ mul_pos (P.marginal_positive a) (hf (tokenType a))) =
      P.oddsRow ((1 - P.p) * f false / (P.p * f true))
        (div_nonneg (mul_nonneg (by linarith [P.p_lt_half]) (hf false).le)
          (mul_nonneg P.p_pos.le (hf true).le)) := by
  have hp : 0 < 1 - P.p := by linarith [P.p_lt_half]
  have hB : (0 : ℝ) < B := Nat.cast_pos.mpr P.background_pos
  have hden : 0 < (1 - P.p) * f false + P.p * f true :=
    add_pos (mul_pos hp (hf false)) (mul_pos P.p_pos (hf true))
  have hθ : ((1 - P.p) * f false / (P.p * f true)) /
      (1 + (1 - P.p) * f false / (P.p * f true)) =
        (1 - P.p) * f false / ((1 - P.p) * f false + P.p * f true) := by
    rw [one_add_div (mul_ne_zero P.p_pos.ne' (hf true).ne'),
      div_div_div_cancel_right₀ (mul_ne_zero P.p_pos.ne' (hf true).ne'), add_comm]
  have hsum : (∑ a, P.marginal a * f (tokenType a)) =
      (1 - P.p) * f false + P.p * f true := by
    rw [P.marginal_type_sum f]
    simp only [Fintype.sum_bool, typeMass]
    ring
  ext a
  rw [FinDist.ofPositiveWeights_apply, hsum]
  cases a with
  | none =>
      simp only [marginal_apply, tokenMass, tokenType, oddsRow, typeMixture, FinDist.mass_mk, hθ]
  | some a =>
      cases a <;>
        simp only [marginal_apply, tokenMass, tokenType, oddsRow, typeMixture, FinDist.mass_mk, hθ]
      all_goals
        field_simp [(P.p_pos).ne', (hf true).ne', hden.ne', hB.ne']
        ring

/-- Changing the source type multiplies the readout odds by `scaledOdds`.
The optional other path neighbor contributes the positive factor `q`. -/
def responseRow (P : Parameters B) (q : ℝ) (hq : 0 ≤ q) (source : Token B) :
    FinDist (Token B) :=
  if tokenType source then P.oddsRow q hq
  else P.oddsRow (P.scaledOdds * q)
    (mul_nonneg (lt_trans zero_lt_one P.scaledOdds_gt_one).le hq)

theorem tv_responseRow (P : Parameters B) (q : ℝ) (hq : 0 ≤ q)
    (a b : Token B) :
    FinDist.tv (P.responseRow q hq a) (P.responseRow q hq b) =
      if tokenType a = tokenType b then 0 else P.response q := by
  have hnonneg : 0 ≤ P.response q := by
    rw [P.response_formula q hq]
    have hA := P.scaledOdds_gt_one
    positivity
  unfold responseRow
  cases tokenType a <;> cases tokenType b <;> simp
  · rw [tv_oddsRow]
    exact abs_of_nonneg hnonneg
  · rw [FinDist.tv_comm, tv_oddsRow]
    exact abs_of_nonneg hnonneg

/-- The manuscript's RT estimate is proved on the complete full-token row
formula. The later boundary identification has to connect this formula to
the actual conditional row of the path model. -/
theorem responseRow_tail_bound (P : Parameters B) (q : ℝ) (hq : 0 ≤ q)
    (t : ℝ) (ht : 0 ≤ t) (a b : Token B)
    (ha : P.marginal a ≤ t) (hb : P.marginal b ≤ t) :
    FinDist.tv (P.responseRow q hq a) (P.responseRow q hq b) ≤ t := by
  rw [tv_responseRow]
  split_ifs with heq
  · exact ht
  · have htail : 1 - P.p ≤ t := by
      cases a with
      | none => exact ha
      | some a =>
        cases b with
        | none => exact hb
        | some b => simp [tokenType] at heq
    exact (P.response_le_one_sub_p q hq).trans htail

theorem responseRow_signal_bound (P : Parameters B) (q : ℝ) (hq : 0 ≤ q)
    (hchoices : q = 1 ∨ q = P.otherOddsA ∨ q = P.otherOddsB) :
    P.edgeSignal ≤ FinDist.tv (P.responseRow q hq none) (P.responseRow q hq (some none)) := by
  rw [tv_responseRow]
  simp only [tokenType, Bool.false_eq_true, ite_false]
  exact P.edgeSignal_le_response q hchoices

end
end Parameters
end PathClass
end ForestSampling
