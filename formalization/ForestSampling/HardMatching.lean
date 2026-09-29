import ForestSampling.PaperStatements

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

/-!
# Local laws for the hard matching family

The vocabulary is split into a public candidate bank and a nonempty
background.  This module checks the normalization and strict positivity of
the formulas in `app:def:hard-matching-family` before assembling matching
components into the full sequence law.
-/

/-- Public candidate labels followed by public background labels. -/
abbrev HardVocabulary (bankSize backgroundSize : ℕ) :=
  Fin bankSize ⊕ Fin backgroundSize

/-- Finite scalar hypotheses needed for the local hard-family laws. -/
structure HardLocalParameters (bankSize backgroundSize : ℕ) where
  triggerMass : ℝ
  edgeCoupling : ℝ
  background_nonempty : 0 < backgroundSize
  trigger_pos : 0 < triggerMass
  bank_mass_lt_one : (bankSize : ℝ) * triggerMass < 1
  coupling_pos : 0 < edgeCoupling
  coupling_le_trigger : edgeCoupling ≤ triggerMass
  trigger_le_half : triggerMass ≤ (1 / 2 : ℝ)

namespace HardLocalParameters

variable {bankSize backgroundSize : ℕ}

noncomputable section

/-- Pointwise common marginal from `app:eq:hard-common-marginal`. -/
def commonMass (P : HardLocalParameters bankSize backgroundSize) :
    HardVocabulary bankSize backgroundSize → ℝ
  | Sum.inl _ => P.triggerMass
  | Sum.inr _ =>
      (1 - (bankSize : ℝ) * P.triggerMass) / (backgroundSize : ℝ)

theorem commonMass_pos (P : HardLocalParameters bankSize backgroundSize)
    (a : HardVocabulary bankSize backgroundSize) :
    0 < P.commonMass a := by
  cases a with
  | inl c => exact P.trigger_pos
  | inr b =>
      exact div_pos (sub_pos.mpr P.bank_mass_lt_one)
        (Nat.cast_pos.mpr P.background_nonempty)

theorem sum_commonMass (P : HardLocalParameters bankSize backgroundSize) :
    ∑ a, P.commonMass a = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [commonMass, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hbackground : (backgroundSize : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt P.background_nonempty)
  field_simp
  ring

/-- The common strictly positive marginal used at every position. -/
def commonMarginal (P : HardLocalParameters bankSize backgroundSize) :
    FinDist (HardVocabulary bankSize backgroundSize) where
  mass := P.commonMass
  nonneg a := (P.commonMass_pos a).le
  sum_mass := P.sum_commonMass

@[simp]
theorem commonMarginal_apply (P : HardLocalParameters bankSize backgroundSize)
    (a : HardVocabulary bankSize backgroundSize) :
    P.commonMarginal a = P.commonMass a := rfl

theorem commonMarginal_strictlyPositive
    (P : HardLocalParameters bankSize backgroundSize) :
    P.commonMarginal.StrictlyPositive :=
  P.commonMass_pos

/-- Centered trigger feature from `app:eq:hard-features`. -/
def feature (P : HardLocalParameters bankSize backgroundSize)
    (trigger : Fin bankSize) (a : HardVocabulary bankSize backgroundSize) : ℝ :=
  (if a = Sum.inl trigger then 1 else 0) - P.triggerMass

/-- Trigger-feature variance. -/
def triggerVariance (P : HardLocalParameters bankSize backgroundSize) : ℝ :=
  P.triggerMass * (1 - P.triggerMass)

theorem triggerMass_lt_one (P : HardLocalParameters bankSize backgroundSize) :
    P.triggerMass < 1 := by
  linarith [P.trigger_le_half]

theorem triggerVariance_pos (P : HardLocalParameters bankSize backgroundSize) :
    0 < P.triggerVariance := by
  exact mul_pos P.trigger_pos (sub_pos.mpr P.triggerMass_lt_one)

@[simp]
theorem commonMass_trigger (P : HardLocalParameters bankSize backgroundSize)
    (trigger : Fin bankSize) :
    P.commonMass (Sum.inl trigger) = P.triggerMass := rfl

@[simp]
theorem feature_at_trigger (P : HardLocalParameters bankSize backgroundSize)
    (trigger : Fin bankSize) :
    P.feature trigger (Sum.inl trigger) = 1 - P.triggerMass := by
  simp [feature]

theorem feature_off_trigger (P : HardLocalParameters bankSize backgroundSize)
    (trigger : Fin bankSize) {a : HardVocabulary bankSize backgroundSize}
    (ha : a ≠ Sum.inl trigger) :
    P.feature trigger a = -P.triggerMass := by
  simp [feature, ha]

/-- The trigger feature is centered under the common marginal. -/
theorem weighted_feature_sum (P : HardLocalParameters bankSize backgroundSize)
    (trigger : Fin bankSize) :
    ∑ a, P.commonMarginal a * P.feature trigger a = 0 := by
  calc
    (∑ a, P.commonMarginal a * P.feature trigger a)
        = (∑ a, P.commonMarginal a *
            (if a = Sum.inl trigger then 1 else 0)) -
          P.triggerMass * ∑ a, P.commonMarginal a := by
            unfold feature
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
            ring
    _ = P.commonMarginal (Sum.inl trigger) - P.triggerMass := by
          simp_rw [mul_ite, mul_one, mul_zero]
          rw [Fintype.sum_ite_eq', P.commonMarginal.sum_mass, mul_one]
    _ = 0 := by simp

/-- The trigger feature has Bernoulli variance under the common marginal. -/
theorem weighted_feature_sq_sum
    (P : HardLocalParameters bankSize backgroundSize)
    (trigger : Fin bankSize) :
    ∑ a, P.commonMarginal a * (P.feature trigger a) ^ 2 =
      P.triggerVariance := by
  calc
    (∑ a, P.commonMarginal a * (P.feature trigger a) ^ 2) =
        ∑ a, (
          (P.commonMarginal a * P.feature trigger a) *
              (if a = Sum.inl trigger then 1 else 0) -
            P.triggerMass *
              (P.commonMarginal a * P.feature trigger a)) := by
                apply Finset.sum_congr rfl
                intro a _
                unfold feature
                ring
    _ = (∑ a,
          (P.commonMarginal a * P.feature trigger a) *
            (if a = Sum.inl trigger then 1 else 0)) -
          P.triggerMass *
            ∑ a, P.commonMarginal a * P.feature trigger a := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = P.commonMarginal (Sum.inl trigger) *
          P.feature trigger (Sum.inl trigger) := by
            rw [P.weighted_feature_sum, mul_zero, sub_zero]
            simp_rw [mul_ite, mul_one, mul_zero]
            rw [Fintype.sum_ite_eq']
    _ = P.triggerVariance := by
          rw [P.commonMarginal_apply, P.commonMass_trigger,
            P.feature_at_trigger]
          rfl

/-- First absolute centered moment of the Bernoulli trigger feature. -/
theorem weighted_abs_feature_sum
    (P : HardLocalParameters bankSize backgroundSize)
    (trigger : Fin bankSize) :
    ∑ a, P.commonMarginal a * |P.feature trigger a| =
      2 * P.triggerVariance := by
  have hone : 0 ≤ 1 - P.triggerMass :=
    sub_nonneg.mpr P.triggerMass_lt_one.le
  calc
    (∑ a, P.commonMarginal a * |P.feature trigger a|) =
        ∑ a, P.commonMarginal a *
          ((1 - 2 * P.triggerMass) *
              (if a = Sum.inl trigger then 1 else 0) +
            P.triggerMass) := by
              apply Finset.sum_congr rfl
              intro a _
              by_cases ha : a = Sum.inl trigger
              · rw [ha, P.feature_at_trigger, abs_of_nonneg hone]
                rw [if_pos rfl]
                ring
              · rw [P.feature_off_trigger trigger ha,
                  abs_neg, abs_of_pos P.trigger_pos, if_neg ha]
                ring
    _ = (1 - 2 * P.triggerMass) *
          P.commonMarginal (Sum.inl trigger) +
        P.triggerMass * ∑ a, P.commonMarginal a := by
          calc
            _ = ∑ a, (
                (1 - 2 * P.triggerMass) *
                    (P.commonMarginal a *
                      (if a = Sum.inl trigger then 1 else 0)) +
                  P.triggerMass * P.commonMarginal a) := by
                    apply Finset.sum_congr rfl
                    intro a _
                    ring
            _ = (1 - 2 * P.triggerMass) *
                  ∑ a, P.commonMarginal a *
                    (if a = Sum.inl trigger then 1 else 0) +
                P.triggerMass * ∑ a, P.commonMarginal a := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
                    ← Finset.mul_sum]
            _ = _ := by
                  simp_rw [mul_ite, mul_one, mul_zero]
                  rw [Fintype.sum_ite_eq']
    _ = 2 * P.triggerVariance := by
          rw [P.commonMarginal_apply, P.commonMass_trigger,
            P.commonMarginal.sum_mass]
          unfold triggerVariance
          ring

/-- Multiplicative interaction factor in the hard endpoint kernel. -/
def interactionFactor (P : HardLocalParameters bankSize backgroundSize)
    (sourceTrigger targetTrigger : Fin bankSize)
    (a b : HardVocabulary bankSize backgroundSize) : ℝ :=
  1 + P.edgeCoupling *
    (P.feature sourceTrigger a * P.feature targetTrigger b) /
      P.triggerVariance

theorem one_sub_edgeCoupling_pos
    (P : HardLocalParameters bankSize backgroundSize) :
    0 < 1 - P.edgeCoupling := by
  linarith [P.coupling_le_trigger, P.trigger_le_half]

theorem interactionFactor_pos (P : HardLocalParameters bankSize backgroundSize)
    (sourceTrigger targetTrigger : Fin bankSize)
    (a b : HardVocabulary bankSize backgroundSize) :
    0 < P.interactionFactor sourceTrigger targetTrigger a b := by
  by_cases ha : a = Sum.inl sourceTrigger
  · by_cases hb : b = Sum.inl targetTrigger
    · have hfeatures :
          0 ≤ P.feature sourceTrigger a * P.feature targetTrigger b := by
        rw [ha, hb, P.feature_at_trigger, P.feature_at_trigger]
        exact mul_nonneg (sub_nonneg.mpr P.triggerMass_lt_one.le)
          (sub_nonneg.mpr P.triggerMass_lt_one.le)
      have hquot :
          0 ≤ P.edgeCoupling *
            (P.feature sourceTrigger a * P.feature targetTrigger b) /
              P.triggerVariance :=
        div_nonneg (mul_nonneg P.coupling_pos.le hfeatures)
          P.triggerVariance_pos.le
      unfold interactionFactor
      linarith
    · unfold interactionFactor
      rw [ha, P.feature_at_trigger, P.feature_off_trigger targetTrigger hb]
      unfold triggerVariance
      have hθ : P.triggerMass ≠ 0 := ne_of_gt P.trigger_pos
      have h1θ : 1 - P.triggerMass ≠ 0 :=
        ne_of_gt (sub_pos.mpr P.triggerMass_lt_one)
      have heq :
          1 + P.edgeCoupling *
              ((1 - P.triggerMass) * -P.triggerMass) /
                (P.triggerMass * (1 - P.triggerMass)) =
            1 - P.edgeCoupling := by
        field_simp
        ring
      rw [heq]
      exact P.one_sub_edgeCoupling_pos
  · by_cases hb : b = Sum.inl targetTrigger
    · unfold interactionFactor
      rw [P.feature_off_trigger sourceTrigger ha, hb, P.feature_at_trigger]
      unfold triggerVariance
      have hθ : P.triggerMass ≠ 0 := ne_of_gt P.trigger_pos
      have h1θ : 1 - P.triggerMass ≠ 0 :=
        ne_of_gt (sub_pos.mpr P.triggerMass_lt_one)
      have heq :
          1 + P.edgeCoupling *
              (-P.triggerMass * (1 - P.triggerMass)) /
                (P.triggerMass * (1 - P.triggerMass)) =
            1 - P.edgeCoupling := by
        field_simp
        ring
      rw [heq]
      exact P.one_sub_edgeCoupling_pos
    · have hfeatures :
          0 ≤ P.feature sourceTrigger a * P.feature targetTrigger b := by
        rw [P.feature_off_trigger sourceTrigger ha,
          P.feature_off_trigger targetTrigger hb]
        nlinarith [sq_nonneg P.triggerMass]
      have hquot :
          0 ≤ P.edgeCoupling *
            (P.feature sourceTrigger a * P.feature targetTrigger b) /
              P.triggerVariance :=
        div_nonneg (mul_nonneg P.coupling_pos.le hfeatures)
          P.triggerVariance_pos.le
      unfold interactionFactor
      linarith

/-- Endpoint conditional kernel in `app:eq:hard-target-and-kernel`. -/
def endpointKernel (P : HardLocalParameters bankSize backgroundSize)
    (sourceTrigger targetTrigger : Fin bankSize)
    (a : HardVocabulary bankSize backgroundSize) :
    FinDist (HardVocabulary bankSize backgroundSize) where
  mass b := P.commonMarginal b *
    P.interactionFactor sourceTrigger targetTrigger a b
  nonneg b := mul_nonneg (P.commonMarginal.nonneg b)
    (P.interactionFactor_pos sourceTrigger targetTrigger a b).le
  sum_mass := by
    calc
      (∑ b, P.commonMarginal b *
          P.interactionFactor sourceTrigger targetTrigger a b)
          = ∑ b, (P.commonMarginal b +
              (P.edgeCoupling * P.feature sourceTrigger a /
                P.triggerVariance) *
                (P.commonMarginal b * P.feature targetTrigger b)) := by
                  apply Finset.sum_congr rfl
                  intro b _
                  unfold interactionFactor
                  ring
      _ = (∑ b, P.commonMarginal b) +
            (P.edgeCoupling * P.feature sourceTrigger a /
              P.triggerVariance) *
              ∑ b, P.commonMarginal b * P.feature targetTrigger b := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 1 := by
        rw [P.commonMarginal.sum_mass, P.weighted_feature_sum]
        ring

@[simp]
theorem endpointKernel_apply (P : HardLocalParameters bankSize backgroundSize)
    (sourceTrigger targetTrigger : Fin bankSize)
    (a b : HardVocabulary bankSize backgroundSize) :
    P.endpointKernel sourceTrigger targetTrigger a b =
      P.commonMarginal b *
        P.interactionFactor sourceTrigger targetTrigger a b := rfl

theorem endpointKernel_strictlyPositive
    (P : HardLocalParameters bankSize backgroundSize)
    (sourceTrigger targetTrigger : Fin bankSize)
    (a : HardVocabulary bankSize backgroundSize) :
    (P.endpointKernel sourceTrigger targetTrigger a).StrictlyPositive := by
  intro b
  exact mul_pos (P.commonMarginal_strictlyPositive b)
    (P.interactionFactor_pos sourceTrigger targetTrigger a b)

/-- For a revealed nontrigger source, the hard conditional's displacement
from the common marginal has a one-feature closed form. -/
theorem endpointKernel_sub_common_of_ne_trigger
    (P : HardLocalParameters bankSize backgroundSize)
    (sourceTrigger targetTrigger : Fin bankSize)
    {a : HardVocabulary bankSize backgroundSize}
    (ha : a ≠ Sum.inl sourceTrigger)
    (b : HardVocabulary bankSize backgroundSize) :
    P.endpointKernel sourceTrigger targetTrigger a b - P.commonMarginal b =
      -(P.commonMarginal b * P.edgeCoupling * P.feature targetTrigger b) /
        (1 - P.triggerMass) := by
  rw [endpointKernel_apply]
  unfold interactionFactor
  rw [P.feature_off_trigger sourceTrigger ha]
  unfold triggerVariance
  have hθ : P.triggerMass ≠ 0 := ne_of_gt P.trigger_pos
  have h1θ : 1 - P.triggerMass ≠ 0 :=
    ne_of_gt (sub_pos.mpr P.triggerMass_lt_one)
  field_simp
  ring

/-- Exact Pearson divergence in the sole inexact branch of the selected
oracle. -/
theorem endpointKernel_chiSquare_common_of_ne_trigger
    (P : HardLocalParameters bankSize backgroundSize)
    (sourceTrigger targetTrigger : Fin bankSize)
    {a : HardVocabulary bankSize backgroundSize}
    (ha : a ≠ Sum.inl sourceTrigger) :
    FinDist.chiSquare
      (P.endpointKernel sourceTrigger targetTrigger a) P.commonMarginal =
        P.edgeCoupling ^ 2 * P.triggerMass / (1 - P.triggerMass) := by
  unfold FinDist.chiSquare
  simp_rw [P.endpointKernel_sub_common_of_ne_trigger
    sourceTrigger targetTrigger ha]
  calc
    (∑ b,
        (-(P.commonMarginal b * P.edgeCoupling * P.feature targetTrigger b) /
            (1 - P.triggerMass)) ^ 2 / P.commonMarginal b) =
        (P.edgeCoupling ^ 2 / (1 - P.triggerMass) ^ 2) *
          ∑ b, P.commonMarginal b * (P.feature targetTrigger b) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            have hb : P.commonMarginal b ≠ 0 :=
              ne_of_gt (P.commonMarginal_strictlyPositive b)
            have h1θ : 1 - P.triggerMass ≠ 0 :=
              ne_of_gt (sub_pos.mpr P.triggerMass_lt_one)
            field_simp
    _ = (P.edgeCoupling ^ 2 / (1 - P.triggerMass) ^ 2) *
          P.triggerVariance := by
            rw [P.weighted_feature_sq_sum]
    _ = P.edgeCoupling ^ 2 * P.triggerMass /
          (1 - P.triggerMass) := by
            unfold triggerVariance
            have h1θ : 1 - P.triggerMass ≠ 0 :=
              ne_of_gt (sub_pos.mpr P.triggerMass_lt_one)
            field_simp

/-- The squared-Hellinger bound quoted in
`app:eq:hard-local-oracle-error`. -/
theorem endpointKernel_sqHellinger_common_of_ne_trigger
    (P : HardLocalParameters bankSize backgroundSize)
    (sourceTrigger targetTrigger : Fin bankSize)
    {a : HardVocabulary bankSize backgroundSize}
    (ha : a ≠ Sum.inl sourceTrigger) :
    FinDist.sqHellinger
        (P.endpointKernel sourceTrigger targetTrigger a) P.commonMarginal ≤
      P.edgeCoupling ^ 2 * P.triggerMass /
        (2 * (1 - P.triggerMass)) := by
  calc
    FinDist.sqHellinger
        (P.endpointKernel sourceTrigger targetTrigger a) P.commonMarginal ≤
        FinDist.chiSquare
          (P.endpointKernel sourceTrigger targetTrigger a) P.commonMarginal / 2 :=
      FinDist.sqHellinger_le_half_chiSquare _ _
        P.commonMarginal_strictlyPositive
    _ = P.edgeCoupling ^ 2 * P.triggerMass /
          (2 * (1 - P.triggerMass)) := by
            rw [P.endpointKernel_chiSquare_common_of_ne_trigger
              sourceTrigger targetTrigger ha]
            have h1θ : 1 - P.triggerMass ≠ 0 :=
              ne_of_gt (sub_pos.mpr P.triggerMass_lt_one)
            field_simp

theorem endpointKernel_sqHellinger_common_le_coupling_sq_mul_trigger
    (P : HardLocalParameters bankSize backgroundSize)
    (sourceTrigger targetTrigger : Fin bankSize)
    {a : HardVocabulary bankSize backgroundSize}
    (ha : a ≠ Sum.inl sourceTrigger) :
    FinDist.sqHellinger
        (P.endpointKernel sourceTrigger targetTrigger a) P.commonMarginal ≤
      P.edgeCoupling ^ 2 * P.triggerMass := by
  have hden : 0 < 2 * (1 - P.triggerMass) := by
    nlinarith [P.trigger_le_half]
  have hnum : 0 ≤ P.edgeCoupling ^ 2 * P.triggerMass :=
    mul_nonneg (sq_nonneg _) P.trigger_pos.le
  calc
    _ ≤ P.edgeCoupling ^ 2 * P.triggerMass /
          (2 * (1 - P.triggerMass)) :=
      P.endpointKernel_sqHellinger_common_of_ne_trigger
        sourceTrigger targetTrigger ha
    _ ≤ P.edgeCoupling ^ 2 * P.triggerMass := by
      exact (div_le_iff₀ hden).2 (by
        nlinarith [P.trigger_le_half])

/-- The TV error in the selected oracle's inexact local branch is exactly
`edgeCoupling * triggerMass`, as stated in `app:rem:oracle-slack`. -/
theorem endpointKernel_tv_common_of_ne_trigger
    (P : HardLocalParameters bankSize backgroundSize)
    (sourceTrigger targetTrigger : Fin bankSize)
    {a : HardVocabulary bankSize backgroundSize}
    (ha : a ≠ Sum.inl sourceTrigger) :
    FinDist.tv
        (P.endpointKernel sourceTrigger targetTrigger a) P.commonMarginal =
      P.edgeCoupling * P.triggerMass := by
  unfold FinDist.tv
  simp_rw [P.endpointKernel_sub_common_of_ne_trigger
    sourceTrigger targetTrigger ha]
  have hdenpos : 0 < 1 - P.triggerMass :=
    sub_pos.mpr P.triggerMass_lt_one
  have hterm : ∀ b : HardVocabulary bankSize backgroundSize,
      |-(P.commonMarginal b * P.edgeCoupling * P.feature targetTrigger b) /
          (1 - P.triggerMass)| =
        (P.edgeCoupling / (1 - P.triggerMass)) *
          (P.commonMarginal b * |P.feature targetTrigger b|) := by
    intro b
    rw [abs_div, abs_neg, abs_mul, abs_mul,
      abs_of_nonneg (P.commonMarginal.nonneg b),
      abs_of_pos P.coupling_pos, abs_of_pos hdenpos]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, P.weighted_abs_feature_sum]
  unfold triggerVariance
  have hden : 1 - P.triggerMass ≠ 0 := ne_of_gt hdenpos
  field_simp

/-- One correlated matching-edge law. -/
def edgeLaw (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize) :
    FinDist (HardVocabulary bankSize backgroundSize ×
      HardVocabulary bankSize backgroundSize) where
  mass x := P.commonMarginal x.1 *
    P.endpointKernel leftTrigger rightTrigger x.1 x.2
  nonneg x := mul_nonneg (P.commonMarginal.nonneg x.1)
    ((P.endpointKernel leftTrigger rightTrigger x.1).nonneg x.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ a, ∑ b, P.commonMarginal a *
          P.endpointKernel leftTrigger rightTrigger a b)
          = ∑ a, P.commonMarginal a *
              ∑ b, P.endpointKernel leftTrigger rightTrigger a b := by
                apply Finset.sum_congr rfl
                intro a _
                rw [Finset.mul_sum]
      _ = ∑ a, P.commonMarginal a := by
            simp only [FinDist.sum_mass, mul_one]
      _ = 1 := P.commonMarginal.sum_mass

@[simp]
theorem edgeLaw_apply (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize)
    (a b : HardVocabulary bankSize backgroundSize) :
    P.edgeLaw leftTrigger rightTrigger (a, b) =
      P.commonMarginal a * P.commonMarginal b *
        P.interactionFactor leftTrigger rightTrigger a b := by
  simp [edgeLaw, endpointKernel_apply, mul_assoc]

theorem edgeLaw_strictlyPositive
    (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize) :
    (P.edgeLaw leftTrigger rightTrigger).StrictlyPositive := by
  intro x
  exact mul_pos (P.commonMarginal_strictlyPositive x.1)
    (P.endpointKernel_strictlyPositive leftTrigger rightTrigger x.1 x.2)

/-- The left endpoint marginal of an edge is the common marginal. -/
theorem edgeLaw_left_sum (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize)
    (a : HardVocabulary bankSize backgroundSize) :
    ∑ b, P.edgeLaw leftTrigger rightTrigger (a, b) =
      P.commonMarginal a := by
  change (∑ b, P.commonMarginal a *
      P.endpointKernel leftTrigger rightTrigger a b) = P.commonMarginal a
  rw [← Finset.mul_sum]
  rw [(P.endpointKernel leftTrigger rightTrigger a).sum_mass, mul_one]

/-- The right endpoint marginal of an edge is also the common marginal. -/
theorem edgeLaw_right_sum (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize)
    (b : HardVocabulary bankSize backgroundSize) :
    ∑ a, P.edgeLaw leftTrigger rightTrigger (a, b) =
      P.commonMarginal b := by
  calc
    (∑ a, P.edgeLaw leftTrigger rightTrigger (a, b)) =
        ∑ a, P.commonMarginal b *
          P.endpointKernel rightTrigger leftTrigger b a := by
            apply Finset.sum_congr rfl
            intro a _
            simp only [edgeLaw_apply, endpointKernel_apply, interactionFactor]
            ring
    _ = P.commonMarginal b *
          ∑ a, P.endpointKernel rightTrigger leftTrigger b a := by
            rw [Finset.mul_sum]
    _ = P.commonMarginal b := by
          rw [(P.endpointKernel rightTrigger leftTrigger b).sum_mass, mul_one]

theorem edgeLaw_map_fst (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize) :
    (P.edgeLaw leftTrigger rightTrigger).map Prod.fst =
      P.commonMarginal := by
  ext a
  rw [FinDist.map_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simpa only [ite_true] using
      P.edgeLaw_left_sum leftTrigger rightTrigger a
  · intro a' _ ha'
    simp only [ha', ite_false, Finset.sum_const_zero]
  · simp

theorem edgeLaw_map_snd (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize) :
    (P.edgeLaw leftTrigger rightTrigger).map Prod.snd =
      P.commonMarginal := by
  ext b
  rw [FinDist.map_apply, Fintype.sum_prod_type]
  calc
    (∑ a, ∑ b', if b' = b then P.edgeLaw leftTrigger rightTrigger (a, b') else 0) =
        ∑ a, P.edgeLaw leftTrigger rightTrigger (a, b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Fintype.sum_ite_eq']
    _ = P.commonMarginal b := P.edgeLaw_right_sum leftTrigger rightTrigger b

/-- The event that the left endpoint equals `a` has its common-marginal
probability. -/
theorem edgeLaw_eventMass_fst_eq
    (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize)
    (a : HardVocabulary bankSize backgroundSize) :
    (P.edgeLaw leftTrigger rightTrigger).eventMass (fun z ↦ z.1 = a) =
      P.commonMarginal a := by
  change (P.edgeLaw leftTrigger rightTrigger).map Prod.fst a =
    P.commonMarginal a
  rw [P.edgeLaw_map_fst]

/-- The event that the right endpoint equals `b` has its common-marginal
probability. -/
theorem edgeLaw_eventMass_snd_eq
    (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize)
    (b : HardVocabulary bankSize backgroundSize) :
    (P.edgeLaw leftTrigger rightTrigger).eventMass (fun z ↦ z.2 = b) =
      P.commonMarginal b := by
  change (P.edgeLaw leftTrigger rightTrigger).map Prod.snd b =
    P.commonMarginal b
  rw [P.edgeLaw_map_snd]

/-- Revealing the left endpoint makes the exact right conditional equal to
the forward endpoint kernel. -/
theorem edgeLaw_conditionalMap_snd_given_fst
    (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize)
    (a : HardVocabulary bankSize backgroundSize) :
    (P.edgeLaw leftTrigger rightTrigger).conditionalMap
        (fun z ↦ z.1 = a)
        (by rw [P.edgeLaw_eventMass_fst_eq leftTrigger rightTrigger a]
            exact P.commonMarginal_strictlyPositive a)
        Prod.snd =
      P.endpointKernel leftTrigger rightTrigger a := by
  ext b
  unfold FinDist.conditionalMap
  rw [FinDist.map_apply, Fintype.sum_prod_type]
  change
    (∑ x, ∑ y,
      if y = b then
        (if x = a then
          P.edgeLaw leftTrigger rightTrigger (x, y) /
            (P.edgeLaw leftTrigger rightTrigger).eventMass
              (fun z ↦ z.1 = a)
        else 0)
      else 0) =
      P.endpointKernel leftTrigger rightTrigger a b
  calc
    _ = P.edgeLaw leftTrigger rightTrigger (a, b) /
          (P.edgeLaw leftTrigger rightTrigger).eventMass
            (fun z ↦ z.1 = a) := by
          simp
    _ = P.commonMarginal a *
          P.endpointKernel leftTrigger rightTrigger a b /
            P.commonMarginal a := by
          rw [P.edgeLaw_eventMass_fst_eq]
          rfl
    _ = P.endpointKernel leftTrigger rightTrigger a b := by
          exact mul_div_cancel_left₀ _
            (ne_of_gt (P.commonMarginal_strictlyPositive a))

/-- Revealing the right endpoint makes the exact left conditional equal to
the reverse endpoint kernel. -/
theorem edgeLaw_conditionalMap_fst_given_snd
    (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize)
    (b : HardVocabulary bankSize backgroundSize) :
    (P.edgeLaw leftTrigger rightTrigger).conditionalMap
        (fun z ↦ z.2 = b)
        (by rw [P.edgeLaw_eventMass_snd_eq leftTrigger rightTrigger b]
            exact P.commonMarginal_strictlyPositive b)
        Prod.fst =
      P.endpointKernel rightTrigger leftTrigger b := by
  ext a
  unfold FinDist.conditionalMap
  rw [FinDist.map_apply, Fintype.sum_prod_type]
  change
    (∑ x, ∑ y,
      if x = a then
        (if y = b then
          P.edgeLaw leftTrigger rightTrigger (x, y) /
            (P.edgeLaw leftTrigger rightTrigger).eventMass
              (fun z ↦ z.2 = b)
        else 0)
      else 0) =
      P.endpointKernel rightTrigger leftTrigger b a
  calc
    _ = P.edgeLaw leftTrigger rightTrigger (a, b) /
          (P.edgeLaw leftTrigger rightTrigger).eventMass
            (fun z ↦ z.2 = b) := by
          simp
    _ = P.commonMarginal b *
          P.endpointKernel rightTrigger leftTrigger b a /
            P.commonMarginal b := by
          rw [P.edgeLaw_eventMass_snd_eq]
          rw [P.edgeLaw_apply, P.endpointKernel_apply]
          unfold interactionFactor
          ring
    _ = P.endpointKernel rightTrigger leftTrigger b a := by
          exact mul_div_cancel_left₀ _
            (ne_of_gt (P.commonMarginal_strictlyPositive b))

/-- Endpoint compatibility (C0) holds for the hard kernels. -/
theorem endpoint_compatibility
    (P : HardLocalParameters bankSize backgroundSize)
    (leftTrigger rightTrigger : Fin bankSize)
    (a b : HardVocabulary bankSize backgroundSize) :
    P.commonMarginal a * P.endpointKernel leftTrigger rightTrigger a b =
      P.commonMarginal b * P.endpointKernel rightTrigger leftTrigger b a := by
  simp only [endpointKernel_apply, interactionFactor]
  ring

end

end HardLocalParameters

/-! ## Product assembly over a perfect matching -/

/-- A perfect matching represented by its fixed-point-free mate involution. -/
structure PerfectMatching (N : ℕ) where
  mate : Position N → Position N
  mate_ne_self : ∀ i, mate i ≠ i
  mate_mate : Function.Involutive mate

namespace PerfectMatching

variable {N : ℕ}

/-- The smaller endpoint of every matching edge, used once. -/
def representatives (M : PerfectMatching N) : Finset (Position N) :=
  Finset.univ.filter fun i ↦ i < M.mate i

/-- One index for each unordered matching edge. -/
abbrev EdgeIndex (M : PerfectMatching N) := M.representatives

@[simp]
theorem mem_representatives_iff (M : PerfectMatching N) (i : Position N) :
    i ∈ M.representatives ↔ i < M.mate i := by
  simp [representatives]

theorem mate_lt_of_not_lt (M : PerfectMatching N) {i : Position N}
    (hi : ¬i < M.mate i) :
    M.mate i < i := by
  exact lt_of_le_of_ne (le_of_not_gt hi) (M.mate_ne_self i)

theorem mate_mem_representatives_of_not_lt (M : PerfectMatching N)
    {i : Position N} (hi : ¬i < M.mate i) :
    M.mate i ∈ M.representatives := by
  rw [M.mem_representatives_iff, M.mate_mate i]
  exact M.mate_lt_of_not_lt hi

/-- The simple graph whose connected components are the matching pairs. -/
def graph (M : PerfectMatching N) : SimpleGraph (Position N) where
  Adj i j := M.mate i = j
  symm.symm := by
    intro i j hij
    simpa [← hij] using M.mate_mate i
  loopless.irrefl := M.mate_ne_self

@[simp]
theorem graph_adj_iff (M : PerfectMatching N) (i j : Position N) :
    M.graph.Adj i j ↔ M.mate i = j :=
  Iff.rfl

/-- A matching graph is acyclic: a cycle would give a vertex two distinct
neighbors, whereas its mate is its unique neighbor. -/
theorem graph_acyclic (M : PerfectMatching N) : M.graph.IsAcyclic := by
  intro v c hc
  have hsnd := c.adj_snd hc.not_nil
  have hpen := (c.adj_penultimate hc.not_nil).symm
  change M.mate v = c.snd at hsnd
  change M.mate v = c.penultimate at hpen
  exact hc.snd_ne_penultimate (hsnd.symm.trans hpen)

/-- Root each matching edge at its smaller endpoint. -/
def rooting (M : PerfectMatching N) : Rooting M.graph where
  roots := M.representatives
  parent := M.mate
  depth i := if i < M.mate i then 0 else 1
  root_iff_depth_zero := by
    intro i
    simp [representatives]
  parent_adj := by
    intro i _
    change M.mate (M.mate i) = i
    exact M.mate_mate i
  parent_depth_lt := by
    intro i hi
    have hnot : ¬i < M.mate i := by
      intro hlt
      apply hi
      exact (M.mem_representatives_iff i).2 hlt
    have hmate : M.mate i < i := M.mate_lt_of_not_lt hnot
    simp [hnot, hmate, M.mate_mate i]
  edge_oriented := by
    intro i j hij
    change M.mate i = j at hij
    by_cases hi : i ∈ M.representatives
    · right
      constructor
      · intro hj
        have hiless : i < M.mate i :=
          (M.mem_representatives_iff i).1 hi
        have hjless : j < M.mate j :=
          (M.mem_representatives_iff j).1 hj
        rw [← hij, M.mate_mate i] at hjless
        exact (lt_asymm hiless hjless).elim
      · simpa [← hij] using M.mate_mate i
    · exact Or.inl ⟨hi, hij⟩

theorem mate_not_mem_representatives (M : PerfectMatching N)
    {i : Position N} (hi : i ∈ M.representatives) :
    M.mate i ∉ M.representatives := by
  intro hmate
  have hiless : i < M.mate i :=
    (M.mem_representatives_iff i).1 hi
  have hmateless : M.mate i < i := by
    simpa [M.mate_mate i] using
      (M.mem_representatives_iff (M.mate i)).1 hmate
  exact (lt_asymm hiless hmateless).elim

/-- Taking mates bijects the selected smaller endpoints with the nonroots. -/
def mateNonRootsEquiv (M : PerfectMatching N) :
    M.EdgeIndex ≃ M.rooting.nonRoots where
  toFun e := ⟨M.mate e.1, by
    rw [Rooting.mem_nonRoots_iff]
    exact M.mate_not_mem_representatives e.2⟩
  invFun j := ⟨M.mate j.1, by
    apply M.mate_mem_representatives_of_not_lt
    intro hjlt
    apply (Rooting.mem_nonRoots_iff M.rooting j.1).1 j.2
    exact (M.mem_representatives_iff j.1).2 hjlt⟩
  left_inv e := by
    apply Subtype.ext
    exact M.mate_mate e.1
  right_inv j := by
    apply Subtype.ext
    exact M.mate_mate j.1

@[simp]
theorem mateNonRootsEquiv_apply_val (M : PerfectMatching N)
    (e : M.EdgeIndex) :
    (M.mateNonRootsEquiv e).1 = M.mate e.1 :=
  rfl

variable {V : Type*}

/-- Repackage a complete configuration as endpoint pairs, one per edge. -/
def toPairs (M : PerfectMatching N) (x : Configuration N V) :
    M.EdgeIndex → V × V :=
  fun e ↦ (x e.1, x (M.mate e.1))

/-- Reassemble endpoint pairs into a complete configuration. -/
def fromPairs (M : PerfectMatching N) (z : M.EdgeIndex → V × V) :
    Configuration N V :=
  fun i ↦ if hi : i < M.mate i then
      (z ⟨i, (M.mem_representatives_iff i).2 hi⟩).1
    else
      (z ⟨M.mate i, M.mate_mem_representatives_of_not_lt hi⟩).2

theorem fromPairs_toPairs (M : PerfectMatching N)
    (x : Configuration N V) :
    M.fromPairs (M.toPairs x) = x := by
  funext i
  by_cases hi : i < M.mate i
  · simp [fromPairs, toPairs, hi]
  · simp [fromPairs, toPairs, hi, M.mate_mate i]

theorem toPairs_fromPairs (M : PerfectMatching N)
    (z : M.EdgeIndex → V × V) :
    M.toPairs (M.fromPairs z) = z := by
  funext e
  apply Prod.ext
  · simp [toPairs, fromPairs, (M.mem_representatives_iff e.1).1 e.2]
  · have he : e.1 < M.mate e.1 :=
      (M.mem_representatives_iff e.1).1 e.2
    have hmate : ¬M.mate e.1 < e.1 := not_lt_of_ge he.le
    simp [toPairs, fromPairs, M.mate_mate e.1, hmate]

/-- Equivalence between configurations and matching-edge endpoint pairs. -/
def pairEquiv (M : PerfectMatching N) :
    Configuration N V ≃ (M.EdgeIndex → V × V) where
  toFun := M.toPairs
  invFun := M.fromPairs
  left_inv := M.fromPairs_toPairs
  right_inv := M.toPairs_fromPairs

/-! Coordinatewise observation events on matching-edge pairs. -/

/-- A pair on one matching edge agrees with the observations at both of its
endpoints. -/
def edgeAgrees (M : PerfectMatching N) (y : MaskedState N V)
    (e : M.EdgeIndex) (z : V × V) : Prop :=
  (∀ a, y e.1 = some a → z.1 = a) ∧
    (∀ b, y (M.mate e.1) = some b → z.2 = b)

noncomputable instance edgeAgreesDecidablePred
    (M : PerfectMatching N) (y : MaskedState N V) (e : M.EdgeIndex) :
    DecidablePred (M.edgeAgrees y e) :=
  fun _ ↦ Classical.propDecidable _

/-- Global agreement after reassembling pairs is exactly coordinatewise
agreement on every matching edge. -/
theorem agrees_fromPairs_iff [DecidableEq V]
    (M : PerfectMatching N) (y : MaskedState N V)
    (z : M.EdgeIndex → V × V) :
    y.Agrees (M.fromPairs z) ↔ ∀ e, M.edgeAgrees y e (z e) := by
  constructor
  · intro hy e
    have hpair := congrFun (M.toPairs_fromPairs z) e
    constructor
    · intro a ha
      have hx := hy e.1 a ha
      exact (congrArg Prod.fst hpair).symm.trans hx
    · intro b hb
      have hx := hy (M.mate e.1) b hb
      exact (congrArg Prod.snd hpair).symm.trans hx
  · intro hz i a hya
    by_cases hi : i < M.mate i
    · simpa [PerfectMatching.fromPairs, hi] using
        (hz ⟨i, (M.mem_representatives_iff i).2 hi⟩).1 a hya
    · let e : M.EdgeIndex :=
        ⟨M.mate i, M.mate_mem_representatives_of_not_lt hi⟩
      have hobs : y (M.mate e.1) = some a := by
        simpa [e, M.mate_mate i] using hya
      have hv := (hz e).2 a hobs
      simpa [PerfectMatching.fromPairs, hi, e] using hv

/-- Completing every mask supplies a witness for every local edge-agreement
event. -/
theorem edgeAgrees_completion [DecidableEq V]
    (M : PerfectMatching N) (y : MaskedState N V)
    (e : M.EdgeIndex) (fallback : V) :
    M.edgeAgrees y e (M.toPairs (y.completion fallback) e) := by
  apply (M.agrees_fromPairs_iff y (M.toPairs (y.completion fallback))).mp
  rw [M.fromPairs_toPairs]
  exact y.completion_agrees fallback

/-- Every local edge-agreement event has positive mass under a strictly
positive edge law. -/
theorem edgeAgrees_eventMass_pos [Fintype V] [DecidableEq V] [Nonempty V]
    (M : PerfectMatching N) (y : MaskedState N V)
    (e : M.EdgeIndex) (p : FinDist (V × V))
    (hp : p.StrictlyPositive) :
    0 < p.eventMass (M.edgeAgrees y e) := by
  classical
  let fallback : V := Classical.choice (inferInstance : Nonempty V)
  exact p.eventMass_pos_of_exists hp (M.edgeAgrees y e)
    ⟨M.toPairs (y.completion fallback) e,
      M.edgeAgrees_completion y e fallback⟩

end PerfectMatching

namespace HardMatching

variable {N bankSize backgroundSize : ℕ}

noncomputable section

/-- Full target law obtained by taking the product over matching edges. -/
def target (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize) :
    FinDist (Configuration N (HardVocabulary bankSize backgroundSize)) :=
  (FinDist.piProduct fun e : M.EdgeIndex ↦
    P.edgeLaw (trigger e.1) (trigger (M.mate e.1))).map
      (M.pairEquiv (V := HardVocabulary bankSize backgroundSize)).symm

@[simp]
theorem target_apply (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (x : Configuration N (HardVocabulary bankSize backgroundSize)) :
    target P M trigger x =
      ∏ e : M.EdgeIndex,
        P.edgeLaw (trigger e.1) (trigger (M.mate e.1))
          (x e.1, x (M.mate e.1)) := by
  unfold target
  rw [FinDist.map_equiv_apply]
  rfl

theorem target_strictlyPositive
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize) :
    (target P M trigger).StrictlyPositive := by
  unfold target
  apply FinDist.map_strictlyPositive_of_surjective
  · apply FinDist.piProduct_strictlyPositive
    intro e
    exact P.edgeLaw_strictlyPositive (trigger e.1) (trigger (M.mate e.1))
  · exact (M.pairEquiv (V := HardVocabulary bankSize backgroundSize)).symm.surjective

/-- Every position of the full hard target has the advertised public common
marginal. -/
theorem target_positionMarginal
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (i : Position N) :
    (target P M trigger).positionMarginal i = P.commonMarginal := by
  unfold FinDist.positionMarginal target
  rw [FinDist.map_comp]
  by_cases hi : i < M.mate i
  · let e : M.EdgeIndex :=
      ⟨i, (M.mem_representatives_iff i).2 hi⟩
    have hfun :
        ((fun x : Configuration N (HardVocabulary bankSize backgroundSize) ↦ x i) ∘
            (M.pairEquiv (V := HardVocabulary bankSize backgroundSize)).symm) =
          Prod.fst ∘ (fun z ↦ z e) := by
      funext z
      simp [PerfectMatching.pairEquiv, PerfectMatching.fromPairs, hi, e]
    rw [hfun, ← FinDist.map_comp, FinDist.piProduct_map_eval]
    exact P.edgeLaw_map_fst (trigger i) (trigger (M.mate i))
  · let e : M.EdgeIndex :=
      ⟨M.mate i, M.mate_mem_representatives_of_not_lt hi⟩
    have hfun :
        ((fun x : Configuration N (HardVocabulary bankSize backgroundSize) ↦ x i) ∘
            (M.pairEquiv (V := HardVocabulary bankSize backgroundSize)).symm) =
          Prod.snd ∘ (fun z ↦ z e) := by
      funext z
      simp [PerfectMatching.pairEquiv, PerfectMatching.fromPairs, hi, e]
    rw [hfun, ← FinDist.map_comp, FinDist.piProduct_map_eval]
    simpa [e, M.mate_mate i] using
      P.edgeLaw_map_snd (trigger (M.mate i)) (trigger i)

/-- The endpoint kernels attached to every ordered pair.  Their values away
from matching edges are harmless totalizations; only graph edges enter the
forest assumptions. -/
def kernel (P : HardLocalParameters bankSize backgroundSize)
    (trigger : Position N → Fin bankSize) :
    EndpointKernel N (HardVocabulary bankSize backgroundSize) :=
  fun i j ↦ P.endpointKernel (trigger i) (trigger j)

theorem kernel_strictlyPositive
    (P : HardLocalParameters bankSize backgroundSize)
    (trigger : Position N → Fin bankSize) (i j : Position N)
    (a : HardVocabulary bankSize backgroundSize) :
    (kernel P trigger i j a).StrictlyPositive :=
  P.endpointKernel_strictlyPositive (trigger i) (trigger j) a

/-- The matching product has exactly the rooted forest factorization (S0). -/
theorem target_factorizes
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize) :
    ForestFactorization.Holds (target P M trigger) (kernel P trigger)
      M.graph M.rooting := by
  intro x
  rw [target_apply]
  unfold ForestFactorization.mass
  simp_rw [target_positionMarginal]
  change
    (∏ e : M.EdgeIndex,
        P.edgeLaw (trigger e.1) (trigger (M.mate e.1))
          (x e.1, x (M.mate e.1))) =
      (∏ i ∈ M.representatives, P.commonMarginal (x i)) *
        ∏ j ∈ M.rooting.nonRoots,
          P.endpointKernel (trigger (M.mate j)) (trigger j)
            (x (M.mate j)) (x j)
  rw [← Finset.prod_coe_sort M.representatives
    (fun i ↦ P.commonMarginal (x i))]
  rw [← Finset.prod_coe_sort M.rooting.nonRoots
    (fun j ↦ P.endpointKernel (trigger (M.mate j)) (trigger j)
      (x (M.mate j)) (x j))]
  rw [← (M.mateNonRootsEquiv).prod_comp
    (fun j : M.rooting.nonRoots ↦
      P.endpointKernel (trigger (M.mate j.1)) (trigger j.1)
        (x (M.mate j.1)) (x j.1))]
  simp only [PerfectMatching.mateNonRootsEquiv_apply_val]
  simp_rw [HardLocalParameters.edgeLaw]
  rw [Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  rw [M.mate_mate e.1]

/-- The full hard target and its kernels satisfy endpoint compatibility (C0). -/
theorem target_endpointCompatible
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize) :
    ForestFactorization.EndpointCompatible (target P M trigger)
      (kernel P trigger) M.graph := by
  intro i j _ a b
  rw [target_positionMarginal, target_positionMarginal]
  exact P.endpoint_compatibility (trigger i) (trigger j) a b

/-- The explicit hard matching target packaged as an instance of the common
finite forest model. -/
def model (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize) :
    ForestModel N (HardVocabulary bankSize backgroundSize) where
  target := target P M trigger
  target_positive := target_strictlyPositive P M trigger
  graph := M.graph
  graph_acyclic := M.graph_acyclic
  kernel := kernel P trigger
  kernel_positive := by
    intro i j _ a
    exact kernel_strictlyPositive P trigger i j a
  rooting := M.rooting
  factorizes := target_factorizes P M trigger
  endpoint_compatible := target_endpointCompatible P M trigger

@[simp]
theorem model_target
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize) :
    (model P M trigger).target = target P M trigger :=
  rfl

theorem model_marginal
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (i : Position N) :
    (model P M trigger).marginal i = P.commonMarginal :=
  target_positionMarginal P M trigger i

/-! ## Selected frozen oracle and instance family -/

/-- If the left endpoint is masked, conditioning one edge on all visible
endpoint observations and reading left depends only on the right endpoint's
observation. -/
theorem edgeAgrees_conditionalMap_fst
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize))
    (e : M.EdgeIndex) (hmask : y e.1 = none) :
    (P.edgeLaw (trigger e.1) (trigger (M.mate e.1))).conditionalMap
        (M.edgeAgrees y e)
        (M.edgeAgrees_eventMass_pos y e
          (P.edgeLaw (trigger e.1) (trigger (M.mate e.1)))
          (P.edgeLaw_strictlyPositive
            (trigger e.1) (trigger (M.mate e.1))))
        Prod.fst =
      match y (M.mate e.1) with
      | none => P.commonMarginal
      | some b =>
          P.endpointKernel (trigger (M.mate e.1)) (trigger e.1) b := by
  let p := P.edgeLaw (trigger e.1) (trigger (M.mate e.1))
  have hlocal : 0 < p.eventMass (M.edgeAgrees y e) :=
    M.edgeAgrees_eventMass_pos y e p
      (P.edgeLaw_strictlyPositive (trigger e.1) (trigger (M.mate e.1)))
  cases hmate : y (M.mate e.1) with
  | none =>
      have hevent : ∀ z, M.edgeAgrees y e z ↔ True := by
        intro z
        simp [PerfectMatching.edgeAgrees, hmask, hmate]
      calc
        p.conditionalMap (M.edgeAgrees y e) hlocal Prod.fst =
            p.conditionalMap (fun _ ↦ True)
              (by rw [p.eventMass_true]; norm_num) Prod.fst := by
                exact FinDist.conditionalMap_congr p
                  (M.edgeAgrees y e) (fun _ ↦ True) hlocal _
                  Prod.fst Prod.fst hevent (fun _ ↦ rfl)
        _ = p.map Prod.fst := p.conditionalMap_true Prod.fst
        _ = P.commonMarginal := by
              exact P.edgeLaw_map_fst (trigger e.1) (trigger (M.mate e.1))
  | some b =>
      have hevent : ∀ z, M.edgeAgrees y e z ↔ z.2 = b := by
        intro z
        simp [PerfectMatching.edgeAgrees, hmask, hmate]
      calc
        p.conditionalMap (M.edgeAgrees y e) hlocal Prod.fst =
            p.conditionalMap (fun z ↦ z.2 = b)
              (by rw [P.edgeLaw_eventMass_snd_eq
                    (trigger e.1) (trigger (M.mate e.1)) b]
                  exact P.commonMarginal_strictlyPositive b)
              Prod.fst := by
                exact FinDist.conditionalMap_congr p
                  (M.edgeAgrees y e) (fun z ↦ z.2 = b) hlocal _
                  Prod.fst Prod.fst hevent (fun _ ↦ rfl)
        _ = P.endpointKernel (trigger (M.mate e.1)) (trigger e.1) b :=
          P.edgeLaw_conditionalMap_fst_given_snd
            (trigger e.1) (trigger (M.mate e.1)) b

/-- If the right endpoint is masked, the analogous conditional readout is
the common marginal or the forward endpoint kernel according to the visible
left endpoint. -/
theorem edgeAgrees_conditionalMap_snd
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize))
    (e : M.EdgeIndex) (hmask : y (M.mate e.1) = none) :
    (P.edgeLaw (trigger e.1) (trigger (M.mate e.1))).conditionalMap
        (M.edgeAgrees y e)
        (M.edgeAgrees_eventMass_pos y e
          (P.edgeLaw (trigger e.1) (trigger (M.mate e.1)))
          (P.edgeLaw_strictlyPositive
            (trigger e.1) (trigger (M.mate e.1))))
        Prod.snd =
      match y e.1 with
      | none => P.commonMarginal
      | some a => P.endpointKernel (trigger e.1) (trigger (M.mate e.1)) a := by
  let p := P.edgeLaw (trigger e.1) (trigger (M.mate e.1))
  have hlocal : 0 < p.eventMass (M.edgeAgrees y e) :=
    M.edgeAgrees_eventMass_pos y e p
      (P.edgeLaw_strictlyPositive (trigger e.1) (trigger (M.mate e.1)))
  cases hmate : y e.1 with
  | none =>
      have hevent : ∀ z, M.edgeAgrees y e z ↔ True := by
        intro z
        simp [PerfectMatching.edgeAgrees, hmask, hmate]
      calc
        p.conditionalMap (M.edgeAgrees y e) hlocal Prod.snd =
            p.conditionalMap (fun _ ↦ True)
              (by rw [p.eventMass_true]; norm_num) Prod.snd := by
                exact FinDist.conditionalMap_congr p
                  (M.edgeAgrees y e) (fun _ ↦ True) hlocal _
                  Prod.snd Prod.snd hevent (fun _ ↦ rfl)
        _ = p.map Prod.snd := p.conditionalMap_true Prod.snd
        _ = P.commonMarginal := by
              exact P.edgeLaw_map_snd (trigger e.1) (trigger (M.mate e.1))
  | some a =>
      have hevent : ∀ z, M.edgeAgrees y e z ↔ z.1 = a := by
        intro z
        simp [PerfectMatching.edgeAgrees, hmask, hmate]
      calc
        p.conditionalMap (M.edgeAgrees y e) hlocal Prod.snd =
            p.conditionalMap (fun z ↦ z.1 = a)
              (by rw [P.edgeLaw_eventMass_fst_eq
                    (trigger e.1) (trigger (M.mate e.1)) a]
                  exact P.commonMarginal_strictlyPositive a)
              Prod.snd := by
                exact FinDist.conditionalMap_congr p
                  (M.edgeAgrees y e) (fun z ↦ z.1 = a) hlocal _
                  Prod.snd Prod.snd hevent (fun _ ↦ rfl)
        _ = P.endpointKernel (trigger e.1) (trigger (M.mate e.1)) a :=
          P.edgeLaw_conditionalMap_snd_given_fst
            (trigger e.1) (trigger (M.mate e.1)) a

/-- The true local conditional predicted by matching-edge independence: it
is the common marginal when the mate is masked and the edge kernel at the
mate's value when the mate is observed. -/
def idealRow (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize))
    (j : MaskedPosition y) :
    FinDist (HardVocabulary bankSize backgroundSize) :=
  match y (M.mate j.1) with
  | none => P.commonMarginal
  | some a =>
      P.endpointKernel (trigger (M.mate j.1)) (trigger j.1) a

/-- The selected hard-family row from `app:eq:hard-oracle`.

It exposes the edge kernel only when the mate is visibly equal to its private
trigger.  If the mate is masked or visibly nontrigger, it returns the common
marginal. -/
def selectedRow (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize))
    (j : MaskedPosition y) :
    FinDist (HardVocabulary bankSize backgroundSize) :=
  if y (M.mate j.1) = some (Sum.inl (trigger (M.mate j.1))) then
    P.endpointKernel (trigger (M.mate j.1)) (trigger j.1)
      (Sum.inl (trigger (M.mate j.1)))
  else
    P.commonMarginal

theorem selectedRow_strictlyPositive
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize))
    (j : MaskedPosition y) :
    (selectedRow P M trigger y j).StrictlyPositive := by
  unfold selectedRow
  split
  · exact P.endpointKernel_strictlyPositive
      (trigger (M.mate j.1)) (trigger j.1)
      (Sum.inl (trigger (M.mate j.1)))
  · exact P.commonMarginal_strictlyPositive

/-- Before proving the global conditioning identity, the entire numerical
oracle-error calculation can already be reduced to the one local branch. -/
theorem idealRow_selectedRow_sqHellinger_le
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize))
    (j : MaskedPosition y) :
    FinDist.sqHellinger (idealRow P M trigger y j)
        (selectedRow P M trigger y j) ≤
      P.edgeCoupling ^ 2 * P.triggerMass := by
  unfold idealRow selectedRow
  cases hmate : y (M.mate j.1) with
  | none =>
      simp [hmate, FinDist.sqHellinger_self,
        mul_nonneg (sq_nonneg P.edgeCoupling) P.trigger_pos.le]
  | some a =>
      by_cases ha : a = Sum.inl (trigger (M.mate j.1))
      · subst a
        simp [hmate, FinDist.sqHellinger_self,
          mul_nonneg (sq_nonneg P.edgeCoupling) P.trigger_pos.le]
      · simp only [hmate, ha, Option.some.injEq, ite_false]
        exact P.endpointKernel_sqHellinger_common_le_coupling_sq_mul_trigger
          (trigger (M.mate j.1)) (trigger j.1) ha

/-- The sole remaining probabilistic identity needed to turn the preceding
local calculation into (A2). -/
def ExactRowCharacterization
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize) : Prop :=
  ∀ (y : MaskedState N (HardVocabulary bankSize backgroundSize))
    (j : MaskedPosition y),
    y.exactRow (model P M trigger).target
        (model P M trigger).target_positive j =
      idealRow P M trigger y j

/-- Exact conditional rows of the full matching product are precisely the
local laws described by `idealRow`. -/
theorem exactRowCharacterization
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize) :
    ExactRowCharacterization P M trigger := by
  classical
  intro y j
  let edgeP : M.EdgeIndex →
      FinDist (HardVocabulary bankSize backgroundSize ×
        HardVocabulary bankSize backgroundSize) :=
    fun e ↦ P.edgeLaw (trigger e.1) (trigger (M.mate e.1))
  let q := FinDist.piProduct edgeP
  let assemble :=
    (M.pairEquiv (V := HardVocabulary bankSize backgroundSize)).symm
  have hedge : ∀ e, 0 < (edgeP e).eventMass (M.edgeAgrees y e) := by
    intro e
    exact M.edgeAgrees_eventMass_pos y e (edgeP e) (by
      simpa [edgeP] using
        P.edgeLaw_strictlyPositive (trigger e.1) (trigger (M.mate e.1)))
  have hall :
      0 < q.eventMass (fun z ↦ ∀ e, M.edgeAgrees y e (z e)) := by
    exact FinDist.piProduct_eventMass_forall_pos edgeP
      (fun e ↦ M.edgeAgrees y e) hedge
  have hevent : ∀ z,
      (y.Agrees ∘ assemble) z ↔ ∀ e, M.edgeAgrees y e (z e) := by
    intro z
    simpa [assemble, PerfectMatching.pairEquiv, Function.comp_def] using
      (M.agrees_fromPairs_iff y z)
  have htransport : 0 < q.eventMass (y.Agrees ∘ assemble) := by
    rw [q.eventMass_congr (y.Agrees ∘ assemble)
      (fun z ↦ ∀ e, M.edgeAgrees y e (z e)) hevent]
    exact hall
  have hmapped : 0 < (q.map assemble).eventMass y.Agrees := by
    rw [q.map_equiv_eventMass assemble y.Agrees]
    exact htransport
  have htarget : target P M trigger = q.map assemble := by
    rfl
  have hmaskj : y j.1 = none :=
    (MaskedState.mem_masked_iff y j.1).mp j.2
  by_cases hj : j.1 < M.mate j.1
  · let e : M.EdgeIndex :=
      ⟨j.1, (M.mem_representatives_iff j.1).2 hj⟩
    have hreadout : ∀ z,
        (((fun x : Configuration N (HardVocabulary bankSize backgroundSize) ↦
            x j.1) ∘ assemble) z) = Prod.fst (z e) := by
      intro z
      simp [assemble, PerfectMatching.pairEquiv,
        PerfectMatching.fromPairs, hj, e]
    calc
      y.exactRow (model P M trigger).target
          (model P M trigger).target_positive j =
          (q.map assemble).conditionalMap y.Agrees hmapped
            (fun x ↦ x j.1) := by
              exact FinDist.conditionalMap_congr_dist htarget y.Agrees _ _
                (fun x ↦ x j.1)
      _ = q.conditionalMap (y.Agrees ∘ assemble) htransport
            ((fun x ↦ x j.1) ∘ assemble) := by
              exact q.map_equiv_conditionalMap assemble y.Agrees htransport
                (fun x ↦ x j.1)
      _ = q.conditionalMap (fun z ↦ ∀ e, M.edgeAgrees y e (z e)) hall
            (fun z ↦ Prod.fst (z e)) := by
              exact FinDist.conditionalMap_congr q
                (y.Agrees ∘ assemble)
                (fun z ↦ ∀ e, M.edgeAgrees y e (z e))
                htransport hall _ _ hevent hreadout
      _ = (edgeP e).conditionalMap (M.edgeAgrees y e) (hedge e)
            Prod.fst := by
              exact FinDist.piProduct_conditionalMap_eval edgeP
                (fun e ↦ M.edgeAgrees y e) hedge e Prod.fst
      _ = idealRow P M trigger y j := by
            simpa [edgeP, e, idealRow] using
              edgeAgrees_conditionalMap_fst P M trigger y e hmaskj
  · let e : M.EdgeIndex :=
      ⟨M.mate j.1, M.mate_mem_representatives_of_not_lt hj⟩
    have hreadout : ∀ z,
        (((fun x : Configuration N (HardVocabulary bankSize backgroundSize) ↦
            x j.1) ∘ assemble) z) = Prod.snd (z e) := by
      intro z
      simp [assemble, PerfectMatching.pairEquiv,
        PerfectMatching.fromPairs, hj, e]
    have hmaske : y (M.mate e.1) = none := by
      simpa [e, M.mate_mate j.1] using hmaskj
    calc
      y.exactRow (model P M trigger).target
          (model P M trigger).target_positive j =
          (q.map assemble).conditionalMap y.Agrees hmapped
            (fun x ↦ x j.1) := by
              exact FinDist.conditionalMap_congr_dist htarget y.Agrees _ _
                (fun x ↦ x j.1)
      _ = q.conditionalMap (y.Agrees ∘ assemble) htransport
            ((fun x ↦ x j.1) ∘ assemble) := by
              exact q.map_equiv_conditionalMap assemble y.Agrees htransport
                (fun x ↦ x j.1)
      _ = q.conditionalMap (fun z ↦ ∀ e, M.edgeAgrees y e (z e)) hall
            (fun z ↦ Prod.snd (z e)) := by
              exact FinDist.conditionalMap_congr q
                (y.Agrees ∘ assemble)
                (fun z ↦ ∀ e, M.edgeAgrees y e (z e))
                htransport hall _ _ hevent hreadout
      _ = (edgeP e).conditionalMap (M.edgeAgrees y e) (hedge e)
            Prod.snd := by
              exact FinDist.piProduct_conditionalMap_eval edgeP
                (fun e ↦ M.edgeAgrees y e) hedge e Prod.snd
      _ = idealRow P M trigger y j := by
            simpa [edgeP, e, idealRow, M.mate_mate j.1] using
              edgeAgrees_conditionalMap_snd P M trigger y e hmaske

/-- The deterministic frozen oracle selected for the lower-bound family. -/
def selectedOracle (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize) :
    FrozenOracle N (HardVocabulary bankSize backgroundSize) where
  row := selectedRow P M trigger
  row_positive := selectedRow_strictlyPositive P M trigger

@[simp]
theorem selectedOracle_row
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize))
    (j : MaskedPosition y) :
    (selectedOracle P M trigger).row y j = selectedRow P M trigger y j :=
  rfl

/-- Once matching-product conditioning is identified with `idealRow`, the
paper's scalar inclusion condition implies frozen-oracle accuracy (A2). -/
theorem selectedOracle_accurate_of_exactRowCharacterization
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (oracleRadius : ℝ)
    (hradius0 : 0 ≤ oracleRadius) (hradius1 : oracleRadius ≤ 1)
    (hscale : P.edgeCoupling ^ 2 * P.triggerMass ≤
      oracleRadius ^ 2 / (2 * (N : ℝ)))
    (hexact : ExactRowCharacterization P M trigger) :
    (selectedOracle P M trigger).Accurate (model P M trigger)
      oracleRadius := by
  refine ⟨hradius0, hradius1, ?_⟩
  intro y j
  rw [hexact y j]
  exact (idealRow_selectedRow_sqHellinger_le P M trigger y j).trans hscale

/-- Hidden data indexing the finite matching family. -/
abbrev InstanceIndex (N bankSize : ℕ) :=
  PerfectMatching N × (Position N → Fin bankSize)

/-- One fully typed target--oracle pair from the hard matching family. -/
def samplingInstance (P : HardLocalParameters bankSize backgroundSize)
    (I : InstanceIndex N bankSize) :
    SamplingInstance N (HardVocabulary bankSize backgroundSize) where
  model := model P I.1 I.2
  oracle := selectedOracle P I.1 I.2

/-- The explicit hard matching family, ranging over every matching and every
private trigger vector. -/
def family (P : HardLocalParameters bankSize backgroundSize) :
    InstanceIndex N bankSize →
      SamplingInstance N (HardVocabulary bankSize backgroundSize) :=
  samplingInstance P

end

end HardMatching

namespace MatchingLowerParameters

variable {N : ℕ}

/-- Size of the public background block in the paper's `vocabSize`
parameterization. -/
def backgroundSize (P : MatchingLowerParameters N) : ℕ :=
  P.vocabSize - P.bankSize

theorem backgroundSize_pos (P : MatchingLowerParameters N) :
    0 < P.backgroundSize := by
  exact Nat.sub_pos_of_lt P.bank_lt_vocab

/-- The finite lower-bound hypotheses imply exactly the local hypotheses used
to normalize the hard edge laws. -/
def toHardLocal (P : MatchingLowerParameters N) :
    HardLocalParameters P.bankSize P.backgroundSize where
  triggerMass := P.triggerMass
  edgeCoupling := P.edgeCoupling
  background_nonempty := P.backgroundSize_pos
  trigger_pos := lt_of_lt_of_le P.coupling_pos P.coupling_le_trigger
  bank_mass_lt_one := P.bank_mass_lt_one
  coupling_pos := P.coupling_pos
  coupling_le_trigger := P.coupling_le_trigger
  trigger_le_half := P.trigger_le_half

theorem hardVocabulary_card (P : MatchingLowerParameters N) :
    Fintype.card (HardVocabulary P.bankSize P.backgroundSize) = P.vocabSize := by
  rw [Fintype.card_sum]
  simp only [Fintype.card_fin]
  exact Nat.add_sub_of_le (Nat.le_of_lt P.bank_lt_vocab)

/-- The concrete hard family used to instantiate the abstract finite lower
statement. -/
noncomputable def hardFamily (P : MatchingLowerParameters N) :
    HardMatching.InstanceIndex N P.bankSize →
      SamplingInstance N (HardVocabulary P.bankSize P.backgroundSize) :=
  HardMatching.family P.toHardLocal

/-- The paper's finite lower theorem specialized to its explicit witness
family.  This remains a proposition until the collision argument is
formalized. -/
def ExplicitHardFamilyLowerBound (P : MatchingLowerParameters N) : Prop :=
  FiniteAdaptiveLowerBound P P.hardFamily

end MatchingLowerParameters

end ForestSampling
