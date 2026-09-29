import ForestSampling.HardMatching

set_option autoImplicit false

namespace ForestSampling

/-!
# Statements of the compiled September 26 manuscript

The old linear contracts in `PaperStatements` are retained for compatibility.
This module records the current nonlinear lower contract, without the old
`N * lambda^2 <= 1` restriction. A proposition below is a specification, not
a proof of the adaptive matching lower bound. The scalar corollary and the
selected-oracle accuracy wrapper are actual checked theorems.
-/

/-- Scalar hypotheses of `app:thm:nonlinear-finite-lower`. -/
structure NonlinearMatchingParameters (N : ℕ) where
  vocabSize : ℕ
  bankSize : ℕ
  triggerMass : ℝ
  edgeCoupling : ℝ
  even_length : Even N
  bank_nonempty : 1 ≤ bankSize
  bank_lt_vocab : bankSize < vocabSize
  bank_mass_lt_one : (bankSize : ℝ) * triggerMass < 1
  coupling_pos : 0 < edgeCoupling
  coupling_le_trigger : edgeCoupling ≤ triggerMass
  trigger_le_half : triggerMass ≤ (1 / 2 : ℝ)

namespace NonlinearMatchingParameters

variable {N : ℕ}

/-- Number of background tokens, which is positive in the finite family. -/
def backgroundSize (P : NonlinearMatchingParameters N) : ℕ :=
  P.vocabSize - P.bankSize

theorem backgroundSize_pos (P : NonlinearMatchingParameters N) :
    0 < P.backgroundSize := Nat.sub_pos_of_lt P.bank_lt_vocab

/-- The current hypotheses imply every hypothesis of the local edge law. -/
def toHardLocal (P : NonlinearMatchingParameters N) :
    HardLocalParameters P.bankSize P.backgroundSize where
  triggerMass := P.triggerMass
  edgeCoupling := P.edgeCoupling
  background_nonempty := P.backgroundSize_pos
  trigger_pos := lt_of_lt_of_le P.coupling_pos P.coupling_le_trigger
  bank_mass_lt_one := P.bank_mass_lt_one
  coupling_pos := P.coupling_pos
  coupling_le_trigger := P.coupling_le_trigger
  trigger_le_half := P.trigger_le_half

theorem hardVocabulary_card (P : NonlinearMatchingParameters N) :
    Fintype.card (HardVocabulary P.bankSize P.backgroundSize) = P.vocabSize := by
  rw [Fintype.card_sum]
  simp only [Fintype.card_fin]
  exact Nat.add_sub_of_le (Nat.le_of_lt P.bank_lt_vocab)

/-- The explicit family already constructed and normalized in `HardMatching`. -/
noncomputable def hardFamily (P : NonlinearMatchingParameters N) :
    HardMatching.InstanceIndex N P.bankSize →
      SamplingInstance N (HardVocabulary P.bankSize P.backgroundSize) :=
  HardMatching.family P.toHardLocal

/-- Current nonlinear value, with the paper's finite numerical constant. -/
noncomputable def lowerValue (P : NonlinearMatchingParameters N) (R : ℕ) : ℝ :=
  (1 / 4 : ℝ) *
    (1 - Real.exp (-((N : ℝ) * P.edgeCoupling ^ 2 / (98304 * (R : ℝ)))))

theorem lowerValue_nonneg (P : NonlinearMatchingParameters N) (R : ℕ) :
    0 ≤ P.lowerValue R := by
  unfold lowerValue
  have hx : 0 ≤ (N : ℝ) * P.edgeCoupling ^ 2 / (98304 * (R : ℝ)) := by
    positivity
  have he : Real.exp (-((N : ℝ) * P.edgeCoupling ^ 2 /
      (98304 * (R : ℝ)))) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  positivity

theorem lowerValue_le_quarter (P : NonlinearMatchingParameters N) (R : ℕ) :
    P.lowerValue R ≤ (1 / 4 : ℝ) := by
  unfold lowerValue
  have := Real.exp_nonneg (-((N : ℝ) * P.edgeCoupling ^ 2 / (98304 * (R : ℝ))))
  linarith

/-- The current substantive lower theorem, still an unproved contract.
The family is explicit; no arbitrary conclusion is hidden in its parameters. -/
def FiniteAdaptiveLowerBound (P : NonlinearMatchingParameters N) : Prop :=
  ∀ Q R : ℕ, Q ≤ P.bankSize / 8 → 1 ≤ R → R ≤ N / 16384 →
    P.lowerValue R ≤ InstanceFamily.minimax P.hardFamily Q R

end NonlinearMatchingParameters

/-- Inverting a small nonlinear loss using the tangent bound for `exp`.
This is the scalar step in `app:cor:nonlinear-finite-target-tradeoff`. -/
theorem nonlinear_exponent_le_eight_mul {x ε : ℝ}
    (hx : 0 ≤ x) (hε : ε ≤ (1 / 8 : ℝ))
    (hloss : (1 / 4 : ℝ) * (1 - Real.exp (-x)) ≤ ε) : x ≤ 8 * ε := by
  have hepos : 0 ≤ Real.exp (-x) := Real.exp_nonneg _
  have htangent := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) hepos
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hcancel] at htangent
  have hscaled := mul_nonneg hx (show 0 ≤ Real.exp (-x) - (1 - 4 * ε) by linarith)
  have hsmall := mul_nonneg hx (show 0 ≤ (1 / 2 : ℝ) - 4 * ε by linarith)
  nlinarith

/-- The target-error alternative conditional only on the substantive lower
estimate. This does not assert that the adaptive lower estimate is proved. -/
theorem nonlinear_target_error_alternative {N : ℕ}
    (P : NonlinearMatchingParameters N) (Q R : ℕ) (risk ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ (1 / 8 : ℝ)) (hR : 1 ≤ R)
    (hrisk : risk ≤ ε)
    (hlower : Q ≤ P.bankSize / 8 → R ≤ N / 16384 → P.lowerValue R ≤ risk) :
    P.bankSize / 8 < Q ∨ N / 16384 < R ∨
      (N : ℝ) * P.edgeCoupling ^ 2 / (786432 * ε) ≤ (R : ℝ) := by
  by_cases hQ : Q ≤ P.bankSize / 8
  · by_cases hRN : R ≤ N / 16384
    · right
      right
      have hRreal : (0 : ℝ) < (R : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
      have hx : 0 ≤ (N : ℝ) * P.edgeCoupling ^ 2 / (98304 * (R : ℝ)) := by
        positivity
      have hbound := nonlinear_exponent_le_eight_mul hx hε1
        ((hlower hQ hRN).trans hrisk)
      have hnum := (div_le_iff₀ (show 0 < (98304 : ℝ) * (R : ℝ) by positivity)).mp hbound
      apply (div_le_iff₀ (show 0 < (786432 : ℝ) * ε by positivity)).mpr
      nlinarith
    · exact Or.inr (Or.inl (Nat.lt_of_not_ge hRN))
  · exact Or.inl (Nat.lt_of_not_ge hQ)

namespace HardMatching

/-- Unconditional selected-oracle accuracy: the exact conditional-row
characterization is now discharged by its existing checked proof. -/
theorem selectedOracle_accurate {N bankSize backgroundSize : ℕ}
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (oracleRadius : ℝ) (hradius0 : 0 ≤ oracleRadius) (hradius1 : oracleRadius ≤ 1)
    (hscale : P.edgeCoupling ^ 2 * P.triggerMass ≤
      oracleRadius ^ 2 / (2 * (N : ℝ))) :
    (selectedOracle P M trigger).Accurate (model P M trigger) oracleRadius := by
  exact selectedOracle_accurate_of_exactRowCharacterization P M trigger
    oracleRadius hradius0 hradius1 hscale (exactRowCharacterization P M trigger)

end HardMatching

end ForestSampling
