import ForestSampling.HardFamilyInclusion

set_option autoImplicit false

namespace ForestSampling

/-- The actual integer bank size in the finite signal-calibrated witness. -/
noncomputable def calibratedBank (signal exponent : ℝ) : ℕ :=
  ⌊signal ^ (-1 / exponent)⌋₊

/-- Finite floor and real-power estimates for the calibrated bank. They
establish the hard-family hypotheses at the actual public signal, rather
than only at the level of asymptotic exponents. -/
theorem calibratedBank_bounds (signal exponent : ℝ)
    (hs0 : 0 < signal) (hs1 : signal < 1) (he : 1 < exponent) :
    1 ≤ calibratedBank signal exponent ∧
    (calibratedBank signal exponent : ℝ) ≤ signal ^ (-1 / exponent) ∧
    (calibratedBank signal exponent : ℝ) * signal < 1 ∧
    signal ≤ (calibratedBank signal exponent : ℝ) ^ (-exponent) := by
  have he0 : 0 < exponent := by linarith
  have hexp : -1 / exponent < 0 := div_neg_of_neg_of_pos (by norm_num) he0
  have hx : 1 ≤ signal ^ (-1 / exponent) :=
    (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hs0 hs1 hexp).le
  have hk : 1 ≤ calibratedBank signal exponent := Nat.le_floor (by simpa using hx)
  have hfloor : (calibratedBank signal exponent : ℝ) ≤ signal ^ (-1 / exponent) :=
    Nat.floor_le (Real.rpow_nonneg hs0.le _)
  have hneg : (-1 : ℝ) < -1 / exponent := by
    apply (lt_div_iff₀ he0).mpr
    linarith
  have hmax : signal ^ (-1 / exponent) < signal⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_lt_rpow_of_exponent_gt hs0 hs1 hneg
  have hmass : (calibratedBank signal exponent : ℝ) * signal < 1 := by
    have hm := mul_lt_mul_of_pos_right (hfloor.trans_lt hmax) hs0
    simpa only [inv_mul_cancel₀ (ne_of_gt hs0)] using hm
  refine ⟨hk, hfloor, hmass, ?_⟩
  have hkr : (0 : ℝ) < calibratedBank signal exponent := by exact_mod_cast hk
  calc
    signal = (signal ^ (-1 / exponent)) ^ (-exponent) := by
      rw [← Real.rpow_mul hs0.le]
      have heq : (-1 / exponent) * (-exponent) = (1 : ℝ) := by field_simp
      rw [heq, Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hkr hfloor (by linarith)

/-- The finite public vocabulary condition places the calibrated bank
strictly inside the given vocabulary. -/
theorem calibratedBank_lt_vocab (V : ℕ) (signal exponent : ℝ)
    (hs0 : 0 < signal) (hs1 : signal < 1) (he : 1 < exponent)
    (hV : 1 < (V : ℝ) * signal) : calibratedBank signal exponent < V := by
  have hk := (calibratedBank_bounds signal exponent hs0 hs1 he).2.2.1
  have hlt : (calibratedBank signal exponent : ℝ) < V :=
    (mul_lt_mul_iff_left₀ hs0).mp (hk.trans hV)
  exact_mod_cast hlt

/-- A fully constructed finite hard-family parameter object at the
signal-calibrated bank size. Its validity fields are the preceding proved
floor/power estimates, not independent calibration assumptions. -/
noncomputable def signalCalibratedParameters (N V : ℕ) (signal exponent : ℝ)
    (hN : Even N) (hs0 : 0 < signal) (hs1 : signal ≤ (1 / 2 : ℝ))
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * signal) :
    NonlinearMatchingParameters N where
  vocabSize := V
  bankSize := calibratedBank signal exponent
  triggerMass := signal
  edgeCoupling := signal
  even_length := hN
  bank_nonempty := (calibratedBank_bounds signal exponent hs0 (by linarith) he).1
  bank_lt_vocab := calibratedBank_lt_vocab V signal exponent hs0 (by linarith) he hV
  bank_mass_lt_one := (calibratedBank_bounds signal exponent hs0 (by linarith) he).2.2.1
  coupling_pos := hs0
  coupling_le_trigger := le_rfl
  trigger_le_half := hs1

/-- The constructed finite witness satisfies the rank-envelope parameter
inequality needed by the concrete hard-family inclusion theorem. -/
theorem signalCalibratedParameters_rank (N V : ℕ) (signal exponent : ℝ)
    (hN : Even N) (hs0 : 0 < signal) (hs1 : signal ≤ (1 / 2 : ℝ))
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * signal) :
    let P := signalCalibratedParameters N V signal exponent hN hs0 hs1 he hV
    P.triggerMass ≤ (P.bankSize : ℝ) ^ (-exponent) :=
  (calibratedBank_bounds signal exponent hs0 (by linarith) he).2.2.2

/-- The cubic signal condition is exactly the A2 inclusion condition for
this concrete witness, for every matching and every private trigger vector. -/
theorem signalCalibratedParameters_oracleAccurate (N V : ℕ) (signal exponent radius : ℝ)
    (hN : Even N) (hs0 : 0 < signal) (hs1 : signal ≤ (1 / 2 : ℝ))
    (he : 1 < exponent) (hV : 1 < (V : ℝ) * signal)
    (hr0 : 0 ≤ radius) (hr1 : radius ≤ 1)
    (hscale : signal ^ 3 ≤ radius ^ 2 / (2 * (N : ℝ))) :
    let P := signalCalibratedParameters N V signal exponent hN hs0 hs1 he hV
    letI : Nonempty (HardVocabulary P.bankSize P.backgroundSize) :=
      ⟨Sum.inr ⟨0, P.backgroundSize_pos⟩⟩
    ∀ I, (P.hardFamily I).oracle.Accurate (P.hardFamily I).model radius := by
  intro P
  let : Nonempty (HardVocabulary P.bankSize P.backgroundSize) :=
    ⟨Sum.inr ⟨0, P.backgroundSize_pos⟩⟩
  intro I
  apply HardMatching.selectedOracle_accurate P.toHardLocal I.1 I.2 radius hr0 hr1
  change signal ^ 2 * signal ≤ _
  convert hscale using 1 <;> ring

end ForestSampling
