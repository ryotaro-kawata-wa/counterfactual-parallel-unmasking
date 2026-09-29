import ForestSampling.CurrentUpperTheorem

set_option autoImplicit false

namespace ForestSampling
namespace PackedSampler

variable {N : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]

/-- The public auxiliary radius, row budget and reference-failure allocation
used by the paper's output-KL-epsilon corollary. -/
noncomputable def klRadius (ε : ℝ) : ℝ := Real.sqrt (ε / 2)
noncomputable def klRowBudget (N : ℕ) (ε : ℝ) : ℝ := ε / (2 * N)
noncomputable def klFailureBudget (N vocabSize : ℕ) (ε : ℝ) : ℝ :=
  ε / (2 * N * Real.log vocabSize)

/-- Both error contributions equal epsilon/2, and all public accuracy and
failure parameters lie in their declared finite domains. -/
theorem klCalibration (N vocabSize : ℕ) (ε : ℝ) (hN : 10 ≤ N)
    (hV : 2 ≤ vocabSize) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ klRadius ε ∧ klRadius ε ≤ 1 ∧
    klRowBudget N ε = (klRadius ε)^2 / (N : ℝ) ∧
    0 < klFailureBudget N vocabSize ε ∧ klFailureBudget N vocabSize ε < 1 ∧
    (N : ℝ) * klRowBudget N ε +
      (N : ℝ) * Real.log vocabSize * klFailureBudget N vocabSize ε = ε := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hVr : (2 : ℝ) ≤ vocabSize := by exact_mod_cast hV
  have hvp : (0 : ℝ) < vocabSize := by linarith
  have hl : (1/2 : ℝ) ≤ Real.log vocabSize := by
    have hh := Real.one_sub_inv_le_log_of_pos hvp
    have hi : (vocabSize : ℝ)⁻¹ ≤ 1/2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hVr
    linarith
  have hlp : 0 < Real.log vocabSize := by linarith
  refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (by linarith), ?_, ?_, ?_, ?_⟩
  · unfold klRowBudget klRadius
    rw [Real.sq_sqrt (by positivity)]
    ring
  · unfold klFailureBudget
    positivity
  · unfold klFailureBudget
    apply (div_lt_one (by positivity)).mpr
    have hn10 : (10 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  · unfold klRowBudget klFailureBudget
    field_simp
    ring

/-- The actual capped sampler achieves output KL at most epsilon with the
paper's linear per-row KL budget. All graph/screen assumptions are the
original finite setup at the calibrated public radius. -/
theorem manuscript_kl_target_error (M : ForestModel N V) (O : FrozenOracle N V)
    (D L : ℕ) (t C s ν signal ε : ℝ)
    (hN : 10 ≤ N) (hV : 2 ≤ Fintype.card V) (hD : 9 ≤ D) (hL : 0 < L)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - klRadius ε / Real.sqrt N)
    (hν : 0 ≤ ν) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * t ^ s) ≤ ν)
    (hmargin : 4 * (klRadius ε / Real.sqrt N) + ν < signal)
    (hO : O.ForwardKLAccurate M (klRowBudget N ε)) :
    let P := manuscriptParameters N V D L t (klRadius ε)
      (klFailureBudget N (Fintype.card V) ε) (by omega) hL hfloor
    (sampler (Color := Fin (colorCount D)) P).seedKLRisk
      (seedLaw (Color := Fin (colorCount D)) P).toMeasure M O ≤ ε := by
  obtain ⟨hr0, hr1, hrow, hη, _, htotal⟩ := klCalibration N (Fintype.card V) ε hN hV hε hε1
  have hh := manuscript_finite_kl_upper M O D L t C s ν signal (klRadius ε)
    (klRowBudget N ε) (klFailureBudget N (Fintype.card V) ε)
    (by omega) hD hL hfloor hν ht0 ht1 hRT hUEN hfeasible hmargin hη hr0 hr1 hO hrow.le
  exact hh.1.trans_eq htotal

/-- Splitting the Hellinger/TV budget equally between row error and screen
failure gives output TV at most the requested epsilon. -/
theorem manuscript_tv_target_error (M : ForestModel N V) (O : FrozenOracle N V)
    (D L : ℕ) (t C s ν signal ε : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D) (hL : 0 < L) (hε : 0 < ε)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - (ε / 2) / Real.sqrt N)
    (hν : 0 ≤ ν) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * t ^ s) ≤ ν)
    (hmargin : 4 * ((ε / 2) / Real.sqrt N) + ν < signal)
    (hO : O.Accurate M (ε / 2)) :
    let P := manuscriptParameters N V D L t (ε / 2) (ε / 2) hN hL hfloor
    (sampler (Color := Fin (colorCount D)) P).seedRisk
      (seedLaw (Color := Fin (colorCount D)) P).toMeasure M O ≤ ε := by
  have hh := (manuscript_finite_hellinger_upper M O D L t C s ν signal (ε/2) (ε/2)
    hN hD hL hfloor hν ht0 ht1 hRT hUEN hfeasible hmargin (by positivity) hO).1
  linarith

end PackedSampler
end ForestSampling
