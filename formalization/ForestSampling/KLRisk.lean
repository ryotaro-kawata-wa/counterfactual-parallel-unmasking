import ForestSampling.KLOracle
import ForestSampling.ProgramKL

set_option autoImplicit false
open MeasureTheory

namespace ForestSampling
namespace Sampler

variable {N : ℕ} {V Seed : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V]

omit [Nonempty V] in
/-- The complete output law is positive: positive fresh-batch laws and the
proved replay equivalence give a positive mass for every full assignment. -/
theorem outputLaw_strictlyPositive (A : Sampler N V Seed)
    (w : Seed) (O : FrozenOracle N V) : (A.outputLaw w O).StrictlyPositive := by
  change (Program.eval O (A.program w (O.readState (MaskedState.allMask N V)))).StrictlyPositive
  rw [← Program.retainedOutputLaw_ofOracle]
  let p := A.program w (O.readState (MaskedState.allMask N V))
  change ((Program.retainedLaw O (BatchKernel.ofOracle O) p).map
    (Program.retainedOutputEquiv O p)).StrictlyPositive
  exact FinDist.map_strictlyPositive_of_surjective _
    (Program.retainedLaw_strictlyPositive O (BatchKernel.ofOracle O) p)
    (Program.retainedOutputEquiv O p)
    (Program.retainedOutputEquiv O p).surjective

omit [Nonempty V] in
/-- Every fixed-seed forward KL is nonnegative. -/
theorem output_klDivergence_nonneg (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V) :
    0 ≤ FinDist.klDivergence M.target (A.outputLaw w O) :=
  FinDist.klDivergence_nonneg _ _ M.target_positive (A.outputLaw_strictlyPositive w O)

/-- A finite bound valid even when every batch may be dependent. This bound
supplies integrability before the sharper failed-screen estimate is applied. -/
theorem output_klDivergence_le_global (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V)
    {κ : ℝ} (hO : O.ForwardKLAccurate M κ) :
    FinDist.klDivergence M.target (A.outputLaw w O) ≤
      (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) := by
  classical
  have h := A.output_klDivergence_le_reference_failure_mass M w O κ hO.1 hO.2
    (fun _ ↦ True) (by intro path hh; exact (hh True.intro).elim)
  simpa only [FinDist.eventMass_true, mul_one] using h

variable [MeasurableSpace Seed]

/-- Bounded and measurable KL loss is integrable on the seed probability law. -/
theorem integrable_seedKLLoss (A : Sampler N V Seed) (μ : Measure Seed)
    [IsProbabilityMeasure μ] (M : ForestModel N V) (O : FrozenOracle N V)
    {κ : ℝ} (hO : O.ForwardKLAccurate M κ)
    (hmeas : A.KLRiskMeasurableAt μ M O) :
    Integrable (fun w ↦ FinDist.klDivergence M.target (A.outputLaw w O)) μ := by
  refine (integrable_const ((N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V))).mono' hmeas ?_
  exact ae_of_all _ fun w ↦ by
    rw [Real.norm_of_nonneg (A.output_klDivergence_nonneg M w O)]
    exact A.output_klDivergence_le_global M w O hO

/-- The averaged KL bound charges failure under the exact joint reference,
not under the implemented sampler, and averages over seeds only at the end.
The screen construction must still prove factorization on good paths and the
stated mean reference-failure bound. -/
theorem seedKLRisk_le_reference_failure (A : Sampler N V Seed) (μ : Measure Seed)
    [IsProbabilityMeasure μ] (M : ForestModel N V) (O : FrozenOracle N V)
    {κ η : ℝ} (hO : O.ForwardKLAccurate M κ)
    (hmeas : A.KLRiskMeasurableAt μ M O)
    (bad : ∀ w : Seed, Program.RetainedPath O
      (A.program w (O.readState (MaskedState.allMask N V))) → Prop)
    [∀ w, DecidablePred (bad w)]
    (hgood : ∀ w path, ¬ bad w path → Program.PathBatchesFactorize M.target
      M.target_positive O (A.program w (O.readState (MaskedState.allMask N V))) path)
    (hfailMeas : AEStronglyMeasurable
      (fun w ↦ (A.jointReferencePathLaw M w O).eventMass (bad w)) μ)
    (hfailure : (∫ w, (A.jointReferencePathLaw M w O).eventMass (bad w) ∂μ) ≤ η) :
    A.seedKLRisk μ M O ≤ (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * η := by
  let f : Seed → ℝ := fun w ↦ (A.jointReferencePathLaw M w O).eventMass (bad w)
  have hintf : Integrable f μ := by
    refine (integrable_const (1 : ℝ)).mono' hfailMeas ?_
    exact ae_of_all _ fun w ↦ by
      rw [Real.norm_of_nonneg (FinDist.eventMass_nonneg _ _)]
      exact FinDist.eventMass_le_one _ _
  have hintkl := A.integrable_seedKLLoss μ M O hO hmeas
  have hintupper := (integrable_const ((N : ℝ) * κ)).add
    (hintf.const_mul ((N : ℝ) * Real.log (Fintype.card V)))
  have hpoint : ∀ w, FinDist.klDivergence M.target (A.outputLaw w O) ≤
      (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * f w := by
    intro w
    exact A.output_klDivergence_le_reference_failure_mass M w O κ hO.1 hO.2
      (bad w) (hgood w)
  unfold seedKLRisk
  calc
    (∫ w, FinDist.klDivergence M.target (A.outputLaw w O) ∂μ) ≤
        ∫ w, (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * f w ∂μ :=
      integral_mono hintkl hintupper hpoint
    _ = (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * ∫ w, f w ∂μ := by
      rw [integral_add (integrable_const _) (hintf.const_mul _), integral_const_mul]
      simp
      rw [integral_const_mul]
    _ ≤ (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * η := by
      have hc : 0 ≤ (N : ℝ) * Real.log (Fintype.card V) :=
        mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hfailure hc)

end Sampler
end ForestSampling
