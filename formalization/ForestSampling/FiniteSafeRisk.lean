import ForestSampling.PrefixSafeRepair
import ForestSampling.FiniteMeasure
import ForestSampling.KLRisk

set_option autoImplicit false
open MeasureTheory

namespace ForestSampling
namespace Sampler

variable {N : ℕ} {V Seed : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V]
variable [Fintype Seed] [MeasurableSpace Seed] [MeasurableSingletonClass Seed]

/-- Replace first-failure markers by concrete safe completions. This
analytic sampler retains the original finite controller seed exactly. -/
noncomputable def safeRepairedSampler (A : Sampler N V Seed) (O : FrozenOracle N V)
    (marker : ∀ w : Seed, Program.PrefixRepair
      (A.program w (O.readState (MaskedState.allMask N V)))
      (A.program w (O.readState (MaskedState.allMask N V)))) : Sampler N V Seed where
  program w _ := (marker w).repaired

/-- A finite sampler's actual pre-failure safety and averaged first-failure
probability imply the manuscript's TV seed-risk guarantee. Measurability is
proved from finiteness, and the replacement controller is constructed. -/
theorem finite_seedRisk_le_of_safeBeforeStop (A : Sampler N V Seed)
    (seedLaw : FinDist Seed) (M : ForestModel N V) (O : FrozenOracle N V)
    (ρ η : ℝ) (hN : 0 < N) (hO : O.Accurate M ρ)
    (marker : ∀ w : Seed, Program.PrefixRepair
      (A.program w (O.readState (MaskedState.allMask N V)))
      (A.program w (O.readState (MaskedState.allMask N V))))
    (hsafe : ∀ w, (marker w).SafeBeforeStop M O)
    (hfailure : seedLaw.expectation (fun w ↦
      (marker w).failureMassWith O (BatchKernel.ofOracle O)) ≤ η) :
    A.seedRisk seedLaw.toMeasure M O ≤ ρ + η := by
  let B := A.safeRepairedSampler O marker
  have hB : ∀ w, FinDist.tv M.target (B.outputLaw w O) ≤ ρ := by
    intro w
    exact B.output_tv_le_of_structurallySafe M w O ρ hN hO
      ((marker w).repaired_safe M O (hsafe w))
  have hmean : (∫ w, (marker w).replacement.failureMass O ∂seedLaw.toMeasure) ≤ η := by
    rw [seedLaw.integral_toMeasure]
    calc
      _ = seedLaw.expectation (fun w ↦
          (marker w).failureMassWith O (BatchKernel.ofOracle O)) := by
        apply congrArg seedLaw.expectation
        funext w
        rw [← Program.PrefixRepair.failureMassWith_ofOracle,
          Program.PrefixRepair.replacement_failureMassWith]
      _ ≤ η := hfailure
  exact A.seedRisk_le_of_prefix_repair B seedLaw.toMeasure M O ρ η
    (fun w ↦ (marker w).replacement) hB
    ((measurable_of_finite _).aestronglyMeasurable)
    ((measurable_of_finite _).aestronglyMeasurable) hmean

/-- The forward-KL guarantee charges the very same marker under actual
joint target commits. Pre-failure structural safety supplies factorization
on good paths; the finite seed law supplies all required measurability. -/
theorem finite_seedKLRisk_le_of_safeBeforeStop (A : Sampler N V Seed)
    (seedLaw : FinDist Seed) (M : ForestModel N V) (O : FrozenOracle N V)
    (κ η : ℝ) (hO : O.ForwardKLAccurate M κ)
    (marker : ∀ w : Seed, Program.PrefixRepair
      (A.program w (O.readState (MaskedState.allMask N V)))
      (A.program w (O.readState (MaskedState.allMask N V))))
    (hsafe : ∀ w, (marker w).SafeBeforeStop M O)
    (hfailure : seedLaw.expectation (fun w ↦
      (marker w).failureMassWith O (BatchKernel.ofTarget M.target M.target_positive)) ≤ η) :
    A.seedKLRisk seedLaw.toMeasure M O ≤
      (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * η := by
  classical
  apply A.seedKLRisk_le_reference_failure seedLaw.toMeasure M O hO
    ((measurable_of_finite _).aestronglyMeasurable)
    (fun w ↦ (marker w).HitsRepair O)
    (fun w path hgood ↦ (marker w).pathBatchesFactorize_of_safeBeforeStop M O
      (hsafe w) path hgood)
    ((measurable_of_finite _).aestronglyMeasurable)
  rw [seedLaw.integral_toMeasure]
  calc
    _ = seedLaw.expectation (fun w ↦
        (marker w).failureMassWith O (BatchKernel.ofTarget M.target M.target_positive)) := by
      apply congrArg seedLaw.expectation
      funext w
      exact ((marker w).failureMassWith_eq_event O
        (BatchKernel.ofTarget M.target M.target_positive)).symm
    _ ≤ η := hfailure

end Sampler
end ForestSampling
