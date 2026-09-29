import ForestSampling.MatchingLaplace
import ForestSampling.KLOracle
import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

namespace ForestSampling
namespace FinDist

variable {α : Type*} [Fintype α]

/-- The existing finite real-valued law as a normalized Mathlib PMF. No
resampling or change of weights is involved in this conversion. -/
noncomputable def toPMF (p : FinDist α) : PMF α :=
  PMF.ofFintype (fun a ↦ ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ p.nonneg a), p.sum_mass]
    simp)

@[simp] theorem toPMF_apply (p : FinDist α) (a : α) :
    p.toPMF a = ENNReal.ofReal (p a) := rfl

variable [MeasurableSpace α]

/-- The probability measure induced by precisely the same finite law. -/
noncomputable def toMeasure (p : FinDist α) : Measure α := p.toPMF.toMeasure

instance toMeasure_probability (p : FinDist α) : IsProbabilityMeasure p.toMeasure :=
  inferInstanceAs (IsProbabilityMeasure p.toPMF.toMeasure)

variable [MeasurableSingletonClass α]

/-- Every real-valued statistic of a finite seed is measurable. -/
theorem measurable_toMeasure_statistic (f : α → ℝ) : Measurable f :=
  measurable_of_finite f

/-- A finite seed statistic has exactly its original weighted average as
its integral under the induced probability measure. -/
theorem integral_toMeasure (p : FinDist α) (f : α → ℝ) :
    (∫ a, f a ∂p.toMeasure) = p.expectation f := by
  rw [toMeasure, PMF.integral_eq_sum]
  unfold expectation
  apply Finset.sum_congr rfl
  intro a _
  rw [toPMF_apply, ENNReal.toReal_ofReal (p.nonneg a)]
  rfl

/-- Event probabilities are preserved by the finite-law measure conversion. -/
theorem toMeasure_singleton (p : FinDist α) (a : α) :
    p.toMeasure {a} = ENNReal.ofReal (p a) := by
  exact PMF.toMeasure_apply_singleton p.toPMF a (MeasurableSet.singleton a)

end FinDist

namespace Sampler

variable {N : ℕ} {V Seed : Type*} [Fintype V] [DecidableEq V]
variable [Fintype Seed] [MeasurableSpace Seed] [MeasurableSingletonClass Seed]

/-- The seed-risk definition agrees exactly with finite averaging over the
concrete sampler's chosen seed law. -/
theorem seedRisk_eq_finite_expectation (A : Sampler N V Seed) (p : FinDist Seed)
    (M : ForestModel N V) (O : FrozenOracle N V) :
    A.seedRisk p.toMeasure M O = p.expectation (fun w ↦ FinDist.tv M.target (A.outputLaw w O)) :=
  p.integral_toMeasure _

/-- The forward-KL seed risk uses the same unchanged finite seed weights. -/
theorem seedKLRisk_eq_finite_expectation (A : Sampler N V Seed) (p : FinDist Seed)
    (M : ForestModel N V) (O : FrozenOracle N V) :
    A.seedKLRisk p.toMeasure M O =
      p.expectation (fun w ↦ FinDist.klDivergence M.target (A.outputLaw w O)) :=
  p.integral_toMeasure _

end Sampler
end ForestSampling
