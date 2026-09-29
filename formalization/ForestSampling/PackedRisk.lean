import ForestSampling.FiniteSafeRisk
import ForestSampling.PackedFailure

set_option autoImplicit false
open MeasureTheory

namespace ForestSampling
namespace PackedSampler

variable {N : ℕ} {V Color : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color] [Nonempty Color]
variable [MeasurableSpace Color] [MeasurableSingletonClass Color]

/-- The actual packed sampler's finite seed law yields TV risk at most
rho+eta once the concrete successful-prefix safety invariant is supplied.
Adaptive reached-screen probability and the repaired controller are proved. -/
theorem sampler_seedRisk_le_of_safeBeforeStop (P : Parameters N V)
    (M : ForestModel N V) (O : FrozenOracle N V) (ρ η : ℝ)
    (hN : 0 < N) (hη : 0 < η) (hO : O.Accurate M ρ)
    (hcolors : 8 * (P.cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((P.phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (P.repetitions : ℝ))
    (hsafe : ∀ blocks, (samplerMarker (Color := Color) P M O blocks).SafeBeforeStop M O) :
    (sampler (Color := Color) P).seedRisk (seedLaw (Color := Color) P).toMeasure M O ≤ ρ + η := by
  apply Sampler.finite_seedRisk_le_of_safeBeforeStop (sampler (Color := Color) P)
    (seedLaw (Color := Color) P) M O ρ η hN hO
    (samplerMarker P M O) hsafe
  exact sampler_mean_failure_le P M O (BatchKernel.ofOracle O) η hN hη hcolors hT

/-- The same actual sampler and seed law give the forward-KL guarantee,
charging failed screens under exact joint target commits. Only the concrete
successful-prefix structural invariant remains as input. -/
theorem sampler_seedKLRisk_le_of_safeBeforeStop (P : Parameters N V)
    (M : ForestModel N V) (O : FrozenOracle N V) (κ η : ℝ)
    (hN : 0 < N) (hη : 0 < η) (hO : O.ForwardKLAccurate M κ)
    (hcolors : 8 * (P.cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((P.phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (P.repetitions : ℝ))
    (hsafe : ∀ blocks, (samplerMarker (Color := Color) P M O blocks).SafeBeforeStop M O) :
    (sampler (Color := Color) P).seedKLRisk (seedLaw (Color := Color) P).toMeasure M O ≤
      (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * η := by
  apply Sampler.finite_seedKLRisk_le_of_safeBeforeStop (sampler (Color := Color) P)
    (seedLaw (Color := Color) P) M O κ η hO (samplerMarker P M O) hsafe
  exact sampler_mean_failure_le P M O (BatchKernel.ofTarget M.target M.target_positive)
    η hN hη hcolors hT

end PackedSampler
end ForestSampling
