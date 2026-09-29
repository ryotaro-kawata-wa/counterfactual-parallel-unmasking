import ForestSampling.SelectedPackedStructure
import ForestSampling.FiniteSafeRisk
import ForestSampling.SelectedPackedParameters

set_option autoImplicit false
open MeasureTheory

namespace ForestSampling.SelectedPackedSampler

variable {N : ℕ} {V Color State : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color] [Nonempty Color]
variable [MeasurableSpace Color] [MeasurableSingletonClass Color]

open PackedSampler (Parameters seedLaw manuscriptParameters initialBanks
  screenColumns colorCount coloringRepetitions coloringRepetitions_spec)

/-- The actual packed sampler's finite seed law yields TV risk at most
rho+eta once the concrete successful-prefix safety invariant is supplied.
Adaptive reached-screen probability and the repaired controller are proved. -/
theorem sampler_seedRisk_le_of_safeBeforeStop (P : Parameters N V)
    (policy : Policy N V Color State P.repetitions)
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State)
    (M : ForestModel N V) (O : FrozenOracle N V) (ρ η : ℝ)
    (hN : 0 < N) (hη : 0 < η) (hO : O.Accurate M ρ)
    (hcolors : 8 * (P.cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((P.phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (P.repetitions : ℝ))
    (hsafe : ∀ blocks, (samplerMarker P policy initialMemory M O blocks).SafeBeforeStop M O) :
    (sampler P policy initialMemory).seedRisk (seedLaw (Color := Color) P).toMeasure M O ≤ ρ + η := by
  apply Sampler.finite_seedRisk_le_of_safeBeforeStop (sampler P policy initialMemory)
    (seedLaw (Color := Color) P) M O ρ η hN hO
    (samplerMarker P policy initialMemory M O) hsafe
  exact sampler_mean_failure_le P policy initialMemory M O (BatchKernel.ofOracle O) η hN hη hcolors hT

/-- The same actual sampler and seed law give the forward-KL guarantee,
charging failed screens under exact joint target commits. Only the concrete
successful-prefix structural invariant remains as input. -/
theorem sampler_seedKLRisk_le_of_safeBeforeStop (P : Parameters N V)
    (policy : Policy N V Color State P.repetitions)
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State)
    (M : ForestModel N V) (O : FrozenOracle N V) (κ η : ℝ)
    (hN : 0 < N) (hη : 0 < η) (hO : O.ForwardKLAccurate M κ)
    (hcolors : 8 * (P.cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((P.phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (P.repetitions : ℝ))
    (hsafe : ∀ blocks, (samplerMarker P policy initialMemory M O blocks).SafeBeforeStop M O) :
    (sampler P policy initialMemory).seedKLRisk (seedLaw (Color := Color) P).toMeasure M O ≤
      (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * η := by
  apply Sampler.finite_seedKLRisk_le_of_safeBeforeStop (sampler P policy initialMemory)
    (seedLaw (Color := Color) P) M O κ η hO (samplerMarker P policy initialMemory M O) hsafe
  exact sampler_mean_failure_le P policy initialMemory M O (BatchKernel.ofTarget M.target M.target_positive)
    η hN hη hcolors hT

/-- The concrete finite Hellinger-to-TV guarantee. Actual caps, independent
colors, reached-call probabilities, successful-prefix safety, singleton
repair, and seed integration are all proved rather than assumed. -/
theorem sampler_seedRisk_le (P : Parameters N V)
    (policy : Policy N V Color State P.repetitions)
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State) (M : ForestModel N V)
    (O : FrozenOracle N V) (C s ν signal ρ η : ℝ)
    (hN : 0 < N) (hD : 9 ≤ P.cutoff)
    (hphases : P.phases = ForestIteration.phaseCap N P.cutoff)
    (hextra : P.extraRounds = ForestIteration.hardRoundCap N P.cutoff - 1)
    (hrowError : P.rowError = ρ / Real.sqrt N)
    (hν : 0 ≤ ν) (ht0 : 0 ≤ P.threshold) (ht1 : P.threshold ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * P.threshold ^ s) ≤ ν)
    (hmargin : 4 * P.rowError + ν < signal)
    (hη : 0 < η) (hO : O.Accurate M ρ)
    (hcolors : 8 * (P.cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((P.phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (P.repetitions : ℝ)) :
    (sampler P policy initialMemory).seedRisk (seedLaw (Color := Color) P).toMeasure M O ≤ ρ + η := by
  apply sampler_seedRisk_le_of_safeBeforeStop P policy initialMemory M O ρ η hN hη hO hcolors hT
  apply samplerMarker_safeBeforeStop P policy initialMemory M O C s ν signal
    hN hD hphases hextra
  · rw [hrowError]
    exact div_nonneg hO.1 (Real.sqrt_nonneg _)
  · exact hν
  · exact ht0
  · exact ht1
  · exact hRT
  · exact hUEN
  · exact hfeasible
  · exact hmargin
  · intro y j
    rw [hrowError]
    exact hO.tv_bound hN y j

/-- The concrete forward-KL upper bound uses the same actual controller and
seed law. Calibrated forward-KL accuracy supplies the row-screen hypotheses;
the final KL estimate is charged under true joint-reference paths. -/
theorem sampler_seedKLRisk_le (P : Parameters N V)
    (policy : Policy N V Color State P.repetitions)
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State) (M : ForestModel N V)
    (O : FrozenOracle N V) (C s ν signal ρ κ η : ℝ)
    (hN : 0 < N) (hD : 9 ≤ P.cutoff)
    (hphases : P.phases = ForestIteration.phaseCap N P.cutoff)
    (hextra : P.extraRounds = ForestIteration.hardRoundCap N P.cutoff - 1)
    (hrowError : P.rowError = ρ / Real.sqrt N)
    (hν : 0 ≤ ν) (ht0 : 0 ≤ P.threshold) (ht1 : P.threshold ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * P.threshold ^ s) ≤ ν)
    (hmargin : 4 * P.rowError + ν < signal)
    (hη : 0 < η) (hr0 : 0 ≤ ρ) (hr1 : ρ ≤ 1)
    (hO : O.ForwardKLAccurate M κ) (hκ : κ ≤ ρ^2/(N : ℝ))
    (hcolors : 8 * (P.cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((P.phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (P.repetitions : ℝ)) :
    (sampler P policy initialMemory).seedKLRisk (seedLaw (Color := Color) P).toMeasure M O ≤
      (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * η := by
  have hAcc := hO.accurate hr0 hr1 hκ
  apply sampler_seedKLRisk_le_of_safeBeforeStop P policy initialMemory M O κ η hN hη hO hcolors hT
  apply samplerMarker_safeBeforeStop P policy initialMemory M O C s ν signal
    hN hD hphases hextra
  · rw [hrowError]
    positivity
  · exact hν
  · exact ht0
  · exact ht1
  · exact hRT
  · exact hUEN
  · exact hfeasible
  · exact hmargin
  · intro y j
    rw [hrowError]
    exact hAcc.tv_bound hN y j


/-- The finite TV theorem with the exact public manuscript formulas for
colors, repetitions, phases, chunk size and rounds. The query factor uses
actual preprocessing banks and includes the zero-column case. -/
theorem manuscript_finite_hellinger_upper (M : ForestModel N V) (O : FrozenOracle N V)
    (D L : ℕ) (t C s ν signal ρ η : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D) (hL : 0 < L)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N)
    (hν : 0 ≤ ν) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * t ^ s) ≤ ν)
    (hmargin : 4 * (ρ / Real.sqrt N) + ν < signal)
    (hη : 0 < η) (hO : O.Accurate M ρ) :
    let P := manuscriptParameters N V D L t ρ η hN hL hfloor
    ∀ (policy : Policy N V (Fin (colorCount D)) State P.repetitions)
      (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State),
    (sampler P policy initialMemory).seedRisk
      (seedLaw (Color := Fin (colorCount D)) P).toMeasure M O ≤ ρ + η ∧
    ∀ blocks, Program.WithinBudgets
      ((sampler P policy initialMemory).program blocks
        (O.readState (MaskedState.allMask N V)))
      (screenColumns (initialBanks (O.readState (MaskedState.allMask N V))
          t (ρ / Real.sqrt N) hfloor) *
        (ForestIteration.phaseCap N D + 1) * coloringRepetitions N D η * colorCount D *
        (colorCount D + L)) (ForestIteration.hardRoundCap N D) := by
  dsimp only
  intro policy initialMemory
  constructor
  · apply sampler_seedRisk_le _ policy initialMemory M O C s ν signal ρ η hN hD rfl rfl rfl
      hν ht0 ht1 hRT hUEN hfeasible hmargin hη hO
    · change 8 * (D + 1) ≤ Fintype.card (Fin (colorCount D))
      rw [Fintype.card_fin]
      exact le_rfl
    · exact coloringRepetitions_spec N D η
  · intro blocks
    exact manuscript_program_withinBudgets D L t ρ η hN hL hfloor policy initialMemory blocks _

/-- The finite forward-KL theorem retains the same concrete public
controller and the same all-path query and round budgets. -/
theorem manuscript_finite_kl_upper (M : ForestModel N V) (O : FrozenOracle N V)
    (D L : ℕ) (t C s ν signal ρ κ η : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D) (hL : 0 < L)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N)
    (hν : 0 ≤ ν) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * t ^ s) ≤ ν)
    (hmargin : 4 * (ρ / Real.sqrt N) + ν < signal)
    (hη : 0 < η) (hr0 : 0 ≤ ρ) (hr1 : ρ ≤ 1)
    (hO : O.ForwardKLAccurate M κ) (hκ : κ ≤ ρ^2/(N : ℝ)) :
    let P := manuscriptParameters N V D L t ρ η hN hL hfloor
    ∀ (policy : Policy N V (Fin (colorCount D)) State P.repetitions)
      (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State),
    (sampler P policy initialMemory).seedKLRisk
      (seedLaw (Color := Fin (colorCount D)) P).toMeasure M O ≤
      (N : ℝ) * κ + (N : ℝ) * Real.log (Fintype.card V) * η ∧
    ∀ blocks, Program.WithinBudgets
      ((sampler P policy initialMemory).program blocks
        (O.readState (MaskedState.allMask N V)))
      (screenColumns (initialBanks (O.readState (MaskedState.allMask N V))
          t (ρ / Real.sqrt N) hfloor) *
        (ForestIteration.phaseCap N D + 1) * coloringRepetitions N D η * colorCount D *
        (colorCount D + L)) (ForestIteration.hardRoundCap N D) := by
  dsimp only
  intro policy initialMemory
  constructor
  · apply sampler_seedKLRisk_le _ policy initialMemory M O C s ν signal ρ κ η hN hD rfl rfl rfl
      hν ht0 ht1 hRT hUEN hfeasible hmargin hη hr0 hr1 hO hκ
    · change 8 * (D + 1) ≤ Fintype.card (Fin (colorCount D))
      rw [Fintype.card_fin]
      exact le_rfl
    · exact coloringRepetitions_spec N D η
  · intro blocks
    exact manuscript_program_withinBudgets D L t ρ η hN hL hfloor policy initialMemory blocks _


end ForestSampling.SelectedPackedSampler
