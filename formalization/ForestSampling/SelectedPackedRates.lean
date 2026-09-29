import ForestSampling.SelectedPackedParameters
import ForestSampling.UpperRates

set_option autoImplicit false

namespace ForestSampling.SelectedPackedSampler

variable {N : ℕ} {V State : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]

/-- The exact query-count expression used in the controller-independent
rate lemmas bounds every actual execution of each public-memory policy. -/
theorem program_within_queryCount (O : FrozenOracle N V) (D : ℕ)
    (t ρ η : ℝ) (hN : 0 < N) (hD : 0 < D)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N)
    (policy : Policy N V (Fin (PackedSampler.colorCount D)) State
      (PackedSampler.coloringRepetitions N D η))
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State)
    (blocks : PackedSampler.ColorBlocks (N := N) (Color := Fin (PackedSampler.colorCount D))
      (ForestIteration.phaseCap N D + 1) (PackedSampler.coloringRepetitions N D η)) :
    Program.WithinBudgets
      ((sampler (PackedSampler.manuscriptParameters N V D D t ρ η hN hD hfloor)
        policy initialMemory).program blocks (O.readState (MaskedState.allMask N V)))
      (UpperRates.queryCount N D D (PackedSampler.screenColumns
        (Screening.Banks.ofOracle O t (ρ / Real.sqrt N) hfloor)) η)
      (ForestIteration.hardRoundCap N D) := by
  simpa only [UpperRates.queryCount, PackedSampler.initialBanks_oracle] using
    manuscript_program_withinBudgets D D t ρ η hN hD hfloor policy initialMemory blocks
      (O.readState (MaskedState.allMask N V))

/-- Actual RF and row accuracy bound the chosen-policy execution's exact
query allowance at the actual dyadic benchmark threshold. No bank power
bound or selector-independence event is supplied as a hypothesis. -/
theorem program_benchmark_rate_envelopes (M : ForestModel N V) (O : FrozenOracle N V)
    (ranking : MarginalRanking M) (D : ℕ) (ζ ρ signal η : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D) (hDN : D ≤ N) (hζ : 0 < ζ)
    (hRF : FiniteRankFrequency M ranking ζ 1) (hO : O.Accurate M ρ)
    (hs : 0 < signal) (hs1 : signal ≤ (1 / 2 : ℝ))
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hmargin : 16 * max (ρ / Real.sqrt N) (Fintype.card V : ℝ)⁻¹ ≤ signal)
    (hf : (ThresholdGrid.feasible
      (UpperRates.benchmarkFloor (Fintype.card V) (ρ / Real.sqrt N)) 1 1 (signal / 2)).Nonempty)
    (hcomplement : (Fintype.card V : ℝ)⁻¹ <
      ThresholdGrid.selected (UpperRates.benchmarkFloor (Fintype.card V) (ρ / Real.sqrt N))
        1 1 (signal / 2) hf - ρ / Real.sqrt N) :
    let t := ThresholdGrid.selected
      (UpperRates.benchmarkFloor (Fintype.card V) (ρ / Real.sqrt N)) 1 1 (signal / 2) hf
    let P := PackedSampler.manuscriptParameters N V D D t ρ η hN (by omega) hcomplement
    let Q := UpperRates.queryCount N D D
      (PackedSampler.screenColumns (Screening.Banks.ofOracle O t (ρ / Real.sqrt N) hcomplement)) η
    ∀ (policy : Policy N V (Fin (PackedSampler.colorCount D)) State P.repetitions)
      (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State),
      (∀ blocks, Program.WithinBudgets
        ((sampler P policy initialMemory).program blocks (O.readState (MaskedState.allMask N V)))
        Q (ForestIteration.hardRoundCap N D)) ∧
      (Q : ℝ) ≤ 272 * ((16 / signal) ^ (1 / ζ) + 1) * UpperRates.screenEnvelope N *
        UpperRates.repetitionEnvelope N η * (D : ℝ)^2 ∧
      (ForestIteration.hardRoundCap N D : ℝ) ≤
        (N : ℝ) / D * UpperRates.roundEnvelope N := by
  intro t P Q policy initialMemory
  refine ⟨fun blocks ↦ program_within_queryCount O D t ρ η hN (by omega)
    hcomplement policy initialMemory blocks, ?_, ?_⟩
  · exact UpperRates.benchmark_queryCount_le M O ranking ζ (ρ / Real.sqrt N) signal η D
      hN hD hζ hRF hs hs1 hη hη1 hmargin hf hcomplement (fun y j ↦ hO.tv_bound hN y j)
  · exact UpperRates.hardRoundCap_le_envelope N D hN hD hDN

end ForestSampling.SelectedPackedSampler
