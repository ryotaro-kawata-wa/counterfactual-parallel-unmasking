import ForestSampling.CurrentUpperTheorem

set_option autoImplicit false

namespace ForestSampling
namespace PackedSampler

variable {N : ℕ} {V Color : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color] [Nonempty Color]

/-- The actual packed sampler admits the paper's analysis-only safe rule.
Its fixed-seed error is at most rho, and its mean TV distance from the
implemented rule is at most eta. The safe rule is explicitly constructed. -/
theorem safe_controller_comparison (P : Parameters N V) (M : ForestModel N V)
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
    ∃ B : Sampler N V (ColorBlocks (N := N) (Color := Color) (P.phases + 1) P.repetitions),
      (∀ w, Program.StructurallySafe M O (B.program w (O.readState (MaskedState.allMask N V)))) ∧
      (∀ w, FinDist.tv M.target (B.outputLaw w O) ≤ ρ) ∧
      (seedLaw (Color := Color) P).expectation (fun w ↦
        FinDist.tv ((sampler (Color := Color) P).outputLaw w O) (B.outputLaw w O)) ≤ η := by
  classical
  let A := sampler (Color := Color) P
  let marker := samplerMarker (Color := Color) P M O
  let B : Sampler N V (ColorBlocks (N := N) (Color := Color) (P.phases + 1) P.repetitions) :=
    { program := fun w _ ↦ (marker w).repaired }
  have hsafe : ∀ w, (marker w).SafeBeforeStop M O := by
    apply PackedLoopStructure.samplerMarker_safeBeforeStop P M O C s ν signal
      hN hD hphases hextra
    · rw [hrowError]; exact div_nonneg hO.1 (Real.sqrt_nonneg _)
    · exact hν
    · exact ht0
    · exact ht1
    · exact hRT
    · exact hUEN
    · exact hfeasible
    · exact hmargin
    · intro y j; rw [hrowError]; exact hO.tv_bound hN y j
  have hB : ∀ w, Program.StructurallySafe M O (B.program w (O.readState (MaskedState.allMask N V))) :=
    fun w ↦ (marker w).repaired_safe M O (hsafe w)
  refine ⟨B, hB, fun w ↦ B.output_tv_le_of_structurallySafe M w O ρ hN hO (hB w), ?_⟩
  calc
    _ ≤ (seedLaw (Color := Color) P).expectation (fun w ↦ (marker w).replacement.failureMass O) :=
      FinDist.expectation_mono _ (fun w ↦ (marker w).replacement.tv_eval_le_failureMass O)
    _ = (seedLaw (Color := Color) P).expectation
        (fun w ↦ (marker w).failureMassWith O (BatchKernel.ofOracle O)) := by
      apply congrArg (seedLaw (Color := Color) P).expectation
      funext w
      rw [← Program.PrefixRepair.failureMassWith_ofOracle,
        Program.PrefixRepair.replacement_failureMassWith]
    _ ≤ η := sampler_mean_failure_le P M O (BatchKernel.ofOracle O) η hN hη hcolors hT

end PackedSampler
end ForestSampling
