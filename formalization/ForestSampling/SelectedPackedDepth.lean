import ForestSampling.SelectedPackedParameters
import ForestSampling.PackedPathDepth

set_option autoImplicit false

namespace ForestSampling
namespace SelectedPackedSampler

open PackedSampler (ColorBlocks InitialReply initialBanks initialDraft initialMarginal
  manuscriptParameters colorCount coloringRepetitions readoutSize)

variable {N repetitions : ℕ} {V State : Type*} {Color : Type}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]

theorem runScreen_pathScreenStages (policy : Policy N V Color State repetitions) (memory : State) (O : FrozenOracle N V) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : State → (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (screens : ℕ) (hnext : ∀ memory rows, Program.PathScreenStages O (next memory rows) screens) :
    Program.PathScreenStages O (runScreen policy memory h B draft baseline q cutoff ε colors next)
      (screens + 1) := by
  classical
  unfold runScreen
  split
  · exact (hnext _ _).mono O (by omega)
  · exact Program.pathScreenStages_queryBlock _ O _ _ _ screens (fun _ ↦ hnext _ _)

/-- At most one fixed-state query group is charged for each available
screen call, independently of how many commit rounds a path actually uses. -/
theorem loop_pathScreenStages (policy : Policy N V Color State repetitions) (O : FrozenOracle N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (ε : ℝ)
    (phases : ℕ) (blocks : ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions)
    (memory : State) (extra : ℕ) (h : History N V) :
    Program.PathScreenStages O (loop policy B draft baseline q cutoff ε phases blocks memory extra h)
      (phases + 1) := by
  induction phases generalizing memory extra h with
  | zero =>
      rw [loop]
      split
      · exact Program.pathScreenStages_done O _ _
      · apply runScreen_pathScreenStages
        intro memory' rows
        exact CappedController.terminal_pathScreenStages O extra h _
  | succ phases ih =>
      rw [loop]
      split
      · exact Program.pathScreenStages_done O _ _
      · apply runScreen_pathScreenStages
        intro memory' rows
        dsimp only
        split
        · exact (CappedController.terminal_pathScreenStages O extra h _).mono O (Nat.zero_le _)
        · apply CappedController.peelPass_pathScreenStages
          intro extra' h'
          exact ih (fun call ↦ blocks call.succ) memory' extra' h'

/-- The exact printed pathwise depth clause, with the path's actual commit
count, together with a genuine grouped trace of the concrete program. The
initial `1` is precisely the distinguished all-mask preprocessing stage. -/
theorem manuscript_sampler_pathwiseOracleDepth (D L : ℕ) (t ρ η : ℝ)
    (hN : 0 < N) (hL : 0 < L)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N)
    (policy : Policy N V (Fin (colorCount D)) State (coloringRepetitions N D η))
    (initialMemory : InitialReply (N := N) (V := V) → State)
    (blocks : ColorBlocks (N := N) (Color := Fin (colorCount D))
      (ForestIteration.phaseCap N D + 1) (coloringRepetitions N D η))
    (reply : InitialReply (N := N) (V := V)) (O : FrozenOracle N V)
    (path : Program.RetainedPath O ((sampler (manuscriptParameters N V D L t ρ η hN hL hfloor) policy initialMemory).program blocks reply)) :
    ∃ depth, Program.GroupedOracleTrace O
        ((sampler (manuscriptParameters N V D L t ρ η hN hL hfloor) policy initialMemory).program blocks reply) path depth ∧
      1 + depth ≤ 1 + Program.retainedRoundCount O
        ((sampler (manuscriptParameters N V D L t ρ η hN hL hfloor) policy initialMemory).program blocks reply) path +
        (ForestIteration.phaseCap N D + 1) := by
  have hb := loop_pathScreenStages policy O (initialBanks reply t (ρ / Real.sqrt N) hfloor)
    (initialDraft reply) (initialMarginal reply) (readoutSize N L)
    D (ρ / Real.sqrt N) (ForestIteration.phaseCap N D) blocks (initialMemory reply)
    (ForestIteration.hardRoundCap N D - 1) (History.empty N V)
  obtain ⟨depth, htrace, hbound⟩ := hb path
  exact ⟨depth, htrace, by
    simpa only [sampler, manuscriptParameters, Nat.add_assoc] using Nat.add_le_add_left hbound 1⟩


end SelectedPackedSampler
end ForestSampling
