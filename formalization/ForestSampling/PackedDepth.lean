import ForestSampling.PackedParameters

set_option autoImplicit false

namespace ForestSampling
namespace Program

universe u
variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- An adaptive oracle-depth witness for an actual program. A query block
is allowed only when its entire list of submitted states is fixed before
any reply, as witnessed by `runQuerySchedule`; commit calls each use one
stage. Thus this quantity is distinct from individual submission count. -/
inductive GroupedOracleDepth : {h : History N V} → Program N V h → ℕ → Prop
  | done {h : History N V} (complete : h.committed = Finset.univ) (depth : ℕ) :
      GroupedOracleDepth (.done complete) depth
  | queryBlock {h : History N V} {Index : Type} [DecidableEq Index]
      (queries : Index → Submission h) (todo : List Index) (replies : ReplyTable queries)
      (next : ReplyTable queries → Program N V h) (depth : ℕ)
      (following : ∀ table, GroupedOracleDepth (next table) depth) :
      GroupedOracleDepth (runQuerySchedule queries todo replies next) (depth + 1)
  | commit {h : History N V} (batch : Finset (Position N)) (nonempty : batch.Nonempty)
      (fresh : batch ⊆ h.uncommitted)
      (next : (z : batch → V) → Program N V (h.appendBatch batch fresh z)) (depth : ℕ)
      (following : ∀ z, GroupedOracleDepth (next z) depth) :
      GroupedOracleDepth (.commit batch nonempty fresh next) (depth + 1)
  | mono {h : History N V} {p : Program N V h} {a b : ℕ}
      (witness : GroupedOracleDepth p a) (le : a ≤ b) : GroupedOracleDepth p b

theorem commitAll_groupedDepth (h : History N V) : GroupedOracleDepth (commitAll h) 1 := by
  unfold commitAll
  split
  · exact .done _ _
  · exact .commit _ _ _ _ 0 (fun _ ↦ .done _ _)

end Program

namespace CappedController

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Every terminal-controller commit uses one oracle stage, including the
reserved fallback, regardless of whether its public graph is correct. -/
theorem terminal_groupedDepth (extra : ℕ) (h : History N V) (G : SimpleGraph (Position N)) :
    Program.GroupedOracleDepth (terminal extra h G) (extra + 1) := by
  induction extra generalizing h with
  | zero =>
      unfold terminal
      split
      · exact .done _ _
      · exact Program.commitAll_groupedDepth h
  | succ extra ih =>
      unfold terminal
      split
      · exact .done _ _
      · exact .commit _ _ _ _ (extra + 1) (fun _ ↦ ih _)

/-- A frozen peel pass adds only its singleton commit stages. Its remaining
fuel bounds those stages uniformly, even if it invokes the hard guard. -/
theorem peelPass_groupedDepth (todo : List (Position N)) (extra : ℕ) (h : History N V)
    (after : (extra : ℕ) → (h : History N V) → Program N V h) (screens : ℕ)
    (hafter : ∀ extra h, Program.GroupedOracleDepth (after extra h) (screens + (extra + 1))) :
    Program.GroupedOracleDepth (peelPass todo extra h after) (screens + (extra + 1)) := by
  induction todo generalizing extra h with
  | nil => exact hafter extra h
  | cons j todo ih =>
      rw [peelPass]
      split
      · exact .done _ _
      · split
        · cases extra with
          | zero => exact (Program.commitAll_groupedDepth h).mono (by omega)
          | succ extra =>
              have hh := Program.GroupedOracleDepth.commit {j} (Finset.singleton_nonempty j)
                (by simpa using ‹j ∈ h.uncommitted›) _ (screens + (extra + 1))
                (fun z ↦ ih extra (h.appendBatch {j} (by simpa using ‹j ∈ h.uncommitted›) z))
              convert hh using 1; omega
        · exact ih extra h

end CappedController

namespace PackedSampler

variable {N : ℕ} {V : Type*} {Color : Type}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]

omit [Nonempty V] in
/-- Every actual screen schedule fits one parallel query group: its states
and enumeration depend only on the current history, draft, and color block. -/
theorem runStandardScreen_groupedDepth (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q cutoff : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (depth : ℕ) (hnext : ∀ rows, Program.GroupedOracleDepth (next rows) depth) :
    Program.GroupedOracleDepth (runStandardScreen h B draft baseline repetitions q cutoff ε colors next)
      (depth + 1) := by
  classical
  unfold runStandardScreen Screening.runScreen
  split
  · exact (hnext _).mono (by omega)
  · exact .queryBlock _ _ _ _ depth (fun _ ↦ hnext _)

omit [Nonempty V] in
/-- The actual capped loop has at most one parallel screen stage per
available call plus its hard bound on mandatory commit stages. -/
theorem loop_groupedDepth (B : Screening.Banks (N := N) (V := V))
    (draft : Position N → V) (baseline : Position N → FinDist V)
    (repetitions q cutoff : ℕ) (ε : ℝ)
    (phases : ℕ) (blocks : ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions)
    (extra : ℕ) (h : History N V) :
    Program.GroupedOracleDepth (loop B draft baseline repetitions q cutoff ε phases blocks extra h)
      ((phases + 1) + (extra + 1)) := by
  induction phases generalizing extra h with
  | zero =>
      rw [loop]
      split
      · exact .done _ _
      · have hh := runStandardScreen_groupedDepth h B draft baseline repetitions q cutoff ε
          (blocks ⟨0, by omega⟩) _ (extra + 1)
          (fun rows ↦ CappedController.terminal_groupedDepth extra h (CappedController.rowGraph h rows))
        convert hh using 1; omega
  | succ phases ih =>
      rw [loop]
      split
      · exact .done _ _
      · refine Program.GroupedOracleDepth.mono
          (a := ((phases + 1) + (extra + 1)) + 1) ?_ (by omega)
        apply runStandardScreen_groupedDepth
        intro rows
        dsimp only
        split
        · exact (CappedController.terminal_groupedDepth extra h _).mono (by omega)
        · apply CappedController.peelPass_groupedDepth
          intro extra' h'
          exact ih (fun call ↦ blocks call.succ) extra' h'

end PackedSampler

namespace Sampler

variable {N : ℕ} {V Seed : Type*} [Fintype V] [DecidableEq V]

/-- Include the single distinguished all-mask stage before the program.
The remaining depth is witnessed by genuine fixed-state query groups and
mandatory commit calls, uniformly over seeds and preprocessing replies. -/
def WithinOracleDepth (A : Sampler N V Seed) (depth : ℕ) : Prop :=
  ∃ programDepth, 1 + programDepth ≤ depth ∧
    ∀ w reply, Program.GroupedOracleDepth (A.program w reply) programDepth

end Sampler

namespace PackedSampler

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]

/-- The displayed finite upper theorem's total adaptive oracle depth,
including preprocessing, is at most `1 + hardRoundCap + screenCallCap`. -/
theorem manuscript_sampler_withinOracleDepth (D L : ℕ) (t ρ η : ℝ)
    (hN : 0 < N) (hL : 0 < L)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N) :
    (sampler (Color := Fin (colorCount D))
      (manuscriptParameters N V D L t ρ η hN hL hfloor)).WithinOracleDepth
      (1 + ForestIteration.hardRoundCap N D + (ForestIteration.phaseCap N D + 1)) := by
  refine ⟨(ForestIteration.phaseCap N D + 1) + ForestIteration.hardRoundCap N D,
    by omega, ?_⟩
  intro blocks reply
  have hh := loop_groupedDepth
    (initialBanks reply t (ρ / Real.sqrt N) hfloor) (initialDraft reply) (initialMarginal reply)
    (coloringRepetitions N D η) (readoutSize N L) D (ρ / Real.sqrt N)
    (ForestIteration.phaseCap N D) blocks (ForestIteration.hardRoundCap N D - 1) (History.empty N V)
  apply hh.mono
  unfold ForestIteration.hardRoundCap
  omega

end PackedSampler
end ForestSampling
