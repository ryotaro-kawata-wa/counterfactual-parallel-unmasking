import ForestSampling.PackedDepth

set_option autoImplicit false

namespace ForestSampling
namespace Program

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Follow the actual frozen-oracle answers through a fixed query block.
No retained commit outcome is removed: a read-only schedule contains no
commits, and its continuation receives exactly the collected reply table. -/
noncomputable def querySchedulePath {Index : Type} [DecidableEq Index]
    {h : History N V} (queries : Index → Submission h) (O : FrozenOracle N V) :
    (todo : List Index) → (replies : ReplyTable queries) →
    (next : ReplyTable queries → Program N V h) →
    RetainedPath O (runQuerySchedule queries todo replies next) →
      RetainedPath O (next (fillQueryReplies queries O todo replies))
  | [], _replies, _next, path => path
  | i :: todo, replies, next, path =>
      querySchedulePath queries O todo
        (Function.update replies i (O.readState (queries i).state)) next path

/-- Grouping independent queries preserves the actual number of mandatory
commit calls along each retained execution. -/
theorem retainedRoundCount_querySchedule {Index : Type} [DecidableEq Index]
    {h : History N V} (queries : Index → Submission h) (O : FrozenOracle N V)
    (todo : List Index) (replies : ReplyTable queries)
    (next : ReplyTable queries → Program N V h)
    (path : RetainedPath O (runQuerySchedule queries todo replies next)) :
    retainedRoundCount O (runQuerySchedule queries todo replies next) path =
      retainedRoundCount O (next (fillQueryReplies queries O todo replies))
        (querySchedulePath queries O todo replies next path) := by
  induction todo generalizing replies with
  | nil => rfl
  | cons i todo ih => exact ih _ path

/-- A legal grouped oracle trace on one actual retained execution. Query
groups require all states to be fixed before replies; mandatory commits
are counted separately, one stage per actual sampled batch. -/
inductive GroupedOracleTrace (O : FrozenOracle N V) :
    {h : History N V} → (p : Program N V h) → RetainedPath O p → ℕ → Prop
  | done {h : History N V} (complete : h.committed = Finset.univ)
      (path : RetainedPath O (.done complete)) : GroupedOracleTrace O (.done complete) path 0
  | queryBlock {h : History N V} {Index : Type} [DecidableEq Index]
      (queries : Index → Submission h) (todo : List Index) (replies : ReplyTable queries)
      (next : ReplyTable queries → Program N V h)
      (path : RetainedPath O (runQuerySchedule queries todo replies next)) (depth : ℕ)
      (following : GroupedOracleTrace O (next (fillQueryReplies queries O todo replies))
        (querySchedulePath queries O todo replies next path) depth) :
      GroupedOracleTrace O (runQuerySchedule queries todo replies next) path (depth + 1)
  | commit {h : History N V} (batch : Finset (Position N)) (nonempty : batch.Nonempty)
      (fresh : batch ⊆ h.uncommitted)
      (next : (z : batch → V) → Program N V (h.appendBatch batch fresh z))
      (z : batch → V) (path : RetainedPath O (next z)) (depth : ℕ)
      (following : GroupedOracleTrace O (next z) path depth) :
      GroupedOracleTrace O (.commit batch nonempty fresh next) ⟨z, path⟩ (depth + 1)

/-- The number of grouped stages in excess of the actual commit count is
bounded by `screens`, separately on every retained execution path. -/
def PathScreenStages (O : FrozenOracle N V) {h : History N V}
    (p : Program N V h) (screens : ℕ) : Prop :=
  ∀ path : RetainedPath O p, ∃ depth,
    GroupedOracleTrace O p path depth ∧ depth ≤ retainedRoundCount O p path + screens

theorem PathScreenStages.mono (O : FrozenOracle N V) {h : History N V}
    {p : Program N V h} {a b : ℕ} (hp : PathScreenStages O p a) (hab : a ≤ b) :
    PathScreenStages O p b := by
  intro path
  obtain ⟨depth, htrace, hbound⟩ := hp path
  exact ⟨depth, htrace, hbound.trans (Nat.add_le_add_left hab _)⟩

theorem pathScreenStages_done (O : FrozenOracle N V) {h : History N V}
    (complete : h.committed = Finset.univ) (screens : ℕ) :
    PathScreenStages O (.done complete) screens := by
  intro path
  exact ⟨0, .done complete path, Nat.zero_le _⟩

theorem pathScreenStages_commit (O : FrozenOracle N V) {h : History N V}
    (batch : Finset (Position N)) (nonempty : batch.Nonempty) (fresh : batch ⊆ h.uncommitted)
    (next : (z : batch → V) → Program N V (h.appendBatch batch fresh z)) (screens : ℕ)
    (hnext : ∀ z, PathScreenStages O (next z) screens) :
    PathScreenStages O (.commit batch nonempty fresh next) screens := by
  intro path
  obtain ⟨depth, htrace, hbound⟩ := hnext path.1 path.2
  refine ⟨depth + 1, .commit batch nonempty fresh next path.1 path.2 depth htrace, ?_⟩
  change depth + 1 ≤ (1 + retainedRoundCount O (next path.1) path.2) + screens
  omega

theorem pathScreenStages_queryBlock {Index : Type} [DecidableEq Index]
    {h : History N V} (queries : Index → Submission h) (O : FrozenOracle N V)
    (todo : List Index) (replies : ReplyTable queries)
    (next : ReplyTable queries → Program N V h) (screens : ℕ)
    (hnext : ∀ table, PathScreenStages O (next table) screens) :
    PathScreenStages O (runQuerySchedule queries todo replies next) (screens + 1) := by
  intro path
  obtain ⟨depth, htrace, hbound⟩ := hnext (fillQueryReplies queries O todo replies)
    (querySchedulePath queries O todo replies next path)
  refine ⟨depth + 1, .queryBlock queries todo replies next path depth htrace, ?_⟩
  rw [retainedRoundCount_querySchedule]
  omega

theorem commitAll_pathScreenStages (O : FrozenOracle N V) (h : History N V) :
    PathScreenStages O (commitAll h) 0 := by
  unfold commitAll
  split
  · exact pathScreenStages_done O _ _
  · exact pathScreenStages_commit O _ _ _ _ _ (fun _ ↦ pathScreenStages_done O _ _)

end Program

namespace CappedController

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem terminal_pathScreenStages (O : FrozenOracle N V) (extra : ℕ) (h : History N V)
    (G : SimpleGraph (Position N)) : Program.PathScreenStages O (terminal extra h G) 0 := by
  induction extra generalizing h with
  | zero =>
      unfold terminal
      split
      · exact Program.pathScreenStages_done O _ _
      · exact Program.commitAll_pathScreenStages O h
  | succ extra ih =>
      unfold terminal
      split
      · exact Program.pathScreenStages_done O _ _
      · exact Program.pathScreenStages_commit O _ _ _ _ _ (fun _ ↦ ih _)

theorem peelPass_pathScreenStages (O : FrozenOracle N V) (todo : List (Position N))
    (extra : ℕ) (h : History N V)
    (after : (extra : ℕ) → (h : History N V) → Program N V h) (screens : ℕ)
    (hafter : ∀ extra h, Program.PathScreenStages O (after extra h) screens) :
    Program.PathScreenStages O (peelPass todo extra h after) screens := by
  induction todo generalizing extra h with
  | nil => exact hafter extra h
  | cons j todo ih =>
      rw [peelPass]
      split
      · exact Program.pathScreenStages_done O _ _
      · split
        · cases extra with
          | zero => exact (Program.commitAll_pathScreenStages O h).mono O (Nat.zero_le _)
          | succ extra => exact Program.pathScreenStages_commit O _ _ _ _ _ (fun _ ↦ ih extra _)
        · exact ih extra h

end CappedController

namespace PackedSampler

variable {N : ℕ} {V : Type*} {Color : Type}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]

omit [Nonempty V] in
theorem runStandardScreen_pathScreenStages (O : FrozenOracle N V) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q cutoff : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (screens : ℕ) (hnext : ∀ rows, Program.PathScreenStages O (next rows) screens) :
    Program.PathScreenStages O (runStandardScreen h B draft baseline repetitions q cutoff ε colors next)
      (screens + 1) := by
  classical
  unfold runStandardScreen Screening.runScreen
  split
  · exact (hnext _).mono O (by omega)
  · exact Program.pathScreenStages_queryBlock _ O _ _ _ screens (fun _ ↦ hnext _)

omit [Nonempty V] in
/-- At most one fixed-state query group is charged for each available
screen call, independently of how many commit rounds a path actually uses. -/
theorem loop_pathScreenStages (O : FrozenOracle N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q cutoff : ℕ) (ε : ℝ)
    (phases : ℕ) (blocks : ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions)
    (extra : ℕ) (h : History N V) :
    Program.PathScreenStages O (loop B draft baseline repetitions q cutoff ε phases blocks extra h)
      (phases + 1) := by
  induction phases generalizing extra h with
  | zero =>
      rw [loop]
      split
      · exact Program.pathScreenStages_done O _ _
      · apply runStandardScreen_pathScreenStages
        intro rows
        exact CappedController.terminal_pathScreenStages O extra h _
  | succ phases ih =>
      rw [loop]
      split
      · exact Program.pathScreenStages_done O _ _
      · apply runStandardScreen_pathScreenStages
        intro rows
        dsimp only
        split
        · exact (CappedController.terminal_pathScreenStages O extra h _).mono O (Nat.zero_le _)
        · apply CappedController.peelPass_pathScreenStages
          intro extra' h'
          exact ih (fun call ↦ blocks call.succ) extra' h'

/-- The exact printed pathwise depth clause, with the path's actual commit
count, together with a genuine grouped trace of the concrete program. The
initial `1` is precisely the distinguished all-mask preprocessing stage. -/
theorem manuscript_sampler_pathwiseOracleDepth (D L : ℕ) (t ρ η : ℝ)
    (hN : 0 < N) (hL : 0 < L)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N)
    (blocks : ColorBlocks (N := N) (Color := Fin (colorCount D))
      (ForestIteration.phaseCap N D + 1) (coloringRepetitions N D η))
    (reply : InitialReply (N := N) (V := V)) (O : FrozenOracle N V)
    (path : Program.RetainedPath O ((sampler (Color := Fin (colorCount D))
      (manuscriptParameters N V D L t ρ η hN hL hfloor)).program blocks reply)) :
    ∃ depth, Program.GroupedOracleTrace O
        ((sampler (Color := Fin (colorCount D))
          (manuscriptParameters N V D L t ρ η hN hL hfloor)).program blocks reply) path depth ∧
      1 + depth ≤ 1 + Program.retainedRoundCount O
        ((sampler (Color := Fin (colorCount D))
          (manuscriptParameters N V D L t ρ η hN hL hfloor)).program blocks reply) path +
        (ForestIteration.phaseCap N D + 1) := by
  have hb := loop_pathScreenStages O (initialBanks reply t (ρ / Real.sqrt N) hfloor)
    (initialDraft reply) (initialMarginal reply) (coloringRepetitions N D η) (readoutSize N L)
    D (ρ / Real.sqrt N) (ForestIteration.phaseCap N D) blocks
    (ForestIteration.hardRoundCap N D - 1) (History.empty N V)
  obtain ⟨depth, htrace, hbound⟩ := hb path
  exact ⟨depth, htrace, by
    simpa only [sampler, manuscriptParameters, Nat.add_assoc] using Nat.add_le_add_left hbound 1⟩

end PackedSampler
end ForestSampling
