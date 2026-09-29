import ForestSampling.ScreeningProgram

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace Screening

variable {N : ℕ} {V Color ι Transcript : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V]
variable [Fintype Color] [DecidableEq Color] [Fintype ι] [DecidableEq ι]

/-- Locate an observed source/readout row in the actual finite schedule.
Different readouts in the same chunk use the same indexed submission. -/
def readoutIndex (h : History N V) (B : Banks (N := N) (V := V))
    (colors : ι → Position N → Color) (q : ℕ) (τ : ι) (i j : ResidualVertex h)
    (hdiff : colors τ i ≠ colors τ j) (column : B.Column) : ProbeIndex h B colors q :=
  ⟨τ, ⟨(colors τ j, colorRank h (colors τ) j / q),
      Finset.mem_image.mpr ⟨j, j.property, rfl⟩⟩, ⟨colors τ i, hdiff⟩, column⟩

omit [Fintype Color] [Fintype ι] [DecidableEq ι] in
theorem scheduledSubmission_readoutIndex (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (q : ℕ) (τ : ι) (i j : ResidualVertex h)
    (hdiff : colors τ i ≠ colors τ j) (column : B.Column) :
    (scheduledSubmission h B draft colors q (readoutIndex h B colors q τ i j hdiff column)).state =
      probeState h B draft (colors τ) (colors τ i) (readoutChunk h (colors τ) q j) column := by
  simp only [scheduledSubmission, readoutIndex]
  rw [← readoutChunk_eq_keyChunk]

omit [LinearOrder V] in
private theorem oracleRow_congr (O : FrozenOracle N V) {y z : MaskedState N V}
    (i : MaskedPosition y) (j : MaskedPosition z) (hstate : y = z) (hindex : i.val = j.val) :
    O.row y i = O.row z j := by
  cases hstate
  have hij : i = j := Subtype.ext hindex
  cases hij
  rfl

/-- Retrieve one masked row from the collected reply table. No oracle is
available to this function; all observations arrive through query replies. -/
noncomputable def tableObserved (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (q : ℕ)
    (table : Program.ReplyTable (scheduledSubmission h B draft colors q))
    (τ : ι) (i j : ResidualVertex h) (hdiff : colors τ i ≠ colors τ j)
    (column : B.Column) : FinDist V :=
  table (readoutIndex h B colors q τ i j hdiff column) ⟨j, by
    rw [scheduledSubmission_readoutIndex, MaskedState.mem_masked_iff,
      probeState_masked_iff _ _ _ _ _ _ (readoutChunk_subset h (colors τ) q j)]
    exact readout_mem_chunk h (colors τ) q j⟩

omit [Fintype Color] [Fintype ι] [DecidableEq ι] in
theorem tableObserved_oracle (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (q : ℕ) (O : FrozenOracle N V)
    (τ : ι) (i j : ResidualVertex h) (hdiff : colors τ i ≠ colors τ j) (column : B.Column) :
    tableObserved h B draft colors q
      (fun index ↦ O.readState (scheduledSubmission h B draft colors q index).state)
      τ i j hdiff column = observedRow O h B draft (colors τ) q i j column := by
  exact oracleRow_congr O _ _
    (scheduledSubmission_readoutIndex h B draft colors q τ i j hdiff column) rfl

/-- Public vote computed exclusively from the collected reply table. -/
noncomputable def tableVote (h : History N V) (B : Banks (N := N) (V := V))
    (draft : Position N → V) (colors : ι → Position N → Color) (q : ℕ) (ε : ℝ)
    (table : Program.ReplyTable (scheduledSubmission h B draft colors q))
    (τ : ι) (i j : ResidualVertex h) : Prop :=
  if hdiff : colors τ i ≠ colors τ j then
    2 * ε < rowDiameter (tableObserved h B draft colors q table τ i j hdiff) else False

theorem tableVote_oracle_iff (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (q : ℕ) (ε : ℝ) (O : FrozenOracle N V)
    (τ : ι) (i j : ResidualVertex h) :
    tableVote h B draft colors q ε
      (fun index ↦ O.readState (scheduledSubmission h B draft colors q index).state) τ i j ↔
      Vote O h B draft (colors τ) q ε i j := by
  by_cases hdiff : colors τ i ≠ colors τ j
  · simp only [tableVote, dif_pos hdiff, Vote]
    have heq := funext (fun column ↦ tableObserved_oracle h B draft colors q O τ i j hdiff column)
    rw [heq]
    exact ⟨fun hv ↦ ⟨hdiff, hv⟩, fun hv ↦ hv.2⟩
  · simp [tableVote, Vote, hdiff]

noncomputable def tableCandidate (h : History N V) (B : Banks (N := N) (V := V))
    (draft : Position N → V) (colors : ι → Position N → Color) (q : ℕ) (ε : ℝ)
    (table : Program.ReplyTable (scheduledSubmission h B draft colors q))
    (j : ResidualVertex h) : Finset (ResidualVertex h) := by
  classical
  exact Finset.univ.filter (fun i ↦ i ≠ j ∧ Fintype.card ι <
    2 * (Finset.univ.filter (fun τ ↦ tableVote h B draft colors q ε table τ i j)).card)

theorem tableCandidate_oracle (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (q : ℕ) (ε : ℝ) (O : FrozenOracle N V)
    (j : ResidualVertex h) :
    tableCandidate h B draft colors q ε
      (fun index ↦ O.readState (scheduledSubmission h B draft colors q index).state) j =
      candidateRow O h B draft colors q ε j := by
  classical
  simp only [tableCandidate, candidateRow, tableVote_oracle_iff]

/-- A concrete screen program: empty banks return immediately; otherwise
the packed schedule collects all replies before votes and selection. The
constructor has no target graph, target law, or frozen-oracle argument. -/
noncomputable def runScreen (h : History N V) (B : Banks (N := N) (V := V))
    (draft : Position N → V) (colors : ι → Position N → Color) (q cutoff : ℕ) (ε : ℝ)
    (baseline : Position N → FinDist V)
    (selector : PublicRowSelector (ResidualVertex h) Transcript)
    (publicTranscript : Program.ReplyTable (scheduledSubmission h B draft colors q) → Transcript)
    (next : (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h) : Program N V h :=
  if B.maxSize = 0 then next (fun _ ↦ ∅) else
    runPackedQueries h B draft colors q (fun _ j ↦ baseline j)
      (fun table ↦ next (fun j ↦ selector.choose j
        (tableCandidate h B draft colors q ε table j) cutoff (publicTranscript table)))

/-- The actual `Program.query` screen returns precisely the previously
verified mathematical returned-row function. -/
theorem eval_runScreen (h : History N V) (B : Banks (N := N) (V := V))
    (draft : Position N → V) (colors : ι → Position N → Color) (q cutoff : ℕ) (ε : ℝ)
    (baseline : Position N → FinDist V)
    (selector : PublicRowSelector (ResidualVertex h) Transcript)
    (publicTranscript : Program.ReplyTable (scheduledSubmission h B draft colors q) → Transcript)
    (next : (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (O : FrozenOracle N V) :
    Program.eval O (runScreen h B draft colors q cutoff ε baseline selector publicTranscript next) =
      Program.eval O (next (returnedRow O h B draft colors q cutoff ε selector
        (publicTranscript (fun index ↦ O.readState (scheduledSubmission h B draft colors q index).state)))) := by
  by_cases hempty : B.maxSize = 0
  · simp only [runScreen, if_pos hempty]
    congr 2
    funext j
    simp only [returnedRow, if_pos hempty]
  · simp only [runScreen, if_neg hempty]
    rw [eval_runPackedQueries]
    congr 2
    funext j
    simp only [returnedRow, if_neg hempty, tableCandidate_oracle]

/-- The implemented screen's all-path query bound holds for every reply
table, with no screen-success or oracle-accuracy premise. -/
theorem runScreen_withinBudgets (h : History N V) (B : Banks (N := N) (V := V))
    (draft : Position N → V) (colors : ι → Position N → Color) (q cutoff : ℕ) (hq : 0 < q) (ε : ℝ)
    (baseline : Position N → FinDist V)
    (selector : PublicRowSelector (ResidualVertex h) Transcript)
    (publicTranscript : Program.ReplyTable (scheduledSubmission h B draft colors q) → Transcript)
    (next : (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (Q R : ℕ) (hnext : ∀ rows, Program.WithinBudgets (next rows) Q R) :
    Program.WithinBudgets (runScreen h B draft colors q cutoff ε baseline selector publicTranscript next)
      (Fintype.card ι * (h.uncommitted.card / q + Fintype.card Color) *
        (Fintype.card Color - 1) * (B.maxSize + 1) + Q) R := by
  unfold runScreen
  split
  · exact Program.withinBudgets_mono _ (hnext _) (Nat.le_add_left _ _) le_rfl
  · exact runPackedQueries_withinBudgets h B draft colors q hq _ _ Q R (fun _ ↦ hnext _)

end Screening
end ForestSampling
