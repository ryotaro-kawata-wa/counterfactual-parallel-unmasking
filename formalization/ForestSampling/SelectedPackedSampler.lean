import ForestSampling.PackedSampler
import ForestSampling.RowSelectorInvariance

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace SelectedPackedSampler

variable {N : ℕ} {V Color State : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]

/-- A public submission and the full reply actually received for that state. -/
structure Observation (N : ℕ) (V : Type*) [Fintype V] [DecidableEq V] where
  state : MaskedState N V
  reply : MaskedPosition state → FinDist V

/-- A selector policy may depend on retained public memory, the current
committed history, the current color block, and all completed screen replies.
It receives neither the target/oracle object nor any future color block.
The memory update permits retaining the entire available public transcript. -/
structure Policy (N : ℕ) (V Color State : Type*) [Fintype V] [DecidableEq V]
    (repetitions : ℕ) where
  selector : (h : History N V) → State → (Fin repetitions → Position N → Color) →
    PublicRowSelector (ResidualVertex h) (List (Observation N V))
  remember : (h : History N V) → State → (Fin repetitions → Position N → Color) →
    List (Observation N V) → State

/-- All actually scheduled state/reply observations, in the public schedule
order. This is formed only after the query collector has returned. -/
noncomputable def observations {repetitions : ℕ} (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : Fin repetitions → Position N → Color) (q : ℕ)
    (table : Program.ReplyTable (Screening.scheduledSubmission h B draft colors q)) :
    List (Observation N V) :=
  Finset.univ.toList.map fun index ↦
    ⟨(Screening.scheduledSubmission h B draft colors q index).state, table index⟩

/-- The actual selector-parametric screen. Public selection and memory
updates add no `Program.query` or `Program.commit` constructor. -/
noncomputable def runScreen {repetitions : ℕ} (policy : Policy N V Color State repetitions)
    (memory : State) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : State → (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h) :
    Program N V h := by
  classical
  exact if B.maxSize = 0 then next (policy.remember h memory colors []) (fun _ ↦ ∅) else
    Screening.runPackedQueries h B draft colors q (fun _ j ↦ baseline j)
      (fun table ↦
        let transcript := observations h B draft colors q table
        next (policy.remember h memory colors transcript)
          (fun j ↦ (policy.selector h memory colors).choose j
            (Screening.tableCandidate h B draft colors q ε table j) cutoff transcript))

/-- The public memory and selector do not alter the all-path per-screen
query allowance or spend any commit rounds. -/
theorem runScreen_withinBudgets {repetitions : ℕ} (policy : Policy N V Color State repetitions)
    (memory : State) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (hq : 0 < q) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : State → (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (Q R : ℕ) (hnext : ∀ memory rows, Program.WithinBudgets (next memory rows) Q R) :
    Program.WithinBudgets (runScreen policy memory h B draft baseline q cutoff ε colors next)
      (PackedSampler.perScreenQueries (Color := Color) B repetitions q + Q) R := by
  classical
  unfold runScreen
  split
  · exact Program.withinBudgets_mono _ (hnext _ _) (Nat.le_add_left _ _) le_rfl
  · let cont := fun (table : Program.ReplyTable (Screening.scheduledSubmission h B draft colors q)) ↦
      next (policy.remember h memory colors (observations h B draft colors q table))
        (fun j ↦ (policy.selector h memory colors).choose j
          (Screening.tableCandidate h B draft colors q ε table j) cutoff
          (observations h B draft colors q table))
    have hb := Screening.runPackedQueries_withinBudgets h B draft colors q hq
      (fun _ j ↦ baseline j) cont Q R (fun table ↦ hnext _ _)
    apply Program.withinBudgets_mono _ hb _ le_rfl
    have hcard : h.uncommitted.card ≤ N := by
      simpa using Finset.card_le_card (Finset.subset_univ h.uncommitted)
    simp only [Fintype.card_fin, PackedSampler.perScreenQueries]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (Nat.add_le_add_right (Nat.div_le_div_right hcard) _)))) Q

/-- The actual capped phase loop with arbitrary public memory and selector.
Only the current block is exposed before passing the unseen tail onward. -/
noncomputable def loop {repetitions : ℕ} (policy : Policy N V Color State repetitions)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (ε : ℝ) :
    (phases : ℕ) → PackedSampler.ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions →
      State → ℕ → (h : History N V) → Program N V h
  | 0, blocks, memory, extra, h =>
      if hc : h.committed = Finset.univ then .done hc else
        runScreen policy memory h B draft baseline q cutoff ε (blocks ⟨0, by omega⟩)
          (fun _ rows ↦ CappedController.terminal extra h (CappedController.rowGraph h rows))
  | phases' + 1, blocks, memory, extra, h =>
      if hc : h.committed = Finset.univ then .done hc else
        runScreen policy memory h B draft baseline q cutoff ε (blocks ⟨0, by omega⟩)
          (fun memory' rows ↦
            let peel := ForestPeeling.peelSet cutoff rows
            if peel = ∅ then CappedController.terminal extra h (CappedController.rowGraph h rows)
            else CappedController.peelPass
              ((peel.map (Function.Embedding.subtype _)).sort (· ≤ ·)) extra h
              (fun extra' h' ↦ loop policy B draft baseline q cutoff ε phases'
                (fun call ↦ blocks call.succ) memory' extra' h'))

/-- The entire policy-parametric executable obeys the same hard query and
round caps, uniformly over public memory, replies, and commit outcomes. -/
theorem loop_withinBudgets {repetitions : ℕ} (policy : Policy N V Color State repetitions)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (hq : 0 < q) (ε : ℝ)
    (phases : ℕ)
    (blocks : PackedSampler.ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions)
    (memory : State) (extra : ℕ) (h : History N V) :
    Program.WithinBudgets (loop policy B draft baseline q cutoff ε phases blocks memory extra h)
      ((phases + 1) * PackedSampler.perScreenQueries (Color := Color) B repetitions q) (extra + 1) := by
  induction phases generalizing memory extra h with
  | zero =>
      rw [loop]
      split
      · trivial
      · have hb := runScreen_withinBudgets policy memory h B draft baseline q cutoff hq ε
          (blocks ⟨0, by omega⟩) _ 0 (extra + 1)
          (fun _ rows ↦ CappedController.terminal_withinBudgets extra h (CappedController.rowGraph h rows) 0)
        simpa using hb
  | succ phases ih =>
      rw [loop]
      split
      · trivial
      · refine Program.withinBudgets_mono _ (runScreen_withinBudgets policy memory h B draft baseline q cutoff hq ε
          (blocks ⟨0, by omega⟩) _ ((phases + 1) * PackedSampler.perScreenQueries (Color := Color) B repetitions q)
          (extra + 1) ?_) ?_ le_rfl
        · intro memory' rows
          dsimp only
          split
          · exact CappedController.terminal_withinBudgets extra h _ _
          · apply CappedController.peelPass_withinBudgets
            intro extra' h'
            exact ih (fun call ↦ blocks call.succ) memory' extra' h'
        · simp only [Nat.add_mul, one_mul]
          omega

/-- A selector-parametric sampler in the existing protocol. Initial memory
is a function only of the public all-mask reply; it sees no color seed. -/
noncomputable def sampler (P : PackedSampler.Parameters N V)
    (policy : Policy N V Color State P.repetitions)
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State) :
    Sampler N V (PackedSampler.ColorBlocks (N := N) (Color := Color) (P.phases + 1) P.repetitions) where
  program blocks reply :=
    loop policy (PackedSampler.initialBanks reply P.threshold P.rowError P.thresholdFloor)
      (PackedSampler.initialDraft reply) (PackedSampler.initialMarginal reply)
      P.chunkSize P.cutoff P.rowError P.phases blocks (initialMemory reply) P.extraRounds (History.empty N V)

/-- The same hard public resources hold for every admissible policy and
initial public-memory function, even on unsuccessful screens. -/
theorem sampler_withinBudgets (P : PackedSampler.Parameters N V)
    (policy : Policy N V Color State P.repetitions)
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State) :
    (sampler P policy initialMemory).WithinBudgets (P.queryBudget Color) P.roundBudget := by
  intro blocks reply
  let B := PackedSampler.initialBanks reply P.threshold P.rowError P.thresholdFloor
  have hb := loop_withinBudgets policy B (PackedSampler.initialDraft reply) (PackedSampler.initialMarginal reply)
    P.chunkSize P.cutoff P.chunkSize_pos P.rowError P.phases blocks
    (initialMemory reply) P.extraRounds (History.empty N V)
  apply Program.withinBudgets_mono _ hb _ le_rfl
  unfold PackedSampler.Parameters.queryBudget PackedSampler.perScreenQueries
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right (PackedSampler.bankMax_le_vocab B) 1))

end SelectedPackedSampler
end ForestSampling
