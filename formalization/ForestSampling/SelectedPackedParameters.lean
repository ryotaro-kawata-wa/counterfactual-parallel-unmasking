import ForestSampling.SelectedPackedSampler
import ForestSampling.PackedParameters

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.SelectedPackedSampler

variable {N repetitions : ℕ} {V Color State : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]

open PackedSampler (ColorBlocks InitialReply initialBanks initialDraft initialMarginal
  screenColumns columnQueryAllowance perScreenQueries colorCount coloringRepetitions
  manuscriptParameters readoutSize readoutSize_pos div_readoutSize_le bankMax_le_vocab)

/-- The exact all-empty-bank early exit costs no queries, while every
other screen obeys the packed schedule's all-reply query allowance. -/
theorem runScreen_withinColumnBudget (policy : Policy N V Color State repetitions) (memory : State) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (hq : 0 < q) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : State → (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (Q R : ℕ) (hnext : ∀ memory rows, Program.WithinBudgets (next memory rows) Q R) :
    Program.WithinBudgets (runScreen policy memory h B draft baseline q cutoff ε colors next)
      (columnQueryAllowance (Color := Color) B repetitions q + Q) R := by
  classical
  by_cases hempty : B.maxSize = 0
  · simpa only [runScreen, if_pos hempty,
      columnQueryAllowance, screenColumns, Nat.mul_zero, Nat.zero_add] using hnext (policy.remember h memory colors []) (fun _ ↦ ∅)
  · simpa only [columnQueryAllowance, screenColumns, if_neg hempty, perScreenQueries] using
      runScreen_withinBudgets policy memory h B draft baseline q cutoff hq ε colors next Q R hnext

/-- The concrete loop's bank-dependent all-path bound includes zero
counterfactual submissions on the all-empty-bank branch. -/
theorem loop_withinColumnBudget (policy : Policy N V Color State repetitions) (B : Screening.Banks (N := N) (V := V))
    (draft : Position N → V) (baseline : Position N → FinDist V)
    (q cutoff : ℕ) (hq : 0 < q) (ε : ℝ)
    (phases : ℕ) (blocks : ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions)
    (memory : State) (extra : ℕ) (h : History N V) :
    Program.WithinBudgets (loop policy B draft baseline q cutoff ε phases blocks memory extra h)
      ((phases + 1) * columnQueryAllowance (Color := Color) B repetitions q) (extra + 1) := by
  induction phases generalizing memory extra h with
  | zero =>
      rw [loop]
      split
      · trivial
      · have hb := runScreen_withinColumnBudget policy memory h B draft baseline q cutoff hq ε
          (blocks ⟨0, by omega⟩) _ 0 (extra + 1)
          (fun _ rows ↦ CappedController.terminal_withinBudgets extra h (CappedController.rowGraph h rows) 0)
        simpa using hb
  | succ phases ih =>
      rw [loop]
      split
      · trivial
      · refine Program.withinBudgets_mono _ (runScreen_withinColumnBudget policy memory h B draft baseline
          q cutoff hq ε (blocks ⟨0, by omega⟩)
          _ ((phases + 1) * columnQueryAllowance (Color := Color) B repetitions q) (extra + 1) ?_)
          ?_ le_rfl
        · intro memory' rows
          dsimp only
          split
          · exact CappedController.terminal_withinBudgets extra h _ _
          · apply CappedController.peelPass_withinBudgets
            intro extra' h'
            exact ih (fun call ↦ blocks call.succ) memory' extra' h'
        · simp only [Nat.add_mul, one_mul]
          omega

/-- The exact finite theorem's pathwise resources, with actual banks from
the supplied preprocessing reply. Later replies, seeds, and product-commit
outcomes are all universally quantified by `WithinBudgets`. -/
theorem manuscript_program_withinBudgets (D L : ℕ) (t ρ η : ℝ)
    (hN : 0 < N) (hL : 0 < L)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N)
    (policy : Policy N V (Fin (colorCount D)) State (coloringRepetitions N D η))
    (initialMemory : InitialReply (N := N) (V := V) → State)
    (blocks : ColorBlocks (N := N) (Color := Fin (colorCount D))
      (ForestIteration.phaseCap N D + 1) (coloringRepetitions N D η))
    (reply : InitialReply (N := N) (V := V)) :
    Program.WithinBudgets
      ((sampler (manuscriptParameters N V D L t ρ η hN hL hfloor) policy initialMemory).program blocks reply)
      (screenColumns (initialBanks reply t (ρ / Real.sqrt N) hfloor) *
        (ForestIteration.phaseCap N D + 1) * coloringRepetitions N D η * colorCount D *
        (colorCount D + L)) (ForestIteration.hardRoundCap N D) := by
  let B := initialBanks reply t (ρ / Real.sqrt N) hfloor
  have hb := loop_withinColumnBudget policy B (initialDraft reply) (initialMarginal reply) (readoutSize N L) D (readoutSize_pos N L hN hL)
    (ρ / Real.sqrt N) (ForestIteration.phaseCap N D) blocks (initialMemory reply)
    (ForestIteration.hardRoundCap N D - 1) (History.empty N V)
  apply Program.withinBudgets_mono _ hb
  · simp only [columnQueryAllowance, Fintype.card_fin]
    calc
      _ ≤ (ForestIteration.phaseCap N D + 1) *
          (coloringRepetitions N D η * (L + colorCount D) * colorCount D * screenColumns B) := by
        gcongr
        · exact div_readoutSize_le N L hL
        · exact Nat.sub_le _ _
      _ = _ := by ring
  · unfold ForestIteration.hardRoundCap
    omega

/-- A fully public resource contract for arbitrary preprocessing replies.
The preceding theorem retains the sharper actual-bank factor. -/
theorem manuscript_sampler_withinBudgets (D L : ℕ) (t ρ η : ℝ)
    (hN : 0 < N) (hL : 0 < L)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N)
    (policy : Policy N V (Fin (colorCount D)) State (coloringRepetitions N D η))
    (initialMemory : InitialReply (N := N) (V := V) → State) :
    (sampler (manuscriptParameters N V D L t ρ η hN hL hfloor) policy initialMemory).WithinBudgets
      ((Fintype.card V + 1) * (ForestIteration.phaseCap N D + 1) *
        coloringRepetitions N D η * colorCount D * (colorCount D + L))
      (ForestIteration.hardRoundCap N D) := by
  intro blocks reply
  apply Program.withinBudgets_mono _
    (manuscript_program_withinBudgets D L t ρ η hN hL hfloor policy initialMemory blocks reply) _ le_rfl
  have hcolumns : screenColumns (initialBanks reply t (ρ / Real.sqrt N) hfloor) ≤
      Fintype.card V + 1 := by
    unfold screenColumns
    split
    · omega
    · exact Nat.add_le_add_right (bankMax_le_vocab _) 1
  gcongr


end ForestSampling.SelectedPackedSampler
