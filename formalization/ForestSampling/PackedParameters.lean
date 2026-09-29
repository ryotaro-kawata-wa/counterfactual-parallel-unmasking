import ForestSampling.PackedFailure
import ForestSampling.ForestIteration

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace PackedSampler

variable {N : ℕ} {V Color : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]

/-- The actual screen has no columns when every bank is empty; otherwise
it uses the common bank maximum plus the certified tail column. -/
def screenColumns (B : Screening.Banks (N := N) (V := V)) : ℕ :=
  if B.maxSize = 0 then 0 else B.maxSize + 1

def columnQueryAllowance (B : Screening.Banks (N := N) (V := V)) (repetitions q : ℕ) : ℕ :=
  repetitions * (N / q + Fintype.card Color) * (Fintype.card Color - 1) * screenColumns B

omit [Nonempty V] in
/-- The exact all-empty-bank early exit costs no queries, while every
other screen obeys the packed schedule's all-reply query allowance. -/
theorem runStandardScreen_withinColumnBudget (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q cutoff : ℕ) (hq : 0 < q) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (Q R : ℕ) (hnext : ∀ rows, Program.WithinBudgets (next rows) Q R) :
    Program.WithinBudgets (runStandardScreen h B draft baseline repetitions q cutoff ε colors next)
      (columnQueryAllowance (Color := Color) B repetitions q + Q) R := by
  classical
  by_cases hempty : B.maxSize = 0
  · simpa only [runStandardScreen, Screening.runScreen, if_pos hempty,
      columnQueryAllowance, screenColumns, Nat.mul_zero, Nat.zero_add] using hnext (fun _ ↦ ∅)
  · simpa only [columnQueryAllowance, screenColumns, if_neg hempty, perScreenQueries] using
      runStandardScreen_withinBudgets h B draft baseline repetitions q cutoff hq ε colors next Q R hnext

omit [Nonempty V] in
/-- The concrete loop's bank-dependent all-path bound includes zero
counterfactual submissions on the all-empty-bank branch. -/
theorem loop_withinColumnBudget (B : Screening.Banks (N := N) (V := V))
    (draft : Position N → V) (baseline : Position N → FinDist V)
    (repetitions q cutoff : ℕ) (hq : 0 < q) (ε : ℝ)
    (phases : ℕ) (blocks : ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions)
    (extra : ℕ) (h : History N V) :
    Program.WithinBudgets (loop B draft baseline repetitions q cutoff ε phases blocks extra h)
      ((phases + 1) * columnQueryAllowance (Color := Color) B repetitions q) (extra + 1) := by
  induction phases generalizing extra h with
  | zero =>
      rw [loop]
      split
      · trivial
      · have hb := runStandardScreen_withinColumnBudget h B draft baseline repetitions q cutoff hq ε
          (blocks ⟨0, by omega⟩) _ 0 (extra + 1)
          (fun rows ↦ CappedController.terminal_withinBudgets extra h (CappedController.rowGraph h rows) 0)
        simpa using hb
  | succ phases ih =>
      rw [loop]
      split
      · trivial
      · refine Program.withinBudgets_mono _ (runStandardScreen_withinColumnBudget h B draft baseline
          repetitions q cutoff hq ε (blocks ⟨0, by omega⟩)
          _ ((phases + 1) * columnQueryAllowance (Color := Color) B repetitions q) (extra + 1) ?_)
          ?_ le_rfl
        · intro rows
          dsimp only
          split
          · exact CappedController.terminal_withinBudgets extra h _ _
          · apply CappedController.peelPass_withinBudgets
            intro extra' h'
            exact ih (fun call ↦ blocks call.succ) extra' h'
        · simp only [Nat.add_mul, one_mul]
          omega

/-- The manuscript's public number of colors. -/
def colorCount (D : ℕ) : ℕ := 8 * (D + 1)

instance colorCount_neZero (D : ℕ) : NeZero (colorCount D) :=
  ⟨by unfold colorCount; omega⟩

/-- The actual maximum readout chunk size is the ceiling of `N/L`. -/
noncomputable def readoutSize (N L : ℕ) : ℕ := ⌈(N : ℝ) / L⌉₊

theorem readoutSize_pos (N L : ℕ) (hN : 0 < N) (hL : 0 < L) :
    0 < readoutSize N L := by
  rw [readoutSize, Nat.ceil_pos]
  positivity

theorem div_readoutSize_le (N L : ℕ) (hL : 0 < L) : N / readoutSize N L ≤ L := by
  apply Nat.div_le_of_le_mul
  have hceil := Nat.le_ceil ((N : ℝ) / L)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hbound : (N : ℝ) ≤ (readoutSize N L : ℝ) * L :=
    (div_le_iff₀ hLr).mp hceil
  exact_mod_cast hbound

/-- The manuscript's exact logarithmic repetition allocation, before any
oracle query or commit. -/
noncomputable def coloringRepetitions (N D : ℕ) (η : ℝ) : ℕ :=
  ⌈8 * Real.log ((ForestIteration.phaseCap N D + 1 : ℕ) * (N : ℝ)^2 / η)⌉₊

theorem coloringRepetitions_spec (N D : ℕ) (η : ℝ) :
    8 * Real.log ((ForestIteration.phaseCap N D + 1 : ℕ) * (N : ℝ)^2 / η) ≤
      (coloringRepetitions N D η : ℝ) := Nat.le_ceil _

/-- The Hellinger-to-TV calibration gives the displayed repetition count
after allocating half the oracle radius to screen failures. -/
theorem coloringRepetitions_hellinger (N D : ℕ) (ρ : ℝ) :
    coloringRepetitions N D (ρ / 2) =
      ⌈8 * Real.log (2 * (ForestIteration.phaseCap N D + 1 : ℕ) * (N : ℝ)^2 / ρ)⌉₊ := by
  unfold coloringRepetitions
  apply congrArg Nat.ceil
  apply congrArg (fun x : ℝ ↦ 8 * Real.log x)
  rw [div_div_eq_mul_div]
  ring

/-- The forward-KL calibration allocates `epsilon/(2*N*log|V|)` to
screen failures and yields the manuscript's additional `N*log|V|` factor. -/
theorem coloringRepetitions_forwardKL (N D vocabSize : ℕ) (εKL : ℝ) :
    coloringRepetitions N D (εKL / (2 * N * Real.log vocabSize)) =
      ⌈8 * Real.log (2 * (ForestIteration.phaseCap N D + 1 : ℕ) *
        (N : ℝ)^3 * Real.log vocabSize / εKL)⌉₊ := by
  unfold coloringRepetitions
  apply congrArg Nat.ceil
  apply congrArg (fun x : ℝ ↦ 8 * Real.log x)
  rw [div_div_eq_mul_div]
  ring

/-- Instantiate every controller cap and color/chunk count by the public
finite-theorem formulas. The threshold is an explicit feasible public
choice; its grid selection is a separate preprocessing result. -/
noncomputable def manuscriptParameters (N : ℕ) (V : Type*) [Fintype V]
    (D L : ℕ) (t ρ η : ℝ) (hN : 0 < N) (hL : 0 < L)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N) : Parameters N V where
  chunkSize := readoutSize N L
  chunkSize_pos := readoutSize_pos N L hN hL
  cutoff := D
  phases := ForestIteration.phaseCap N D
  extraRounds := ForestIteration.hardRoundCap N D - 1
  repetitions := coloringRepetitions N D η
  threshold := t
  rowError := ρ / Real.sqrt N
  thresholdFloor := hfloor

omit [DecidableEq V] [LinearOrder V] [Nonempty V] in
theorem manuscript_roundBudget (D L : ℕ) (t ρ η : ℝ) (hN : 0 < N) (hL : 0 < L)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N) :
    (manuscriptParameters N V D L t ρ η hN hL hfloor).roundBudget =
      ForestIteration.hardRoundCap N D := by
  simp only [Parameters.roundBudget, manuscriptParameters, ForestIteration.hardRoundCap]
  omega

/-- The exact finite theorem's pathwise resources, with actual banks from
the supplied preprocessing reply. Later replies, seeds, and product-commit
outcomes are all universally quantified by `WithinBudgets`. -/
theorem manuscript_program_withinBudgets (D L : ℕ) (t ρ η : ℝ)
    (hN : 0 < N) (hL : 0 < L)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N)
    (blocks : ColorBlocks (N := N) (Color := Fin (colorCount D))
      (ForestIteration.phaseCap N D + 1) (coloringRepetitions N D η))
    (reply : InitialReply (N := N) (V := V)) :
    Program.WithinBudgets
      ((sampler (Color := Fin (colorCount D))
        (manuscriptParameters N V D L t ρ η hN hL hfloor)).program blocks reply)
      (screenColumns (initialBanks reply t (ρ / Real.sqrt N) hfloor) *
        (ForestIteration.phaseCap N D + 1) * coloringRepetitions N D η * colorCount D *
        (colorCount D + L)) (ForestIteration.hardRoundCap N D) := by
  let B := initialBanks reply t (ρ / Real.sqrt N) hfloor
  have hb := loop_withinColumnBudget B (initialDraft reply) (initialMarginal reply)
    (coloringRepetitions N D η) (readoutSize N L) D (readoutSize_pos N L hN hL)
    (ρ / Real.sqrt N) (ForestIteration.phaseCap N D) blocks
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
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N) :
    (sampler (Color := Fin (colorCount D))
      (manuscriptParameters N V D L t ρ η hN hL hfloor)).WithinBudgets
      ((Fintype.card V + 1) * (ForestIteration.phaseCap N D + 1) *
        coloringRepetitions N D η * colorCount D * (colorCount D + L))
      (ForestIteration.hardRoundCap N D) := by
  intro blocks reply
  apply Program.withinBudgets_mono _
    (manuscript_program_withinBudgets D L t ρ η hN hL hfloor blocks reply) _ le_rfl
  have hcolumns : screenColumns (initialBanks reply t (ρ / Real.sqrt N) hfloor) ≤
      Fintype.card V + 1 := by
    unfold screenColumns
    split
    · omega
    · exact Nat.add_le_add_right (bankMax_le_vocab _) 1
  gcongr

/-- The public counts automatically discharge the color and repetition
hypotheses of the actual adaptive failure theorem. -/
theorem manuscript_mean_failure_le (D L : ℕ) (t ρ η : ℝ)
    (hN : 0 < N) (hL : 0 < L) (hη : 0 < η)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ρ / Real.sqrt N)
    (M : ForestModel N V) (O : FrozenOracle N V) (K : BatchKernel N V) :
    let P := manuscriptParameters N V D L t ρ η hN hL hfloor
    (∑ blocks, seedLaw (Color := Fin (colorCount D)) P blocks *
      (samplerMarker P M O blocks).failureMassWith O K) ≤ η := by
  apply sampler_mean_failure_le _ M O K η hN hη
  · change 8 * (D + 1) ≤ Fintype.card (Fin (colorCount D))
    rw [Fintype.card_fin]
    exact le_rfl
  · exact coloringRepetitions_spec N D η

end PackedSampler
end ForestSampling
