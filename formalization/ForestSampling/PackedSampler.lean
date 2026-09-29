import ForestSampling.CappedController
import ForestSampling.ScreeningSuccessProbability

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace PackedSampler

variable {N : ℕ} {V Color : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]

abbrev InitialReply := MaskedPosition (MaskedState.allMask N V) → FinDist V

def initialMarginal (reply : InitialReply (N := N) (V := V)) (i : Position N) : FinDist V :=
  reply ⟨i, by simp⟩

/-- Build public banks from the actual distinguished all-mask reply. No
frozen oracle is available to the sampler constructor. -/
noncomputable def initialBanks (reply : InitialReply (N := N) (V := V)) (t ε : ℝ)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ε) : Screening.Banks (N := N) (V := V) := by
  classical
  let bank := fun i : Position N ↦ Finset.univ.filter (fun a ↦ t - ε ≤ initialMarginal reply i a)
  have hcomplement : ∀ i, (Finset.univ \ bank i).Nonempty := by
    intro i
    obtain ⟨a, ha⟩ := (initialMarginal reply i).exists_apply_le_inv_card
    refine ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro hmem
    have hm := (Finset.mem_filter.mp hmem).2
    linarith
  exact ⟨bank, fun i ↦ (Finset.univ \ bank i).min' (hcomplement i),
    fun _ ↦ (Finset.mem_sdiff.mp (Finset.min'_mem _ _)).2⟩

theorem initialBanks_oracle (O : FrozenOracle N V) (t ε : ℝ)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ε) :
    initialBanks (O.readState (MaskedState.allMask N V)) t ε hfloor =
      Screening.Banks.ofOracle O t ε hfloor := rfl

noncomputable def draftCandidates (reply : InitialReply (N := N) (V := V))
    (i : Position N) : Finset V := by
  classical
  exact Finset.univ.filter (fun a ↦ initialMarginal reply i a =
    Finset.univ.sup' Finset.univ_nonempty (initialMarginal reply i))

omit [LinearOrder V] in
theorem draftCandidates_nonempty (reply : InitialReply (N := N) (V := V))
    (i : Position N) : (draftCandidates reply i).Nonempty := by
  classical
  obtain ⟨a, ha, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (initialMarginal reply i)
  exact ⟨a, Finset.mem_filter.mpr ⟨ha, heq.symm⟩⟩

/-- The standard zero-query draft maximizes each initial marginal and
breaks ties by the public token order. -/
noncomputable def initialDraft (reply : InitialReply (N := N) (V := V)) (i : Position N) : V :=
  (draftCandidates reply i).min' (draftCandidates_nonempty reply i)

theorem initialDraft_maximizes (reply : InitialReply (N := N) (V := V))
    (i : Position N) (a : V) :
    initialMarginal reply i a ≤ initialMarginal reply i (initialDraft reply i) := by
  classical
  have hmem : initialMarginal reply i (initialDraft reply i) =
      Finset.univ.sup' Finset.univ_nonempty (initialMarginal reply i) := by
    exact (Finset.mem_filter.mp
      (Finset.min'_mem (draftCandidates reply i) (draftCandidates_nonempty reply i))).2
  rw [hmem]
  exact Finset.le_sup' _ (Finset.mem_univ a)

/-- Finite independent color blocks can be drawn before the execution;
the controller below reads only the current block, then passes the tail
to the next phase. Commit randomness stays in `Program.commit`. -/
abbrev ColorBlocks (calls repetitions : ℕ) := Fin calls → Fin repetitions → Position N → Color

/-- Uniform public per-screen submission allowance, retaining the actual
preprocessing bank maximum rather than replacing it by the vocabulary size. -/
def perScreenQueries (B : Screening.Banks (N := N) (V := V)) (repetitions q : ℕ) : ℕ :=
  repetitions * (N / q + Fintype.card Color) * (Fintype.card Color - 1) * (B.maxSize + 1)

noncomputable def runStandardScreen (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q cutoff : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h) : Program N V h := by
  classical
  exact Screening.runScreen h B draft colors q cutoff ε baseline
    (PublicRowSelector.standardTopVotes (fun (scores : ResidualVertex h → ResidualVertex h → ℕ) j i ↦ scores j i))
    (fun table j i ↦ (Finset.univ.filter
      (fun τ ↦ Screening.tableVote h B draft colors q ε table τ i j)).card) next

omit [Nonempty V] in
theorem runStandardScreen_withinBudgets (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q cutoff : ℕ) (hq : 0 < q) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (Q R : ℕ) (hnext : ∀ rows, Program.WithinBudgets (next rows) Q R) :
    Program.WithinBudgets (runStandardScreen h B draft baseline repetitions q cutoff ε colors next)
      (perScreenQueries (Color := Color) B repetitions q + Q) R := by
  classical
  have hbound := Screening.runScreen_withinBudgets h B draft colors q cutoff hq ε baseline
    (PublicRowSelector.standardTopVotes (fun (scores : ResidualVertex h → ResidualVertex h → ℕ) j i ↦ scores j i))
    (fun table j i ↦ (Finset.univ.filter
      (fun τ ↦ Screening.tableVote h B draft colors q ε table τ i j)).card) next Q R hnext
  apply Program.withinBudgets_mono _ hbound _ le_rfl
  have hcard : h.uncommitted.card ≤ N := by
    simpa using Finset.card_le_card (Finset.subset_univ h.uncommitted)
  simp only [Fintype.card_fin, perScreenQueries]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.div_le_div_right hcard) _)))) Q

/-- The concrete capped phase loop. One color block is consumed only after
the history/draft are fixed. Frozen peeling commits singleton vertices in
public order; phase exhaustion or an empty peel set enters the public
cycle-trimming/centroid terminal controller. -/
noncomputable def loop (B : Screening.Banks (N := N) (V := V))
    (draft : Position N → V) (baseline : Position N → FinDist V)
    (repetitions q cutoff : ℕ) (ε : ℝ) :
    (phases : ℕ) → ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions →
      ℕ → (h : History N V) → Program N V h
  | 0, blocks, extra, h =>
      if hc : h.committed = Finset.univ then .done hc else
        runStandardScreen h B draft baseline repetitions q cutoff ε (blocks ⟨0, by omega⟩)
          (fun rows ↦ CappedController.terminal extra h (CappedController.rowGraph h rows))
  | phases' + 1, blocks, extra, h =>
      if hc : h.committed = Finset.univ then .done hc else
        runStandardScreen h B draft baseline repetitions q cutoff ε (blocks ⟨0, by omega⟩)
          (fun rows ↦
            let peel := ForestPeeling.peelSet cutoff rows
            if peel = ∅ then CappedController.terminal extra h (CappedController.rowGraph h rows)
            else CappedController.peelPass
              ((peel.map (Function.Embedding.subtype _)).sort (· ≤ ·)) extra h
              (fun extra' h' ↦ loop B draft baseline repetitions q cutoff ε phases'
                (fun call ↦ blocks call.succ) extra' h'))

/-- The actual capped sampler obeys its hard query and commit-round budgets
for every seed, every all-mask reply, and every later reply/commit outcome. -/
theorem loop_withinBudgets (B : Screening.Banks (N := N) (V := V))
    (draft : Position N → V) (baseline : Position N → FinDist V)
    (repetitions q cutoff : ℕ) (hq : 0 < q) (ε : ℝ)
    (phases : ℕ) (blocks : ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions)
    (extra : ℕ) (h : History N V) :
    Program.WithinBudgets (loop B draft baseline repetitions q cutoff ε phases blocks extra h)
      ((phases + 1) * perScreenQueries (Color := Color) B repetitions q) (extra + 1) := by
  induction phases generalizing extra h with
  | zero =>
      rw [loop]
      split
      · trivial
      · have hb := runStandardScreen_withinBudgets h B draft baseline repetitions q cutoff hq ε
          (blocks ⟨0, by omega⟩) _ 0 (extra + 1)
          (fun rows ↦ CappedController.terminal_withinBudgets extra h (CappedController.rowGraph h rows) 0)
        simpa using hb
  | succ phases ih =>
      rw [loop]
      split
      · trivial
      · refine Program.withinBudgets_mono _ (runStandardScreen_withinBudgets h B draft baseline repetitions q cutoff hq ε
          (blocks ⟨0, by omega⟩) _ ((phases + 1) * perScreenQueries (Color := Color) B repetitions q)
          (extra + 1) ?_) ?_ le_rfl
        · intro rows
          dsimp only
          split
          · exact CappedController.terminal_withinBudgets extra h _ _
          · apply CappedController.peelPass_withinBudgets
            intro extra' h'
            exact ih (fun call ↦ blocks call.succ) extra' h'
        · simp only [Nat.add_mul, one_mul]
          omega

/-- Public parameters for the feasible-threshold version of the concrete
sampler. Grid selection and the theorem's rate-specific cap choices are
separate from this program construction. -/
structure Parameters (N : ℕ) (V : Type*) [Fintype V] where
  chunkSize : ℕ
  chunkSize_pos : 0 < chunkSize
  cutoff : ℕ
  phases : ℕ
  extraRounds : ℕ
  repetitions : ℕ
  threshold : ℝ
  rowError : ℝ
  thresholdFloor : (Fintype.card V : ℝ)⁻¹ < threshold - rowError

namespace Parameters

def queryBudget (P : Parameters N V) (Color : Type*) [Fintype Color] : ℕ :=
  (P.phases + 1) * (P.repetitions * (N / P.chunkSize + Fintype.card Color) *
    (Fintype.card Color - 1) * (Fintype.card V + 1))

def roundBudget (P : Parameters N V) : ℕ := P.extraRounds + 1

end Parameters

/-- The actual standard packed sampler as an existing `Sampler`: the only
preprocessing data available to its program is the supplied all-mask reply. -/
noncomputable def sampler (P : Parameters N V) :
    Sampler N V (ColorBlocks (N := N) (Color := Color) (P.phases + 1) P.repetitions) where
  program blocks reply :=
    loop (initialBanks reply P.threshold P.rowError P.thresholdFloor)
      (initialDraft reply) (initialMarginal reply) P.repetitions P.chunkSize P.cutoff P.rowError
      P.phases blocks P.extraRounds (History.empty N V)

omit [DecidableEq V] [LinearOrder V] [Nonempty V] in
theorem bankMax_le_vocab (B : Screening.Banks (N := N) (V := V)) :
    B.maxSize ≤ Fintype.card V := by
  apply Finset.sup_le
  intro i _
  exact (Finset.card_le_card (Finset.subset_univ (B.bank i))).trans_eq (Finset.card_univ)

/-- A universal hard resource contract, even for arbitrary preprocessing
replies. For sharper target-specific bank bounds, use `loop_withinBudgets`
with the actual initial bank maximum before this vocabulary relaxation. -/
theorem sampler_withinBudgets (P : Parameters N V) :
    (sampler (Color := Color) P).WithinBudgets (P.queryBudget Color) P.roundBudget := by
  intro blocks reply
  let B := initialBanks reply P.threshold P.rowError P.thresholdFloor
  have hb := loop_withinBudgets B (initialDraft reply) (initialMarginal reply)
    P.repetitions P.chunkSize P.cutoff P.chunkSize_pos P.rowError P.phases blocks
    P.extraRounds (History.empty N V)
  apply Program.withinBudgets_mono _ hb _ le_rfl
  unfold Parameters.queryBudget perScreenQueries
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right (bankMax_le_vocab B) 1))

/-- The actual finite decision-rule seed law: fresh independent uniform
coloring blocks, independent across reached and unreached call indices.
Product commit draws remain external to this seed as required by `Sampler`. -/
noncomputable def seedLaw [Nonempty Color] (P : Parameters N V) :
    FinDist (ColorBlocks (N := N) (Color := Color) (P.phases + 1) P.repetitions) :=
  FinDist.piProduct (fun _ : Fin (P.phases + 1) ↦
    FinDist.piProduct (fun _ : Fin P.repetitions ↦
      FinDist.uniformColors (α := Position N) (Color := Color)))

end PackedSampler
end ForestSampling
