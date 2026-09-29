import ForestSampling.ScreeningResources

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace Screening

variable {N : ℕ} {V Color ι : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable [Fintype Color] [DecidableEq Color] [Fintype ι] [DecidableEq ι]

/-- One scheduled packed submission is indexed by its coloring, nonempty
readout chunk, different source color, and source column. Masked readouts
are deliberately not an extra index: they share the same state submission. -/
abbrev ProbeIndex (h : History N V) (B : Banks (N := N) (V := V))
    (colors : ι → Position N → Color) (q : ℕ) :=
  (τ : ι) × (key : chunkKeys h (colors τ) q) ×
    ({c : Color // c ≠ key.val.1} × B.Column)

noncomputable def scheduledSubmission (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (q : ℕ) (index : ProbeIndex h B colors q) : Submission h where
  state := probeState h B draft (colors index.1) index.2.2.1
    (keyChunk h (colors index.1) q index.2.1) index.2.2.2
  respects := probeState_respects _ _ _ _ _ _ _

omit [Fintype Color] [Fintype ι] [DecidableEq ι] in
/-- The actual scheduled state masks at most the public chunk size. -/
theorem scheduledSubmission_masked_card_le (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (q : ℕ) (hq : 0 < q)
    (index : ProbeIndex h B colors q) :
    (scheduledSubmission h B draft colors q index).state.masked.card ≤ q := by
  have hmask : (scheduledSubmission h B draft colors q index).state.masked =
      keyChunk h (colors index.1) q index.2.1 := by
    ext j
    rw [MaskedState.mem_masked_iff]
    exact probeState_masked_iff h B draft (colors index.1) index.2.2.1 _
      (keyChunk_subset h (colors index.1) q index.2.1) index.2.2.2 j
  rw [hmask]
  exact keyChunk_card_le _ _ _ hq _

private theorem sourceColor_card (c : Color) :
    Fintype.card {d : Color // d ≠ c} = Fintype.card Color - 1 := by
  change Fintype.card {d : Color // ¬ d = c} = _
  rw [Fintype.card_subtype_compl]
  simp

omit [Fintype V] [DecidableEq V] [LinearOrder V] [DecidableEq ι] in
/-- Exact number of state submissions in the public packed schedule. -/
theorem probeIndex_card (h : History N V) (B : Banks (N := N) (V := V))
    (colors : ι → Position N → Color) (q : ℕ) :
    Fintype.card (ProbeIndex h B colors q) =
      ∑ τ : ι, (chunkKeys h (colors τ) q).card * (Fintype.card Color - 1) * (B.maxSize + 1) := by
  simp only [ProbeIndex, Fintype.card_sigma, Fintype.card_prod, sourceColor_card,
    Banks.Column, Fintype.card_option, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro τ _
  ring

omit [Fintype V] [DecidableEq V] [LinearOrder V] [DecidableEq ι] in
/-- The packed query count keeps the chunking gain: it scales with
`|U|/q + colorCount`, rather than with one query per readout. -/
theorem probeIndex_card_le (h : History N V) (B : Banks (N := N) (V := V))
    (colors : ι → Position N → Color) (q : ℕ) (hq : 0 < q) :
    Fintype.card (ProbeIndex h B colors q) ≤
      Fintype.card ι * (h.uncommitted.card / q + Fintype.card Color) *
        (Fintype.card Color - 1) * (B.maxSize + 1) := by
  rw [probeIndex_card]
  calc
    _ ≤ ∑ _ : ι, (h.uncommitted.card / q + Fintype.card Color) *
        (Fintype.card Color - 1) * (B.maxSize + 1) := by
      apply Finset.sum_le_sum
      intro τ _
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (chunkKeys_card_le h (colors τ) q hq))
    _ = _ := by simp [Nat.mul_assoc]

/-- The finite schedule is public once the current history, fixed draft,
banks, and current color block have been supplied. -/
noncomputable def runPackedQueries (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (q : ℕ)
    (initial : Program.ReplyTable (scheduledSubmission h B draft colors q))
    (next : Program.ReplyTable (scheduledSubmission h B draft colors q) → Program N V h) :
    Program N V h :=
  Program.runQuerySchedule (scheduledSubmission h B draft colors q)
    Finset.univ.toList initial next

/-- The enumerated packed queries return exactly the oracle answers to all
scheduled states. There is no direct oracle access in the program builder. -/
theorem eval_runPackedQueries (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (q : ℕ) (O : FrozenOracle N V)
    (initial : Program.ReplyTable (scheduledSubmission h B draft colors q))
    (next : Program.ReplyTable (scheduledSubmission h B draft colors q) → Program N V h) :
    Program.eval O (runPackedQueries h B draft colors q initial next) =
      Program.eval O (next (fun index ↦ O.readState
        (scheduledSubmission h B draft colors q index).state)) := by
  rw [runPackedQueries, Program.eval_runQuerySchedule,
    Program.fillQueryReplies_eq _ O _ (fun _ ↦ by simp)]

/-- Every possible reply path obeys the sharp packed submission budget.
This is an actual `Program.WithinBudgets` guarantee, including bad screens. -/
theorem runPackedQueries_withinBudgets (h : History N V)
    (B : Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : ι → Position N → Color) (q : ℕ) (hq : 0 < q)
    (initial : Program.ReplyTable (scheduledSubmission h B draft colors q))
    (next : Program.ReplyTable (scheduledSubmission h B draft colors q) → Program N V h)
    (Q R : ℕ) (hnext : ∀ replies, Program.WithinBudgets (next replies) Q R) :
    Program.WithinBudgets (runPackedQueries h B draft colors q initial next)
      (Fintype.card ι * (h.uncommitted.card / q + Fintype.card Color) *
        (Fintype.card Color - 1) * (B.maxSize + 1) + Q) R := by
  have hbound := Program.runQuerySchedule_withinBudgets
    (scheduledSubmission h B draft colors q) Finset.univ.toList initial next Q R hnext
  apply Program.withinBudgets_mono _ hbound _ le_rfl
  simp only [Finset.length_toList, Finset.card_univ]
  exact Nat.add_le_add_right (probeIndex_card_le h B colors q hq) Q

end Screening
end ForestSampling
