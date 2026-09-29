import ForestSampling.PackedStructure

set_option autoImplicit false

namespace ForestSampling.PublicRowSelector

variable {α Transcript : Type*} [Fintype α] [DecidableEq α]

/-- The removed set associated with any admissible selector. -/
def dropped (selector : PublicRowSelector α Transcript) (j : α)
    (C : Finset α) (cutoff : ℕ) (transcript : Transcript) : Finset α :=
  C \ selector.choose j C cutoff transcript

/-- The abstract selector contract gives exactly the manuscript's
candidate-minus-dropped-set representation. -/
theorem choose_eq_sdiff_dropped (selector : PublicRowSelector α Transcript)
    (j : α) (C : Finset α) (cutoff : ℕ) (transcript : Transcript) :
    selector.choose j C cutoff transcript = C \ selector.dropped j C cutoff transcript := by
  have hs := selector.subset j C cutoff transcript
  ext i
  simp only [dropped, Finset.mem_sdiff]
  constructor
  · intro hi
    exact ⟨hs hi, fun hn ↦ hn.2 hi⟩
  · rintro ⟨hi, hn⟩
    by_contra hnot
    exact hn ⟨hi, hnot⟩

/-- At least the excess candidate count is removed. The statement also
holds on nonoverflowing rows, where the excess is zero. -/
theorem dropped_card_ge_excess (selector : PublicRowSelector α Transcript)
    (j : α) (C : Finset α) (cutoff : ℕ) (transcript : Transcript) :
    C.card - cutoff ≤ (selector.dropped j C cutoff transcript).card := by
  have hc := Finset.card_sdiff_add_card_eq_card (selector.subset j C cutoff transcript)
  have hcap := selector.card_le j C cutoff transcript
  change C.card - cutoff ≤ (C \ selector.choose j C cutoff transcript).card
  omega

/-- Nonoverflowing rows have no removed candidates at all. -/
theorem dropped_eq_empty_of_nonoverflow (selector : PublicRowSelector α Transcript)
    (j : α) (C : Finset α) (cutoff : ℕ) (transcript : Transcript) (hc : C.card ≤ cutoff) :
    selector.dropped j C cutoff transcript = ∅ := by
  simp only [dropped, selector.preserves j C cutoff transcript hc, Finset.sdiff_self]

/-- Conversely, the manuscript's explicit overflow-deletion rule satisfies
all three laws used by the concrete screen and forest proofs. -/
def ofDropRule (drop : α → Finset α → ℕ → Transcript → Finset α)
    (hsub : ∀ j C cutoff transcript, drop j C cutoff transcript ⊆ C)
    (hdrop : ∀ j C cutoff transcript, cutoff < C.card →
      C.card - cutoff ≤ (drop j C cutoff transcript).card) : PublicRowSelector α Transcript where
  choose j C cutoff transcript := if C.card ≤ cutoff then C else C \ drop j C cutoff transcript
  subset := by intro j C cutoff transcript; split <;> simp_all
  card_le := by
    intro j C cutoff transcript
    split
    · assumption
    · rename_i hnot
      have hc := Finset.card_sdiff_add_card_eq_card (hsub j C cutoff transcript)
      have hd := hdrop j C cutoff transcript (by omega)
      omega
  preserves := by intro j C cutoff transcript hc; simp [hc]

end ForestSampling.PublicRowSelector
