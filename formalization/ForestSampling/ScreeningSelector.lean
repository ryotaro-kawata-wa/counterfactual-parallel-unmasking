import ForestSampling.ScreeningAggregate

set_option autoImplicit false

namespace ForestSampling
namespace PublicRowSelector

variable {α Transcript : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- Scores sort in decreasing order and positions break ties in increasing
public order, exactly as in the standard top-vote selector. -/
def voteKey (score : α → ℕ) (a : α) : OrderDual ℕ ×ₗ α := toLex (OrderDual.toDual (score a), a)

omit [Fintype α] [DecidableEq α] [LinearOrder α] in
theorem voteKey_injective (score : α → ℕ) : Function.Injective (voteKey score) := by
  intro a b hab
  exact congrArg (fun x : OrderDual ℕ ×ₗ α ↦ (ofLex x).2) hab

/-- Public sorted score/position keys for a candidate row. -/
def sortedVoteKeys (score : α → ℕ) (C : Finset α) : List (OrderDual ℕ ×ₗ α) :=
  (C.image (voteKey score)).sort (· ≤ ·)

/-- Keep the first `cutoff` candidates in descending-vote order. -/
def topVotes (score : α → ℕ) (C : Finset α) (cutoff : ℕ) : Finset α :=
  (((sortedVoteKeys score C).take cutoff).map (fun x ↦ (ofLex x).2)).toFinset

omit [Fintype α] in
theorem topVotes_subset (score : α → ℕ) (C : Finset α) (cutoff : ℕ) :
    topVotes score C cutoff ⊆ C := by
  intro a ha
  simp only [topVotes, List.mem_toFinset, List.mem_map] at ha
  obtain ⟨key, hkey, hread⟩ := ha
  have hmem := List.mem_of_mem_take hkey
  rw [sortedVoteKeys, Finset.mem_sort] at hmem
  obtain ⟨b, hb, hkeyeq⟩ := Finset.mem_image.mp hmem
  have hba : b = a := by
    simpa [← hkeyeq, voteKey] using hread
  exact hba ▸ hb

omit [Fintype α] in
theorem topVotes_card_le (score : α → ℕ) (C : Finset α) (cutoff : ℕ) :
    (topVotes score C cutoff).card ≤ cutoff := by
  apply (List.toFinset_card_le (l := _)).trans
  rw [List.length_map]
  exact List.length_take_le cutoff _

omit [Fintype α] in
theorem topVotes_preserves (score : α → ℕ) (C : Finset α) (cutoff : ℕ)
    (hcap : C.card ≤ cutoff) : topVotes score C cutoff = C := by
  have hlength : (sortedVoteKeys score C).length ≤ cutoff := by
    simpa [sortedVoteKeys, Finset.card_image_of_injective _ (voteKey_injective score)] using hcap
  unfold topVotes
  rw [List.take_of_length_le hlength]
  ext a
  simp only [List.mem_toFinset, List.mem_map, sortedVoteKeys, Finset.mem_sort]
  constructor
  · rintro ⟨key, hkey, hread⟩
    obtain ⟨b, hb, hkeyeq⟩ := Finset.mem_image.mp hkey
    have hba : b = a := by simpa [← hkeyeq, voteKey] using hread
    exact hba ▸ hb
  · intro ha
    exact ⟨voteKey score a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, rfl⟩

/-- The standard top-vote selector, parameterized only by the public score
computed from the completed transcript. -/
def standardTopVotes (score : Transcript → α → α → ℕ) : PublicRowSelector α Transcript where
  choose := fun j C cutoff transcript ↦ topVotes (score transcript j) C cutoff
  subset := fun j C cutoff transcript ↦ topVotes_subset (score transcript j) C cutoff
  card_le := fun j C cutoff transcript ↦ topVotes_card_le (score transcript j) C cutoff
  preserves := fun j C cutoff transcript ↦ topVotes_preserves (score transcript j) C cutoff

end PublicRowSelector
end ForestSampling
