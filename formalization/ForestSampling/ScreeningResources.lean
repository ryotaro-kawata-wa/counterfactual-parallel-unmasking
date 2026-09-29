import ForestSampling.ScreeningAggregate
import ForestSampling.QuerySchedule

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace Screening

namespace OrderedChunk

variable {α : Type*} [LinearOrder α]

/-- Public zero-based rank inside an ordered finite set. -/
def rank (s : Finset α) (a : α) : ℕ := (s.filter (· < a)).card

theorem rank_lt_card (s : Finset α) (a : α) (ha : a ∈ s) : rank s a < s.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have hmem : a ∈ s.filter (· < a) := heq.symm ▸ ha
  simpa using (Finset.mem_filter.mp hmem).2

theorem rank_strictMono (s : Finset α) {a b : α} (ha : a ∈ s) (hab : a < b) :
    rank s a < rank s b := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
      ((Finset.mem_filter.mp hx).2).trans hab⟩
  · intro heq
    have hmem : a ∈ s.filter (· < b) := Finset.mem_filter.mpr ⟨ha, hab⟩
    rw [← heq] at hmem
    simpa using (Finset.mem_filter.mp hmem).2

theorem rank_injOn (s : Finset α) : Set.InjOn (rank s) (s : Set α) := by
  intro a ha b hb heq
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim ((rank_strictMono s ha hab).ne heq)
  · exact hab
  · exact False.elim ((rank_strictMono s hb hab).ne heq.symm)

/-- Equal rank quotients make rank remainders an injection into `Fin q`.
Consequently every consecutive rank chunk has at most q vertices. -/
theorem quotient_chunk_card_le (s : Finset α) (q k : ℕ) (hq : 0 < q) :
    (s.filter (fun a ↦ rank s a / q = k)).card ≤ q := by
  let chunk := s.filter (fun a ↦ rank s a / q = k)
  let f : chunk → Fin q := fun a ↦ ⟨rank s a % q, Nat.mod_lt _ hq⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hmod : rank s a.val % q = rank s b.val % q := congrArg Fin.val hab
    have hdiva : rank s a.val / q = k := (Finset.mem_filter.mp a.property).2
    have hdivb : rank s b.val / q = k := (Finset.mem_filter.mp b.property).2
    have hdecompa := Nat.mod_add_div (rank s a.val) q
    have hdecompb := Nat.mod_add_div (rank s b.val) q
    apply Subtype.ext
    apply rank_injOn s (Finset.mem_filter.mp a.property).1
      (Finset.mem_filter.mp b.property).1
    rw [hdiva] at hdecompa
    rw [hdivb] at hdecompb
    omega
  simpa [chunk] using Fintype.card_le_of_injective f hinj

end OrderedChunk

variable {N : ℕ} {V Color : Type*} [Fintype V] [DecidableEq V]
variable [Fintype Color] [DecidableEq Color]

/-- Actual nonempty chunk keys; no chunk is generated for an empty class
or for a quotient not attained by a residual position. -/
def chunkKeys (h : History N V) (color : Position N → Color) (q : ℕ) : Finset (Color × ℕ) :=
  h.uncommitted.image (fun j ↦ (color j, colorRank h color j / q))

def keyChunk (h : History N V) (color : Position N → Color) (q : ℕ)
    (key : Color × ℕ) : Finset (Position N) :=
  h.uncommitted.filter (fun j ↦ color j = key.1 ∧ colorRank h color j / q = key.2)

omit [Fintype V] [DecidableEq V] [Fintype Color] in
theorem keyChunk_eq_orderedChunk (h : History N V) (color : Position N → Color)
    (q : ℕ) (key : Color × ℕ) :
    keyChunk h color q key = (colorClass h color key.1).filter
      (fun a ↦ OrderedChunk.rank (colorClass h color key.1) a / q = key.2) := by
  ext a
  constructor
  · intro ha
    obtain ⟨har, hc, hr⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨har, hc⟩, ?_⟩
    simpa only [OrderedChunk.rank, colorRank, hc] using hr
  · intro ha
    obtain ⟨har, hr⟩ := Finset.mem_filter.mp ha
    obtain ⟨ham, hc⟩ := Finset.mem_filter.mp har
    apply Finset.mem_filter.mpr
    refine ⟨ham, hc, ?_⟩
    simpa only [OrderedChunk.rank, colorRank, hc] using hr

omit [Fintype V] [DecidableEq V] [Fintype Color] in
theorem keyChunk_card_le (h : History N V) (color : Position N → Color)
    (q : ℕ) (hq : 0 < q) (key : Color × ℕ) : (keyChunk h color q key).card ≤ q := by
  rw [keyChunk_eq_orderedChunk]
  exact OrderedChunk.quotient_chunk_card_le _ q key.2 hq

omit [Fintype V] [Fintype Color] in
theorem readoutChunk_eq_keyChunk (h : History N V) (color : Position N → Color)
    (q : ℕ) (j : ResidualVertex h) :
    readoutChunk h color q j = keyChunk h color q (color j, colorRank h color j / q) := by
  ext a
  simp [readoutChunk, keyChunk, colorClass, and_assoc]

omit [Fintype V] [Fintype Color] in
theorem readoutChunk_card_le (h : History N V) (color : Position N → Color)
    (q : ℕ) (hq : 0 < q) (j : ResidualVertex h) :
    (readoutChunk h color q j).card ≤ q := by
  rw [readoutChunk_eq_keyChunk]
  exact keyChunk_card_le h color q hq _

omit [Fintype V] [DecidableEq V] [Fintype Color] in
theorem keyChunk_nonempty (h : History N V) (color : Position N → Color)
    (q : ℕ) (key : chunkKeys h color q) : (keyChunk h color q key).Nonempty := by
  obtain ⟨j, hj, hkey⟩ := Finset.mem_image.mp key.property
  refine ⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
  have hc := congrArg Prod.fst hkey
  have hr := congrArg Prod.snd hkey
  exact ⟨hc, hr⟩

omit [Fintype V] [DecidableEq V] [Fintype Color] in
theorem keyChunk_subset (h : History N V) (color : Position N → Color)
    (q : ℕ) (key : Color × ℕ) : keyChunk h color q key ⊆ h.uncommitted :=
  Finset.filter_subset _ _

omit [Fintype V] [DecidableEq V] in
theorem chunkKeys_card_le_sum (h : History N V) (color : Position N → Color) (q : ℕ) :
    (chunkKeys h color q).card ≤ ∑ c : Color, ((colorClass h color c).card / q + 1) := by
  let cover := Finset.univ.biUnion (fun c : Color ↦
    Finset.image (fun k : ℕ ↦ (c, k)) (Finset.range ((colorClass h color c).card / q + 1)))
  have hsubset : chunkKeys h color q ⊆ cover := by
    intro key hkey
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hkey
    apply Finset.mem_biUnion.mpr
    refine ⟨color j, Finset.mem_univ _, Finset.mem_image.mpr ⟨colorRank h color j / q, ?_, rfl⟩⟩
    apply Finset.mem_range.mpr
    have hr : colorRank h color j < (colorClass h color (color j)).card :=
      OrderedChunk.rank_lt_card _ j (by simp [colorClass, hj])
    have hd : colorRank h color j / q ≤ (colorClass h color (color j)).card / q :=
      Nat.div_le_div_right (le_of_lt hr)
    omega
  apply (Finset.card_le_card hsubset).trans
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro c _
  exact (Finset.card_image_le).trans_eq (Finset.card_range _)

omit [Fintype V] [DecidableEq V] in
theorem sum_colorClass_card (h : History N V) (color : Position N → Color) :
    (∑ c : Color, (colorClass h color c).card) = h.uncommitted.card := by
  simp only [colorClass, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

omit [Fintype V] [DecidableEq V] in
/-- The total number of nonempty chunks obeys the packed-screen count,
including the at-most-one remainder chunk for each color class. -/
theorem chunkKeys_card_le (h : History N V) (color : Position N → Color)
    (q : ℕ) (hq : 0 < q) :
    (chunkKeys h color q).card ≤ h.uncommitted.card / q + Fintype.card Color := by
  apply (chunkKeys_card_le_sum h color q).trans
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  apply Nat.add_le_add_right
  apply (Nat.le_div_iff_mul_le hq).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ c : Color, (colorClass h color c).card :=
      Finset.sum_le_sum (fun c _ ↦ Nat.div_mul_le_self _ _)
    _ = _ := sum_colorClass_card h color

end Screening
end ForestSampling
