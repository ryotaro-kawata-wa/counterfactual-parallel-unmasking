import ForestSampling.MatchingLaplace
import ForestSampling.HardRestriction
import ForestSampling.HardCollisionAffinity

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace PerfectMatching

variable {N : ℕ}

/-- Membership in the mate image can be tested by taking the mate once. -/
theorem mem_mate_image (M : PerfectMatching N) (S : Finset (Position N))
    (i : Position N) : i ∈ S.image M.mate ↔ M.mate i ∈ S := by
  constructor
  · rintro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    simpa [M.mate_mate _] using hj
  · intro hi
    exact Finset.mem_image.mpr ⟨M.mate i, hi, M.mate_mate i⟩

/-- The intersection of a set and its mate image counts both endpoints of
exactly its internal matching edges. -/
theorem card_inter_mate_image (M : PerfectMatching N) (S : Finset (Position N)) :
    (S ∩ S.image M.mate).card = 2 * M.internalEdgeCount S := by
  have he := M.internalEdges_eq_card S
  have hset : Finset.univ.filter (fun i ↦ i ∈ S ∧ M.mate i ∈ S) =
      S ∩ S.image M.mate := by
    ext i
    simp [M.mem_mate_image]
  have hsum : (∑ i : Position N, if i ∈ S ∧ M.mate i ∈ S then (1 : ℝ) else 0) =
      ((S ∩ S.image M.mate).card : ℝ) := by
    rw [← Finset.sum_filter, hset]
    simp
  change (∑ i : Position N, if i ∈ S ∧ M.mate i ∈ S then (1 : ℝ) else 0) / 2 =
    (M.internalEdgeCount S : ℝ) at he
  rw [hsum] at he
  have hr : ((S ∩ S.image M.mate).card : ℝ) = 2 * (M.internalEdgeCount S : ℝ) := by linarith
  exact_mod_cast hr

/-- Closing a touched set under mates adds two vertices per touched edge;
internal edges account for the double-count correction. -/
theorem card_closure_add_internal (M : PerfectMatching N) (S : Finset (Position N)) :
    (S ∪ S.image M.mate).card + 2 * M.internalEdgeCount S = 2 * S.card := by
  have h := Finset.card_union_add_card_inter S (S.image M.mate)
  rw [M.card_inter_mate_image, Finset.card_image_of_injective S M.mate_mate.injective] at h
  omega

/-- Already retired whole edges do not interact with the closure of the
still-active touched vertices. -/
theorem disjoint_active_closure (M : PerfectMatching N)
    (R S : Finset (Position N)) (hR : HardMatching.RegionClosed M R) :
    Disjoint R ((S \ R) ∪ (S \ R).image M.mate) := by
  apply Finset.disjoint_left.mpr
  intro i hi hactive
  rcases Finset.mem_union.mp hactive with hleft | hright
  · exact (Finset.mem_sdiff.mp hleft).2 hi
  · have hm := (M.mem_mate_image (S \ R) i).mp hright
    exact (Finset.mem_sdiff.mp hm).2 (hR i hi)

/-- The actual whole-edge retirement update decomposes into its old region
and the mate closure of active touched vertices. -/
theorem retirement_decomposition (M : PerfectMatching N)
    (R S : Finset (Position N)) (hR : HardMatching.RegionClosed M R) :
    R ∪ S ∪ S.image M.mate = R ∪ ((S \ R) ∪ (S \ R).image M.mate) := by
  ext i
  simp only [Finset.mem_union, M.mem_mate_image, Finset.mem_sdiff]
  constructor
  · rintro ((hi | hi) | hi)
    · exact Or.inl hi
    · by_cases hr : i ∈ R
      · exact Or.inl hr
      · exact Or.inr (Or.inl ⟨hi, hr⟩)
    · by_cases hr : M.mate i ∈ R
      · exact Or.inl (by simpa [M.mate_mate _] using hR (M.mate i) hr)
      · exact Or.inr (Or.inr ⟨hi, hr⟩)
  · rintro (hi | (hi | hi))
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi.1)
    · exact Or.inr hi.1

/-- One actual retirement increment satisfies the doubled edge ledger.
The active set is exactly the touched set outside the old retired region. -/
theorem retirement_card_ledger (M : PerfectMatching N)
    (R S : Finset (Position N)) (hR : HardMatching.RegionClosed M R) :
    (R ∪ S ∪ S.image M.mate).card + 2 * M.internalEdgeCount (S \ R) =
      R.card + 2 * (S \ R).card := by
  rw [M.retirement_decomposition R S hR,
    Finset.card_union_of_disjoint (M.disjoint_active_closure R S hR)]
  have hc := M.card_closure_add_internal (S \ R)
  omega

/-- Every mate-closed finite region contains an even number of vertices. -/
theorem card_even_of_closed (M : PerfectMatching N)
    (R : Finset (Position N)) (hR : HardMatching.RegionClosed M R) : Even R.card := by
  have himage : R.image M.mate = R := by
    ext i
    rw [M.mem_mate_image]
    exact ⟨fun hi ↦ by simpa [M.mate_mate _] using hR (M.mate i) hi, hR i⟩
  have hc := M.card_closure_add_internal R
  rw [himage, Finset.union_self] at hc
  have heq : R.card = 2 * M.internalEdgeCount R := by omega
  rw [heq]
  exact even_two_mul _

/-- The batch-edge projection type and the integer representative count
refer to exactly the same matching edges. -/
theorem internalEdgeCount_eq_batchEdge_card (M : PerfectMatching N)
    (S : Finset (Position N)) : M.internalEdgeCount S = Fintype.card (M.BatchEdge S) := by
  let e : (M.representatives.filter fun i ↦ i ∈ S ∧ M.mate i ∈ S) ≃ M.BatchEdge S :=
    { toFun := fun i ↦ ⟨⟨i.1, (Finset.mem_filter.mp i.2).1⟩, (Finset.mem_filter.mp i.2).2⟩
      invFun := fun i ↦ ⟨i.1.1, Finset.mem_filter.mpr ⟨i.1.2, i.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  simpa only [internalEdgeCount, Fintype.card_coe] using Fintype.card_congr e

/-- Enlarging a batch can only increase its number of internal matching edges. -/
theorem internalEdgeCount_mono (M : PerfectMatching N)
    {S T : Finset (Position N)} (h : S ⊆ T) :
    M.internalEdgeCount S ≤ M.internalEdgeCount T := by
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hiR, hiS, hmS⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hiR, h hiS, h hmS⟩


end PerfectMatching
end ForestSampling
