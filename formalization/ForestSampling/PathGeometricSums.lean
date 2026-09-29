import ForestSampling.FiniteProbability

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.PathGeometricSums

/-- A finite geometric run bound, including q = 1 without division by
1-q. The probability of a visible separator is q. -/
theorem geometric_range_le (N : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ k ∈ Finset.range N, (1-q)^k) ≤ 1/q := by
  have hr : 0 ≤ 1-q := by linarith
  have hgeom := geom_sum_mul_neg (1-q) N
  have hpower := pow_nonneg hr N
  have heq : 1-(1-q) = q := by ring
  rw [heq] at hgeom
  apply (le_div_iff₀ hq0).mpr
  linarith

/-- An injective set of nonnegative distances below N is bounded by the
whole length-N geometric sum. -/
theorem geometric_injective_sum_le {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (N : ℕ)
    (hinj : Set.InjOn f s) (hbound : ∀ i ∈ s, f i < N)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ i ∈ s, (1-q)^(f i)) ≤ 1/q := by
  have hsub : s.image f ⊆ Finset.range N := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (hbound i hi)
  calc
    _ = ∑ k ∈ s.image f, (1-q)^k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.range N, (1-q)^k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ pow_nonneg (by linarith) _)
    _ ≤ _ := geometric_range_le N q hq0 hq1

/-- At a fixed path coordinate, the two possible directions each contribute
at most one geometric series. No infinite path or boundary approximation
is used. -/
theorem geometric_row_le (N : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (i : Fin N) :
    (∑ j : Fin N, if i ≠ j then (1-q)^(Nat.dist i.val j.val-1) else 0) ≤ 2/q := by
  let left : Finset (Fin N) := Finset.univ.filter (fun j ↦ j.val < i.val)
  let right : Finset (Fin N) := Finset.univ.filter (fun j ↦ i.val < j.val)
  have hleft : (∑ j ∈ left, (1-q)^(i.val-j.val-1)) ≤ 1/q := by
    apply geometric_injective_sum_le left (fun j ↦ i.val-j.val-1) N _ _ q hq0 hq1
    · intro j hj k hk heq
      have hj' : j.val < i.val := (Finset.mem_filter.mp hj).2
      have hk' : k.val < i.val := (Finset.mem_filter.mp hk).2
      apply Fin.ext
      dsimp only at heq
      omega
    · intro j _
      have hi := i.isLt
      omega
  have hright : (∑ j ∈ right, (1-q)^(j.val-i.val-1)) ≤ 1/q := by
    apply geometric_injective_sum_le right (fun j ↦ j.val-i.val-1) N _ _ q hq0 hq1
    · intro j hj k hk heq
      have hj' : i.val < j.val := (Finset.mem_filter.mp hj).2
      have hk' : i.val < k.val := (Finset.mem_filter.mp hk).2
      apply Fin.ext
      dsimp only at heq
      omega
    · intro j _
      have hj := j.isLt
      omega
  have hsplit : (∑ j : Fin N, if i ≠ j then (1-q)^(Nat.dist i.val j.val-1) else 0) =
      (∑ j ∈ left, (1-q)^(i.val-j.val-1)) + (∑ j ∈ right, (1-q)^(j.val-i.val-1)) := by
    dsimp only [left, right]
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hleft : j.val < i.val
    · have hright : ¬i.val < j.val := by omega
      have hne : i ≠ j := by intro h; subst j; omega
      simp [hleft, hright, hne, Nat.dist_eq_sub_of_le_right hleft.le]
    · by_cases hright : i.val < j.val
      · have hne : i ≠ j := by intro h; subst j; omega
        simp [hleft, hright, hne, Nat.dist_eq_sub_of_le hright.le]
      · have heq : i = j := Fin.ext (by omega)
        subst j
        simp
  rw [hsplit]
  exact (add_le_add hleft hright).trans_eq (by ring)

/-- The actual finite ordered-pair geometric sum on a length-N path is
at most 2N/q, uniformly including short paths and q = 1. -/
theorem ordered_geometric_sum_le (N : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ i : Fin N, ∑ j : Fin N,
      if i ≠ j then (1-q)^(Nat.dist i.val j.val-1) else 0) ≤ 2*(N : ℝ)/q := by
  calc
    _ ≤ ∑ _i : Fin N, 2/q := Finset.sum_le_sum (fun i _ ↦ geometric_row_le N q hq0 hq1 i)
    _ = _ := by simp; ring

/-- The same estimate with the diagonal removed by a finite filter. -/
theorem ordered_geometric_filter_sum_le (N : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ j ≠ i),
      (1-q)^(Nat.dist i.val j.val-1)) ≤ 2*(N : ℝ)/q := by
  simpa only [Finset.sum_filter, ne_comm] using ordered_geometric_sum_le N q hq0 hq1

/-- An ordered pair of adjacent vertices whose two coordinates are both
strictly interior to the finite path. -/
def InteriorAdjacent {N : ℕ} (i j : Fin N) : Prop :=
  Nat.dist i.val j.val = 1 ∧ 0 < i.val ∧ i.val < N-1 ∧ 0 < j.val ∧ j.val < N-1

instance {N : ℕ} (i j : Fin N) : Decidable (InteriorAdjacent i j) := by
  unfold InteriorAdjacent
  infer_instance

/-- Increasing interior edges, with endpoints written in their path order. -/
def forwardInteriorPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p ↦ p.1.val+1 = p.2.val ∧ 0 < p.1.val ∧ p.2.val < N-1)

/-- Decreasing interior edges are retained as separate ordered pairs. -/
def backwardInteriorPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p ↦ p.2.val+1 = p.1.val ∧ 0 < p.2.val ∧ p.1.val < N-1)

/-- The increasing interior edges correspond exactly to k+1,k+2 with
k in Fin(N-3), including the empty cases N <= 3. -/
theorem forwardInteriorPairs_card (N : ℕ) : (forwardInteriorPairs N).card = N-3 := by
  have hcard : (Finset.univ : Finset (Fin (N-3))).card = (forwardInteriorPairs N).card := by
    apply Finset.card_bij (fun k _ ↦
      (⟨k.val+1, by have hk := k.isLt; omega⟩, ⟨k.val+2, by have hk := k.isLt; omega⟩))
    · intro k _
      have hk := k.isLt
      simp only [forwardInteriorPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro k _ l _ heq
      have hfirst := congrArg (fun p : Fin N × Fin N ↦ p.1.val) heq
      apply Fin.ext
      dsimp only at hfirst
      omega
    · intro p hp
      simp only [forwardInteriorPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      let k : Fin (N-3) := ⟨p.1.val-1, by omega⟩
      refine ⟨k, Finset.mem_univ _, ?_⟩
      apply Prod.ext <;> apply Fin.ext <;> dsimp only [k] <;> omega
  simpa using hcard.symm

/-- Reversing the endpoints bijects the two orientations. -/
theorem backwardInteriorPairs_card (N : ℕ) : (backwardInteriorPairs N).card = N-3 := by
  have hcard : (backwardInteriorPairs N).card = (forwardInteriorPairs N).card := by
    apply Finset.card_bij (fun p _ ↦ (p.2, p.1))
    · intro p hp
      simpa only [backwardInteriorPairs, forwardInteriorPairs, Finset.mem_filter,
        Finset.mem_univ, true_and] using hp
    · intro p _ r _ heq
      exact Prod.swap_injective heq
    · intro p hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      simpa only [backwardInteriorPairs, forwardInteriorPairs, Finset.mem_filter,
        Finset.mem_univ, true_and] using hp
  exact hcard.trans (forwardInteriorPairs_card N)

/-- Adjacent interior pairs split into two disjoint orientations. -/
theorem interiorAdjacentPairs_eq_union (N : ℕ) :
    Finset.univ.filter (fun p : Fin N × Fin N ↦ InteriorAdjacent p.1 p.2) =
      forwardInteriorPairs N ∪ backwardInteriorPairs N := by
  ext p
  simp only [forwardInteriorPairs, backwardInteriorPairs, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union]
  unfold InteriorAdjacent Nat.dist
  omega

/-- Exact finite ordered count used for the adjacent-pair lower bound. -/
theorem interiorAdjacentPairs_card (N : ℕ) :
    (Finset.univ.filter (fun p : Fin N × Fin N ↦ InteriorAdjacent p.1 p.2)).card = 2*(N-3) := by
  have hdisjoint : Disjoint (forwardInteriorPairs N) (backwardInteriorPairs N) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [forwardInteriorPairs, backwardInteriorPairs, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp hq
    omega
  rw [interiorAdjacentPairs_eq_union, Finset.card_union_of_disjoint hdisjoint,
    forwardInteriorPairs_card, backwardInteriorPairs_card]
  omega

/-- A sum-of-indicators version avoids changing the pair indexing in
masking expectation calculations. -/
theorem interiorAdjacent_indicator_sum (N : ℕ) :
    (∑ i : Fin N, ∑ j : Fin N, if InteriorAdjacent i j then (1 : ℝ) else 0) =
      2*((N-3 : ℕ) : ℝ) := by
  have hsum : (∑ p : Fin N × Fin N, if InteriorAdjacent p.1 p.2 then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun p : Fin N × Fin N ↦ InteriorAdjacent p.1 p.2)).card : ℝ) := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Fintype.sum_prod_type] at hsum
  rw [hsum, interiorAdjacentPairs_card]
  norm_num

end ForestSampling.PathGeometricSums
