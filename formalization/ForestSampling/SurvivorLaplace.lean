import ForestSampling.SurvivorQuery
import ForestSampling.MatchingLaplace

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

namespace MatchingOn

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Restriction to a closed region preserves the internal-edge count of any
set lying entirely in that region. -/
theorem internalEdges_restrict (M : MatchingOn A) (P : A → Prop) [DecidablePred P]
    (hP : M.Closed P) (S : Finset A) (hS : ∀ a ∈ S, P a) :
    (M.restrict P hP).internalEdges (S.subtype P) = M.internalEdges S := by
  unfold internalEdges
  rw [← Fintype.sum_subtype_add_sum_subtype P]
  have hz : (∑ a : {a // ¬ P a},
      if a.1 ∈ S ∧ M.mate a.1 ∈ S then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have ha : a.1 ∉ S := fun ha ↦ a.2 (hS a.1 ha)
    simp [ha]
  rw [hz, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp [restrict]

/-- The fixed Laplace parameter one loses at least half of the unit mass. -/
theorem half_le_one_sub_exp_neg_one : (1 / 2 : ℝ) ≤ 1 - Real.exp (-1) := by
  have h := Real.add_one_le_exp (1 : ℝ)
  have hmul : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hp := Real.exp_nonneg (-1)
  nlinarith

variable [Nonempty (MatchingOn A)]

/-- The actual uniform matching count pays for the paper's one-step
compensation, including zero or one remaining vertex without a division gap. -/
theorem uniform_internalEdges_compensated (S : Finset A) :
    (FinDist.uniform (MatchingOn A)).expectation
      (fun M ↦ Real.exp (-M.internalEdges S +
        ((S.card - 1 : ℕ) : ℝ) ^ 2 / (Fintype.card A : ℝ) / 64)) ≤ 1 := by
  classical
  by_cases hn : 2 ≤ Fintype.card A
  · let c : ℝ := ((S.card - 1 : ℕ) : ℝ) ^ 2 / (Fintype.card A : ℝ) / 64
    have hbase := internalLaplace_le_exp S 1 (by norm_num) hn
    have hcomp : c ≤ (1 - Real.exp (-1)) * ((S.card - 1 : ℕ) : ℝ) ^ 2 /
        (32 * (Fintype.card A : ℝ)) := by
      calc
        c = (1 / 2 : ℝ) * ((S.card - 1 : ℕ) : ℝ) ^ 2 /
            (32 * (Fintype.card A : ℝ)) := by dsimp [c]; ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right half_le_one_sub_exp_neg_one (sq_nonneg _)) (by positivity)
    have hbound : internalLaplace S 1 ≤ Real.exp (-c) :=
      hbase.trans (Real.exp_le_exp.mpr (neg_le_neg hcomp))
    calc
      _ = internalLaplace S 1 * Real.exp c := by
        change (FinDist.uniform (MatchingOn A)).expectation
          (fun M ↦ Real.exp (-M.internalEdges S + c)) = internalLaplace S 1 * Real.exp c
        unfold internalLaplace FinDist.expectation
        simp only [neg_one_mul, Real.exp_add]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro M _
        ring
      _ ≤ Real.exp (-c) * Real.exp c :=
        mul_le_mul_of_nonneg_right hbound (Real.exp_nonneg c)
      _ = 1 := by rw [← Real.exp_add]; simp
  · have hk := Finset.card_le_univ S
    have hz : S.card - 1 = 0 := by omega
    simpa only [internalLaplace, hz, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
      zero_div, add_zero, neg_one_mul] using internalLaplace_le_one S 1 (by norm_num)

end MatchingOn

namespace HardMatching.SurvivorRecord

variable {N K : ℕ}

/-- The committed batch labels that still belong to the hidden survivor region. -/
def activeSurvivors (r : SurvivorRecord N K) (batch : Finset (Position N)) :
    Finset r.Survivor := batch.subtype (fun i ↦ i ∉ r.retired)

/-- Counting the survivor subtype agrees with deleting retired original labels. -/
theorem activeSurvivors_card (r : SurvivorRecord N K) (batch : Finset (Position N)) :
    (r.activeSurvivors batch).card = (batch \ r.retired).card := by
  rw [activeSurvivors, Finset.card_subtype]
  congr 1
  ext i
  simp

/-- The survivor type has exactly the number of labels not yet retired. -/
theorem survivor_card (r : SurvivorRecord N K) :
    Fintype.card r.Survivor = N - r.retired.card := by
  simp [Survivor, Fintype.card_subtype_compl]

/-- Restricting a compatible full matching retains exactly the internal edges
of the active batch, with the manuscript's original-label integer count. -/
theorem internalEdges_fiber (r : SurvivorRecord N K)
    (I : {I : InstanceIndex N K // r.Compatible I}) (batch : Finset (Position N)) :
    (r.fiberEquiv I).1.internalEdges (r.activeSurvivors batch) =
      (I.1.1.internalEdgeCount (batch \ r.retired) : ℝ) := by
  classical
  rw [← PerfectMatching.internalEdges_eq_card]
  let M := (MatchingOn.finEquiv N).symm I.1.1
  have hP : M.Closed (fun i ↦ i ∉ r.retired) := M.closed_compl _ I.2.1.closed
  have hrestrict := M.internalEdges_restrict (fun i ↦ i ∉ r.retired) hP
    (batch \ r.retired) (fun i hi ↦ (Finset.mem_sdiff.mp hi).2)
  have hset : (batch \ r.retired).subtype (fun i ↦ i ∉ r.retired) = r.activeSurvivors batch := by
    ext i
    simp [activeSurvivors, i.2]
  rw [hset] at hrestrict
  exact hrestrict

/-- The actual uniform compatible-instance fiber pays for one commit's
collision compensation. Only still-active original batch labels are counted. -/
theorem uniform_fiber_commit_compensated (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}]
    (batch : Finset (Position N)) :
    (FinDist.uniform {I : InstanceIndex N K // r.Compatible I}).expectation
      (fun I ↦ Real.exp (-(I.1.1.internalEdgeCount (batch \ r.retired) : ℝ) +
        (((batch \ r.retired).card - 1 : ℕ) : ℝ) ^ 2 /
          ((N - r.retired.card : ℕ) : ℝ) / 64)) ≤ 1 := by
  classical
  let : Nonempty (MatchingOn r.Survivor) := ⟨(Classical.choice r.state_nonempty).1⟩
  have h := MatchingOn.uniform_internalEdges_compensated (r.activeSurvivors batch)
  rw [← r.uniform_fiber_map_matching, FinDist.expectation_map] at h
  simpa only [Function.comp_def, internalEdges_fiber, activeSurvivors_card, survivor_card] using h

/-- The same concrete compensation bound under the record's full-instance
extension law, convenient for adaptive evaluator disintegration. -/
theorem uniform_extensions_commit_compensated (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}]
    (batch : Finset (Position N)) :
    r.uniformExtensions.expectation
      (fun I ↦ Real.exp (-(I.1.internalEdgeCount (batch \ r.retired) : ℝ) +
        (((batch \ r.retired).card - 1 : ℕ) : ℝ) ^ 2 /
          ((N - r.retired.card : ℕ) : ℝ) / 64)) ≤ 1 := by
  rw [uniformExtensions, FinDist.expectation_map]
  exact r.uniform_fiber_commit_compensated batch

end HardMatching.SurvivorRecord

end ForestSampling
