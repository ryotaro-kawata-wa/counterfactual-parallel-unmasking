import ForestSampling.SurvivorProcess

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

/-- The uniform law on a finite Cartesian product is the product of uniforms. -/
theorem uniform_prod {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] :
    uniform (α × β) = (uniform α).prod (uniform β) := by
  ext x
  simp [uniform_apply, prod_apply, Fintype.card_prod, Nat.cast_mul, mul_comm]

/-- The uniform law on a finite dependent function space factors by coordinate. -/
theorem uniform_piProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] :
    uniform (∀ i, Ω i) = piProduct (fun i ↦ uniform (Ω i)) := by
  ext x
  simp [uniform_apply, piProduct_apply, Fintype.card_pi,
    Nat.cast_prod, Finset.prod_inv_distrib]

/-- The second marginal of an independent binary product. -/
theorem prod_map_second {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (p : FinDist α) (q : FinDist β) :
    (p.prod q).map Prod.snd = q := by
  ext b
  rw [map_apply, Fintype.sum_prod_type]
  simp only [prod_apply]
  have hi (a : α) : (∑ c, if c = b then p a * q c else 0) = p a * q b :=
    Fintype.sum_ite_eq' _ _
  simp_rw [hi]
  rw [← Finset.sum_mul, p.sum_mass, one_mul]

end FinDist

namespace HardMatching.SurvivorRecord

variable {N K backgroundSize : ℕ}

/-- A displayed candidate deletes that one label from every survivor's old set. -/
theorem queryCandidates_eq_erase (r : SurvivorRecord N K)
    (y : MaskedState N (HardVocabulary K backgroundSize)) (i : Position N)
    (c : Fin K) (hy : y i = some (Sum.inl c)) :
    r.queryCandidates y i = (r.candidates i).erase c := by
  ext a
  simp [queryCandidates, hy, Finset.mem_erase, and_comm, eq_comm]

/-- A mask or a background label excludes no candidate. -/
theorem queryCandidates_eq_of_no_candidate (r : SurvivorRecord N K)
    (y : MaskedState N (HardVocabulary K backgroundSize)) (i : Position N)
    (hy : ∀ c : Fin K, y i ≠ some (Sum.inl c)) :
    r.queryCandidates y i = r.candidates i := by
  ext a
  simp [queryCandidates, hy]

/-- One actual state submission can remove at most one candidate per source. -/
theorem card_queryCandidates_add_one_ge (r : SurvivorRecord N K)
    (y : MaskedState N (HardVocabulary K backgroundSize)) (i : Position N) :
    (r.candidates i).card ≤ (r.queryCandidates y i).card + 1 := by
  cases hy : y i with
  | none =>
      rw [r.queryCandidates_eq_of_no_candidate y i (by intro c; simp [hy])]
      omega
  | some a =>
      cases a with
      | inr b =>
          rw [r.queryCandidates_eq_of_no_candidate y i (by intro c; simp [hy])]
          omega
      | inl c =>
          rw [r.queryCandidates_eq_erase y i c hy]
          by_cases hc : c ∈ r.candidates i
          · rw [Finset.card_erase_of_mem hc]
            have hcard := Finset.card_pos.mpr ⟨c, hc⟩
            omega
          · rw [Finset.erase_eq_of_notMem hc]
            omega

noncomputable section

/-- Every candidate set at a surviving position is nonempty on a nonempty
record fiber; the witness is the actual compatible instance's trigger. -/
theorem candidate_nonempty (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}] (i : r.Survivor) :
    Nonempty {c : Fin K // c ∈ r.candidates i.1} := by
  obtain ⟨I⟩ := ‹Nonempty {I : InstanceIndex N K // r.Compatible I}›
  exact ⟨⟨I.1.2 i.1, I.2.2.2 i.1 i.2⟩⟩

/-- The law of the surviving trigger candidates, viewed as original bank labels. -/
def survivorTriggerLaw (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}] (i : r.Survivor) : FinDist (Fin K) := by
  let := r.candidate_nonempty i
  exact (FinDist.uniform {c : Fin K // c ∈ r.candidates i.1}).map Subtype.val

/-- A surviving private trigger is exactly uniform on its remaining candidates
under the compatible-instance uniform law. This uses the full record-fiber
bijection, so no independence premise is assumed. -/
theorem uniform_fiber_map_trigger (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}] (i : r.Survivor) :
    (FinDist.uniform {I : InstanceIndex N K // r.Compatible I}).map (fun I ↦ I.1.2 i.1) =
      r.survivorTriggerLaw i := by
  let : Nonempty r.State := r.state_nonempty
  let : Nonempty (MatchingOn r.Survivor) :=
    ⟨(Classical.choice (inferInstance : Nonempty r.State)).1⟩
  let : ∀ j : r.Survivor, Nonempty {c : Fin K // c ∈ r.candidates j.1} :=
    r.candidate_nonempty
  have hstate := r.uniform_fiber_map_state
  calc
    _ = ((FinDist.uniform {I : InstanceIndex N K // r.Compatible I}).map r.fiberEquiv).map
        (fun state ↦ (state.2 i).1) := by
      rw [FinDist.map_comp]
      rfl
    _ = (FinDist.uniform r.State).map (fun state ↦ (state.2 i).1) := by rw [hstate]
    _ = (((FinDist.uniform (MatchingOn r.Survivor)).prod
        (FinDist.piProduct (fun j : r.Survivor ↦
          FinDist.uniform {c : Fin K // c ∈ r.candidates j.1}))).map Prod.snd).map
        (fun z ↦ (z i).1) := by
      rw [FinDist.map_comp, ← FinDist.uniform_piProduct, ← FinDist.uniform_prod]
      rfl
    _ = ((FinDist.piProduct (fun j : r.Survivor ↦
        FinDist.uniform {c : Fin K // c ∈ r.candidates j.1})).map (fun z ↦ z i)).map
        Subtype.val := by
      rw [FinDist.prod_map_second, FinDist.map_comp]
      rfl
    _ = _ := by rw [FinDist.piProduct_map_eval]; rfl

/-- The surviving matching marginal is exactly uniform after any realizable record. -/
theorem uniform_fiber_map_matching (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}] :
    letI : Nonempty (MatchingOn r.Survivor) :=
      ⟨(Classical.choice r.state_nonempty).1⟩
    (FinDist.uniform {I : InstanceIndex N K // r.Compatible I}).map
      (fun I ↦ (r.fiberEquiv I).1) = FinDist.uniform (MatchingOn r.Survivor) := by
  let : Nonempty r.State := r.state_nonempty
  let : Nonempty (MatchingOn r.Survivor) := ⟨(Classical.choice r.state_nonempty).1⟩
  let : Nonempty (∀ i : r.Survivor, {c : Fin K // c ∈ r.candidates i.1}) :=
    ⟨(Classical.choice r.state_nonempty).2⟩
  calc
    _ = ((FinDist.uniform {I : InstanceIndex N K // r.Compatible I}).map r.fiberEquiv).map
        Prod.fst := by rw [FinDist.map_comp]; rfl
    _ = (FinDist.uniform r.State).map Prod.fst := by rw [r.uniform_fiber_map_state]
    _ = _ := by rw [FinDist.uniform_prod, FinDist.prod_map_first]

/-- The exact mass of any original bank label in the remaining-candidate law. -/
theorem survivorTriggerLaw_apply (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}] (i : r.Survivor) (c : Fin K) :
    r.survivorTriggerLaw i c =
      if c ∈ r.candidates i.1 then ((r.candidates i.1).card : ℝ)⁻¹ else 0 := by
  classical
  change (∑ a : {c : Fin K // c ∈ r.candidates i.1},
      if a.1 = c then (Fintype.card {c : Fin K // c ∈ r.candidates i.1} : ℝ)⁻¹ else 0) = _
  by_cases hc : c ∈ r.candidates i.1
  · rw [Finset.sum_eq_single ⟨c, hc⟩]
    · simp [hc]
    · intro a _ ha
      rw [if_neg]
      exact fun h ↦ ha (Subtype.ext h)
    · simp
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg]
    exact fun h ↦ hc (h ▸ a.2)

/-- An arbitrary query tests one label at a surviving source, so its hit
probability under the exact compatible fiber is at most the reciprocal of
the number of remaining candidates. Repeated tests and background values
are covered without an independence assumption across different sources. -/
theorem uniform_fiber_hit_probability_le (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}]
    (y : MaskedState N (HardVocabulary K backgroundSize)) (i : r.Survivor) :
    (FinDist.uniform {I : InstanceIndex N K // r.Compatible I}).eventMass
      (fun I ↦ y i.1 = some (Sum.inl (I.1.2 i.1))) ≤
      ((r.candidates i.1).card : ℝ)⁻¹ := by
  classical
  let E (c : Fin K) := y i.1 = some (Sum.inl c)
  have hmap := FinDist.map_eventMass
    (FinDist.uniform {I : InstanceIndex N K // r.Compatible I}) (fun I ↦ I.1.2 i.1) E
  rw [r.uniform_fiber_map_trigger i] at hmap
  have hsame := (FinDist.uniform {I : InstanceIndex N K // r.Compatible I}).eventMass_congr
    (fun I ↦ y i.1 = some (Sum.inl (I.1.2 i.1))) (E ∘ fun I ↦ I.1.2 i.1)
    (fun _ ↦ Iff.rfl)
  rw [hsame, ← hmap]
  by_cases hc : ∃ c : Fin K, y i.1 = some (Sum.inl c)
  · obtain ⟨c, hy⟩ := hc
    have hm : (r.survivorTriggerLaw i).eventMass E = r.survivorTriggerLaw i c := by
      unfold FinDist.eventMass
      simp only [E, hy, Option.some.injEq, Sum.inl.injEq]
      exact Fintype.sum_ite_eq _ _
    rw [hm, r.survivorTriggerLaw_apply]
    split
    · exact le_rfl
    · positivity
  · have hz : (r.survivorTriggerLaw i).eventMass E = 0 := by
      unfold FinDist.eventMass
      apply Finset.sum_eq_zero
      intro c _
      exact if_neg (fun h ↦ hc ⟨c, h⟩)
    rw [hz]
    positivity

/-- When fewer than K queries have occurred, a candidate-count lower bound
turns the exact static hazard into the paper's reciprocal remaining-bank bound. -/
theorem uniform_fiber_hit_probability_le_remaining (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}]
    (y : MaskedState N (HardVocabulary K backgroundSize)) (i : r.Survivor)
    (q : ℕ) (hq : q < K) (hcard : K - q ≤ (r.candidates i.1).card) :
    (FinDist.uniform {I : InstanceIndex N K // r.Compatible I}).eventMass
      (fun I ↦ y i.1 = some (Sum.inl (I.1.2 i.1))) ≤
      ((K - q : ℕ) : ℝ)⁻¹ := by
  apply (r.uniform_fiber_hit_probability_le y i).trans
  have hpos : (0 : ℝ) < ((K - q : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hq
  have hle : ((K - q : ℕ) : ℝ) ≤ ((r.candidates i.1).card : ℝ) := by exact_mod_cast hcard
  simpa only [one_div] using one_div_le_one_div_of_le hpos hle

end
end HardMatching.SurvivorRecord
end ForestSampling
