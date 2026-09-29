import ForestSampling.HardRestriction

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling

namespace FinDist

/-- Conditioning a uniform finite law and then using an explicit equivalence
of its whole event fiber gives the uniform law on the target fiber. -/
theorem uniform_conditionalMap_equiv {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Nonempty α] [Nonempty β] (E : α → Prop) [DecidablePred E]
    [Nonempty {a // E a}] (e : {a // E a} ≃ β)
    (f : α → γ) (g : β → γ) (hf : ∀ a, f a.1 = g (e a))
    (hE : 0 < (uniform α).eventMass E) :
    (uniform α).conditionalMap E hE f = (uniform β).map g := by
  rw [conditionalMap, uniform_conditionOn_eq_map_subtype, map_comp]
  calc
    _ = ((uniform {a // E a}).map e).map g := by
      rw [map_comp]
      congr 1
      funext a
      exact hf a
    _ = _ := by rw [uniform_map_equiv]

/-- A constant conditional kernel has its stated observation marginal. -/
theorem sigmaJoint_constant_eventMass_snd {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] (p : FinDist α) (q : FinDist β) (z : β) :
    (sigmaJoint p (fun _ ↦ q)).eventMass (fun w ↦ w.2 = z) = q z := by
  classical
  unfold eventMass
  rw [Fintype.sum_sigma]
  simp only [sigmaJoint_apply]
  have hinner (a : α) : (∑ b, if b = z then p a * q b else 0) = p a * q z := by
    exact Fintype.sum_ite_eq' _ _
  simp_rw [hinner]
  rw [← Finset.sum_mul, p.sum_mass, one_mul]

/-- Observing the second coordinate of an independent retained pair leaves
the first law unchanged. The positive likelihood is normalized explicitly. -/
theorem sigmaJoint_constant_observation_posterior {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : FinDist α) (q : FinDist β) (z : β) (hq : 0 < q z) :
    (sigmaJoint p (fun _ ↦ q)).conditionalMap (fun w ↦ w.2 = z)
      (by rw [sigmaJoint_constant_eventMass_snd]; exact hq) Sigma.fst = p := by
  classical
  ext a
  rw [conditionalMap_apply_ratio, sigmaJoint_constant_eventMass_snd]
  have hnum : (sigmaJoint p (fun _ ↦ q)).eventMass
      (fun w ↦ w.2 = z ∧ w.1 = a) = p a * q z := by
    unfold eventMass
    rw [Fintype.sum_sigma]
    simp only [sigmaJoint_apply]
    have hinner (b : α) :
        (∑ c, if c = z ∧ b = a then p b * q c else 0) =
          if b = a then p b * q z else 0 := by
      by_cases hb : b = a
      · simp only [hb, and_true]
        exact Fintype.sum_ite_eq' _ _
      · simp [hb]
    simp_rw [hinner]
    exact Fintype.sum_ite_eq' _ _
  rw [hnum]
  exact mul_div_cancel_right₀ _ (ne_of_gt hq)

end FinDist

namespace HardMatching

variable {N K : ℕ}

/-- The hidden data disclosed by whole-edge retirement, together with the
remaining trigger candidates. The survivor matching and surviving triggers
are deliberately absent from this record. -/
@[ext]
structure SurvivorRecord (N K : ℕ) where
  retired : Finset (Position N)
  matching : MatchingOn retired
  triggers : retired → Fin K
  candidates : Position N → Finset (Fin K)

namespace SurvivorRecord

/-- The record space is finite despite its dependent retired-vertex fields. -/
noncomputable instance : Fintype (SurvivorRecord N K) :=
  Fintype.ofEquiv
    ((R : Finset (Position N)) ×
      (MatchingOn R × (R → Fin K) × (Position N → Finset (Fin K))))
    { toFun := fun x ↦ ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
      invFun := fun r ↦ ⟨r.retired, r.matching, r.triggers, r.candidates⟩
      left_inv := by rintro ⟨R, m, t, c⟩; rfl
      right_inv := by intro r; cases r; rfl }

noncomputable instance : DecidableEq (SurvivorRecord N K) := Classical.decEq _

/-- An instance belongs to a record fiber exactly when it extends all
retired edges, retains the disclosed triggers, and passes all failed tests. -/
def Compatible (r : SurvivorRecord N K) (I : InstanceIndex N K) : Prop :=
  ((MatchingOn.finEquiv N).symm I.1).Extends r.matching ∧
  (∀ i : r.retired, I.2 i.1 = r.triggers i) ∧
  (∀ i, i ∉ r.retired → I.2 i ∈ r.candidates i)

noncomputable instance (r : SurvivorRecord N K) : DecidablePred r.Compatible :=
  Classical.decPred _

/-- Unretired original position labels; no renumbering is performed. -/
abbrev Survivor (r : SurvivorRecord N K) := {i : Position N // i ∉ r.retired}

/-- The complete still-hidden configuration compatible with a record. -/
abbrev State (r : SurvivorRecord N K) :=
  MatchingOn r.Survivor × (∀ i : r.Survivor, {c : Fin K // c ∈ r.candidates i.1})

noncomputable section

/-- Every survivor state has exactly one full hard-instance extension by the
disclosed record. This is an explicit bijection of the entire compatible fiber. -/
def fiberEquiv (r : SurvivorRecord N K) :
    {I : InstanceIndex N K // r.Compatible I} ≃ r.State where
  toFun I :=
    ((MatchingOn.extensionEquiv (fun i ↦ i ∈ r.retired) r.matching)
      ⟨(MatchingOn.finEquiv N).symm I.1.1, I.2.1⟩,
      fun i ↦ ⟨I.1.2 i.1, I.2.2.2 i.1 i.2⟩)
  invFun state :=
    ⟨((MatchingOn.finEquiv N)
        (MatchingOn.glue (fun i ↦ i ∈ r.retired) r.matching state.1),
      fun i ↦ if hi : i ∈ r.retired then r.triggers ⟨i, hi⟩ else
        (state.2 ⟨i, hi⟩).1),
      MatchingOn.glue_extends _ _ _,
      (by intro i; simp [i.2]),
      (by intro i hi; simp [hi, (state.2 ⟨i, hi⟩).2])⟩
  left_inv I := by
    apply Subtype.ext
    apply Prod.ext
    · apply PerfectMatching.ext
      intro i
      by_cases hi : i ∈ r.retired
      · simpa [MatchingOn.finEquiv, MatchingOn.glue, hi] using
          (I.2.1 ⟨i, hi⟩).symm
      · simp [MatchingOn.finEquiv, MatchingOn.glue, MatchingOn.extensionEquiv,
          MatchingOn.restrict, hi]
    · funext i
      by_cases hi : i ∈ r.retired
      · simp only [dif_pos hi]
        exact (I.2.2.1 ⟨i, hi⟩).symm
      · simp [hi]
  right_inv state := by
    apply Prod.ext
    · apply MatchingOn.ext
      intro i
      apply Subtype.ext
      simp [MatchingOn.extensionEquiv, MatchingOn.restrict,
        MatchingOn.finEquiv, MatchingOn.glue, i.2]
    · funext i
      apply Subtype.ext
      simp [i.2]

/-- Compatibility itself ensures that the retired region consists of whole
edges of the actual hidden matching. -/
theorem Compatible.regionClosed {r : SurvivorRecord N K} {I : InstanceIndex N K}
    (hI : r.Compatible I) : RegionClosed I.1 r.retired := by
  exact hI.1.closed

/-- All instances in one record fiber agree on the full retired information. -/
theorem Compatible.agreeOnRegion {r : SurvivorRecord N K}
    {I J : InstanceIndex N K} (hI : r.Compatible I) (hJ : r.Compatible J) :
    AgreeOnRegion I.1 J.1 I.2 J.2 r.retired := by
  constructor
  · intro i hi
    exact (hI.1 ⟨i, hi⟩).trans (hJ.1 ⟨i, hi⟩).symm
  · intro i hi
    exact (hI.2.1 ⟨i, hi⟩).trans (hJ.2.1 ⟨i, hi⟩).symm

/-- A nonempty record fiber supplies a nonempty survivor state space. -/
theorem state_nonempty (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}] : Nonempty r.State :=
  Nonempty.map r.fiberEquiv inferInstance

/-- The initial record discloses nothing and excludes no trigger. -/
def initial (N K : ℕ) : SurvivorRecord N K where
  retired := ∅
  matching :=
    { mate := id
      mate_ne_self := by intro i; exact False.elim (Finset.notMem_empty i.1 i.2)
      mate_mate := fun _ ↦ rfl }
  triggers := fun i ↦ False.elim (Finset.notMem_empty i.1 i.2)
  candidates := fun _ ↦ Finset.univ

theorem compatible_initial (I : InstanceIndex N K) : (initial N K).Compatible I := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact False.elim (Finset.notMem_empty i.1 i.2)
  · intro i
    exact False.elim (Finset.notMem_empty i.1 i.2)
  · intro i _
    exact Finset.mem_univ _

/-- The uniform law on a nonempty compatible fiber, transported back to full
instances. This static law will be identified with the adaptive posterior only
after the likelihood induction is proved. -/
def uniformExtensions (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}] :
    FinDist (InstanceIndex N K) :=
  (FinDist.uniform {I : InstanceIndex N K // r.Compatible I}).map Subtype.val

/-- Conditioning the actual uniform hard-instance prior on a record fiber
gives its uniform extension law. No adaptive-observation claim is hidden here. -/
theorem prior_conditionOn_compatible (r : SurvivorRecord N K)
    (hN : Even N) (hK : 1 ≤ K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}]
    (hpos : 0 < (uniformInstancePrior hN hK).eventMass r.Compatible) :
    (uniformInstancePrior hN hK).conditionOn r.Compatible hpos = r.uniformExtensions := by
  let := instanceIndex_nonempty hN hK
  exact FinDist.uniform_conditionOn_eq_map_subtype r.Compatible hpos

/-- The fiber-to-survivor bijection turns its uniform law into the uniform
law on the Cartesian survivor matching-and-candidate state space. -/
theorem uniform_fiber_map_state (r : SurvivorRecord N K)
    [Nonempty {I : InstanceIndex N K // r.Compatible I}] :
    letI := r.state_nonempty
    (FinDist.uniform {I : InstanceIndex N K // r.Compatible I}).map r.fiberEquiv =
      FinDist.uniform r.State := by
  let := r.state_nonempty
  exact FinDist.uniform_map_equiv r.fiberEquiv

/-- Retiring all edges touched by a set adds both of each affected edge's
endpoints. Previously retired vertices remain retired. -/
def retirementClosure (M : PerfectMatching N) (R S : Finset (Position N)) :
    Finset (Position N) := R ∪ S ∪ S.image M.mate

theorem retirementClosure_closed (M : PerfectMatching N)
    (R S : Finset (Position N)) (hR : RegionClosed M R) :
    RegionClosed M (retirementClosure M R S) := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hR i hi))
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [M.mate_mate j]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hj)

theorem subset_retirementClosure_left (M : PerfectMatching N) (R S : Finset (Position N)) :
    R ⊆ retirementClosure M R S := by
  intro i hi
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hi)

theorem subset_retirementClosure_touched (M : PerfectMatching N) (R S : Finset (Position N)) :
    S ⊆ retirementClosure M R S := by
  intro i hi
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)

/-- Actual retirement disclosures obtained from a compatible hidden instance. -/
def fromRegion (I : InstanceIndex N K) (R : Finset (Position N))
    (hR : RegionClosed I.1 R) (candidates : Position N → Finset (Fin K)) : SurvivorRecord N K where
  retired := R
  matching := ((MatchingOn.finEquiv N).symm I.1).restrict (fun i ↦ i ∈ R) hR
  triggers := fun i ↦ I.2 i.1
  candidates := candidates

/-- Equal disclosed regions and equal disclosed hidden data give equal records. -/
theorem fromRegion_eq (I J : InstanceIndex N K) (R S : Finset (Position N))
    (hR : RegionClosed I.1 R) (hS : RegionClosed J.1 S) (hsets : R = S)
    (hagree : AgreeOnRegion I.1 J.1 I.2 J.2 R)
    (candidates : Position N → Finset (Fin K)) :
    fromRegion I R hR candidates = fromRegion J S hS candidates := by
  subst S
  apply SurvivorRecord.ext (x := fromRegion I R hR candidates)
    (y := fromRegion J R hS candidates) rfl
  · apply heq_of_eq
    apply MatchingOn.ext
    intro i
    exact Subtype.ext (hagree.1 i.1 i.2)
  · apply heq_of_eq
    funext i
    exact hagree.2 i.1 i.2
  · rfl

/-- Reveal the whole matching edges touched by this operation. -/
def updateRetirement (r : SurvivorRecord N K) (I : InstanceIndex N K)
    (hI : r.Compatible I) (touched : Finset (Position N))
    (candidates : Position N → Finset (Fin K)) : SurvivorRecord N K :=
  fromRegion I (retirementClosure I.1 r.retired touched)
    (retirementClosure_closed I.1 r.retired touched hI.regionClosed)
    candidates

/-- A query tests at most its one displayed candidate at each unretired source. -/
def queryHits {backgroundSize : ℕ} (r : SurvivorRecord N K) (I : InstanceIndex N K)
    (y : MaskedState N (HardVocabulary K backgroundSize)) : Finset (Position N) :=
  (Finset.univ \ r.retired).filter (fun i ↦ y i = some (Sum.inl (I.2 i)))

/-- Failed candidates are removed only by the actual displayed label.
Masks and background tokens remove none. -/
def queryCandidates {backgroundSize : ℕ} (r : SurvivorRecord N K)
    (y : MaskedState N (HardVocabulary K backgroundSize)) (i : Position N) : Finset (Fin K) :=
  (r.candidates i).filter (fun c ↦ y i ≠ some (Sum.inl c))

/-- The analytic record after an actual query: retire every hit edge and
disclose both endpoint triggers, then discard failed candidates on survivors. -/
def queryUpdate {backgroundSize : ℕ} (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (y : MaskedState N (HardVocabulary K backgroundSize)) : SurvivorRecord N K :=
  r.updateRetirement I hI (r.queryHits I y) (r.queryCandidates y)

/-- The analytic record immediately before drawing values for an actual commit. -/
def commitUpdate (r : SurvivorRecord N K) (I : InstanceIndex N K)
    (hI : r.Compatible I) (batch : Finset (Position N)) : SurvivorRecord N K :=
  r.updateRetirement I hI batch r.candidates

/-- Every actual hidden instance remains in its query-updated record fiber. -/
theorem compatible_queryUpdate {backgroundSize : ℕ} (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (y : MaskedState N (HardVocabulary K backgroundSize)) :
    (r.queryUpdate I hI y).Compatible I := by
  refine ⟨(by intro i; rfl), (by intro i; rfl), ?_⟩
  intro i hi
  have hold : i ∉ r.retired := fun hh ↦ hi
    (subset_retirementClosure_left I.1 r.retired (r.queryHits I y) hh)
  have hmiss : y i ≠ some (Sum.inl (I.2 i)) := by
    intro hhit
    have hin : i ∈ r.queryHits I y := by simp [queryHits, hold, hhit]
    exact hi (subset_retirementClosure_touched I.1 r.retired (r.queryHits I y) hin)
  exact Finset.mem_filter.mpr ⟨hI.2.2 i hold, hmiss⟩

/-- Every actual instance remains in its commit-updated record fiber. -/
theorem compatible_commitUpdate (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I) (batch : Finset (Position N)) :
    (r.commitUpdate I hI batch).Compatible I := by
  refine ⟨(by intro i; rfl), (by intro i; rfl), ?_⟩
  intro i hi
  exact hI.2.2 i (fun hh ↦ hi (subset_retirementClosure_left I.1 r.retired batch hh))

/-- For any two instances in one actual query-record fiber, the complete
frozen reply is identical. Thus the next program branch is fixed on that fiber. -/
theorem queryUpdate_readState_eq {backgroundSize : ℕ}
    (P : HardLocalParameters K backgroundSize) (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (y : MaskedState N (HardVocabulary K backgroundSize))
    (J : InstanceIndex N K) (hJ : (r.queryUpdate I hI y).Compatible J) :
    (selectedOracle P I.1 I.2).readState y = (selectedOracle P J.1 J.2).readState y := by
  have hI' := r.compatible_queryUpdate I hI y
  apply readState_eq_of_region_no_hits P I.1 J.1 I.2 J.2
    (r.queryUpdate I hI y).retired hI'.regionClosed (hI'.agreeOnRegion hJ) y
  · intro i hi
    exact (Finset.mem_filter.mp (hI'.2.2 i hi)).2
  · intro i hi
    exact (Finset.mem_filter.mp (hJ.2.2 i hi)).2

/-- For any two instances in one actual commit-record fiber, the normalized
midpoint batch law is identical. The proof uses the real target and oracle. -/
theorem commitUpdate_midpointBatchLaw_eq {backgroundSize : ℕ}
    [Nonempty (HardVocabulary K backgroundSize)]
    (P : HardLocalParameters K backgroundSize) (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (h : History N (HardVocabulary K backgroundSize)) (hh : h.committed ⊆ r.retired)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (J : InstanceIndex N K) (hJ : (r.commitUpdate I hI batch).Compatible J) :
    ((BatchKernel.ofTarget (target P I.1 I.2) (target_strictlyPositive P I.1 I.2)).midpoint
      (BatchKernel.ofOracle (selectedOracle P I.1 I.2))).law h batch fresh =
    ((BatchKernel.ofTarget (target P J.1 J.2) (target_strictlyPositive P J.1 J.2)).midpoint
      (BatchKernel.ofOracle (selectedOracle P J.1 J.2))).law h batch fresh := by
  have hI' := r.compatible_commitUpdate I hI batch
  exact midpointBatchLaw_eq_of_region P I.1 J.1 I.2 J.2
    (r.commitUpdate I hI batch).retired hI'.regionClosed (hI'.agreeOnRegion hJ) h
    (hh.trans (subset_retirementClosure_left I.1 r.retired batch)) batch fresh
    (subset_retirementClosure_touched I.1 r.retired batch)

/-- Refining a retirement record and only deleting candidates cannot introduce
instances that were incompatible with the previous record. Newly retired
triggers are fixed to the compatible witness and therefore keep old constraints. -/
theorem compatible_updateRetirement_mono (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I) (touched : Finset (Position N))
    (candidates : Position N → Finset (Fin K))
    (hc : ∀ i, candidates i ⊆ r.candidates i)
    (J : InstanceIndex N K)
    (hJ : (r.updateRetirement I hI touched candidates).Compatible J) : r.Compatible J := by
  let R := retirementClosure I.1 r.retired touched
  have hsub := subset_retirementClosure_left I.1 r.retired touched
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hj := hJ.1 ⟨i.1, hsub i.2⟩
    exact hj.trans (hI.1 i)
  · intro i
    have hj := hJ.2.1 ⟨i.1, hsub i.2⟩
    exact hj.trans (hI.2.1 i)
  · intro i hi
    by_cases hr : i ∈ R
    · have ht := hJ.2.1 ⟨i, hr⟩
      change J.2 i = I.2 i at ht
      rw [ht]
      exact hI.2.2 i hi
    · exact hc i (hJ.2.2 i hr)

theorem compatible_queryUpdate_mono {backgroundSize : ℕ} (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (y : MaskedState N (HardVocabulary K backgroundSize))
    (J : InstanceIndex N K) (hJ : (r.queryUpdate I hI y).Compatible J) : r.Compatible J :=
  r.compatible_updateRetirement_mono I hI (r.queryHits I y) (r.queryCandidates y)
    (fun _ ↦ Finset.filter_subset _ _) J hJ

theorem compatible_commitUpdate_mono (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I) (batch : Finset (Position N))
    (J : InstanceIndex N K) (hJ : (r.commitUpdate I hI batch).Compatible J) : r.Compatible J :=
  r.compatible_updateRetirement_mono I hI batch r.candidates (fun _ ↦ Finset.Subset.refl _) J hJ

/-- On a query-record fiber, the entire hit set is fixed, including hits
whose mate row was not requested. Both endpoint triggers were disclosed. -/
theorem queryHits_eq_of_compatible_update {backgroundSize : ℕ} (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (y : MaskedState N (HardVocabulary K backgroundSize))
    (J : InstanceIndex N K) (hJ : (r.queryUpdate I hI y).Compatible J) :
    r.queryHits I y = r.queryHits J y := by
  have hI' := r.compatible_queryUpdate I hI y
  have hagree := hI'.agreeOnRegion hJ
  ext i
  by_cases hi : i ∈ (r.queryUpdate I hI y).retired
  · simp only [queryHits, Finset.mem_filter, hagree.2 i hi]
  · have hmiss := (Finset.mem_filter.mp (hI'.2.2 i hi)).2
    have hmiss' := (Finset.mem_filter.mp (hJ.2.2 i hi)).2
    simp [queryHits, hmiss, hmiss']

/-- Every member of a query-updated compatible fiber produces exactly that
retirement record when the actual query is applied to the previous record. -/
theorem queryUpdate_eq_of_compatible {backgroundSize : ℕ} (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (y : MaskedState N (HardVocabulary K backgroundSize))
    (J : InstanceIndex N K) (hJ : (r.queryUpdate I hI y).Compatible J) :
    r.queryUpdate I hI y =
      r.queryUpdate J (r.compatible_queryUpdate_mono I hI y J hJ) y := by
  have hI' := r.compatible_queryUpdate I hI y
  have hagree := hI'.agreeOnRegion hJ
  have hhits := r.queryHits_eq_of_compatible_update I hI y J hJ
  have hsets : retirementClosure I.1 r.retired (r.queryHits I y) =
      retirementClosure J.1 r.retired (r.queryHits J y) := by
    rw [← hhits]
    unfold retirementClosure
    congr 1
    apply Finset.image_congr
    intro i hi
    exact hagree.1 i (subset_retirementClosure_touched I.1 r.retired (r.queryHits I y) hi)
  exact fromRegion_eq I J _ _ _ _ hsets hagree _

/-- Commit-record fibers have the same exact support characterization. -/
theorem commitUpdate_eq_of_compatible (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I) (batch : Finset (Position N))
    (J : InstanceIndex N K) (hJ : (r.commitUpdate I hI batch).Compatible J) :
    r.commitUpdate I hI batch =
      r.commitUpdate J (r.compatible_commitUpdate_mono I hI batch J hJ) batch := by
  have hI' := r.compatible_commitUpdate I hI batch
  have hagree := hI'.agreeOnRegion hJ
  have hsets : retirementClosure I.1 r.retired batch =
      retirementClosure J.1 r.retired batch := by
    unfold retirementClosure
    congr 1
    apply Finset.image_congr
    intro i hi
    exact hagree.1 i (subset_retirementClosure_touched I.1 r.retired batch hi)
  exact fromRegion_eq I J _ _ _ _ hsets hagree _

/-- An actual query produces a specified retirement record if and only if
the instance belongs to its full compatible survivor fiber. -/
theorem queryUpdate_eq_iff {backgroundSize : ℕ} (r : SurvivorRecord N K)
    (I J : InstanceIndex N K) (hI : r.Compatible I) (hJ : r.Compatible J)
    (y : MaskedState N (HardVocabulary K backgroundSize)) :
    r.queryUpdate I hI y = r.queryUpdate J hJ y ↔ (r.queryUpdate I hI y).Compatible J := by
  constructor
  · intro heq
    rw [heq]
    exact r.compatible_queryUpdate J hJ y
  · intro hnew
    exact r.queryUpdate_eq_of_compatible I hI y J hnew

/-- The analogous exact support identity for a commit retirement. -/
theorem commitUpdate_eq_iff (r : SurvivorRecord N K)
    (I J : InstanceIndex N K) (hI : r.Compatible I) (hJ : r.Compatible J)
    (batch : Finset (Position N)) :
    r.commitUpdate I hI batch = r.commitUpdate J hJ batch ↔
      (r.commitUpdate I hI batch).Compatible J := by
  constructor
  · intro heq
    rw [heq]
    exact r.compatible_commitUpdate J hJ batch
  · intro hnew
    exact r.commitUpdate_eq_of_compatible I hI batch J hnew

/-- The preimage of an actual query retirement record is exactly its entire
new compatible fiber, with both directions given by explicit maps. -/
def queryRetirementFiberEquiv {backgroundSize : ℕ} (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (y : MaskedState N (HardVocabulary K backgroundSize)) :
    {J : {J : InstanceIndex N K // r.Compatible J} //
      r.queryUpdate J.1 J.2 y = r.queryUpdate I hI y} ≃
    {J : InstanceIndex N K // (r.queryUpdate I hI y).Compatible J} where
  toFun J := ⟨J.1.1, (r.queryUpdate_eq_iff I J.1.1 hI J.1.2 y).mp J.2.symm⟩
  invFun J :=
    ⟨⟨J.1, r.compatible_queryUpdate_mono I hI y J.1 J.2⟩,
      (r.queryUpdate_eq_of_compatible I hI y J.1 J.2).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The same complete-fiber equivalence for an actual commit retirement. -/
def commitRetirementFiberEquiv (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I) (batch : Finset (Position N)) :
    {J : {J : InstanceIndex N K // r.Compatible J} //
      r.commitUpdate J.1 J.2 batch = r.commitUpdate I hI batch} ≃
    {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J} where
  toFun J := ⟨J.1.1, (r.commitUpdate_eq_iff I J.1.1 hI J.1.2 batch).mp J.2.symm⟩
  invFun J :=
    ⟨⟨J.1, r.compatible_commitUpdate_mono I hI batch J.1 J.2⟩,
      (r.commitUpdate_eq_of_compatible I hI batch J.1 J.2).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact normalized posterior after observing an actual query retirement.
This one-step theorem starts from the old fiber's uniform law; identifying
that starting law with an arbitrary adaptive-prefix posterior remains separate. -/
theorem uniform_queryRetirementPosterior {backgroundSize : ℕ} (r : SurvivorRecord N K)
    [Nonempty {J : InstanceIndex N K // r.Compatible J}]
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (y : MaskedState N (HardVocabulary K backgroundSize))
    (hpos : 0 < (FinDist.uniform {J : InstanceIndex N K // r.Compatible J}).eventMass
      (fun J ↦ r.queryUpdate J.1 J.2 y = r.queryUpdate I hI y)) :
    letI : Nonempty {J : InstanceIndex N K // (r.queryUpdate I hI y).Compatible J} :=
      ⟨⟨I, r.compatible_queryUpdate I hI y⟩⟩
    (FinDist.uniform {J : InstanceIndex N K // r.Compatible J}).conditionalMap
      (fun J ↦ r.queryUpdate J.1 J.2 y = r.queryUpdate I hI y) hpos Subtype.val =
      (r.queryUpdate I hI y).uniformExtensions := by
  let : Nonempty {J : InstanceIndex N K // (r.queryUpdate I hI y).Compatible J} :=
    ⟨⟨I, r.compatible_queryUpdate I hI y⟩⟩
  let : Nonempty {J : {J : InstanceIndex N K // r.Compatible J} //
      r.queryUpdate J.1 J.2 y = r.queryUpdate I hI y} := ⟨⟨⟨I, hI⟩, rfl⟩⟩
  exact FinDist.uniform_conditionalMap_equiv _ (r.queryRetirementFiberEquiv I hI y)
    Subtype.val Subtype.val (fun _ ↦ rfl) hpos

/-- Exact normalized posterior after observing an actual commit retirement. -/
theorem uniform_commitRetirementPosterior (r : SurvivorRecord N K)
    [Nonempty {J : InstanceIndex N K // r.Compatible J}]
    (I : InstanceIndex N K) (hI : r.Compatible I) (batch : Finset (Position N))
    (hpos : 0 < (FinDist.uniform {J : InstanceIndex N K // r.Compatible J}).eventMass
      (fun J ↦ r.commitUpdate J.1 J.2 batch = r.commitUpdate I hI batch)) :
    letI : Nonempty {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J} :=
      ⟨⟨I, r.compatible_commitUpdate I hI batch⟩⟩
    (FinDist.uniform {J : InstanceIndex N K // r.Compatible J}).conditionalMap
      (fun J ↦ r.commitUpdate J.1 J.2 batch = r.commitUpdate I hI batch) hpos Subtype.val =
      (r.commitUpdate I hI batch).uniformExtensions := by
  let : Nonempty {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J} :=
    ⟨⟨I, r.compatible_commitUpdate I hI batch⟩⟩
  let : Nonempty {J : {J : InstanceIndex N K // r.Compatible J} //
      r.commitUpdate J.1 J.2 batch = r.commitUpdate I hI batch} := ⟨⟨⟨I, hI⟩, rfl⟩⟩
  exact FinDist.uniform_conditionalMap_equiv _ (r.commitRetirementFiberEquiv I hI batch)
    Subtype.val Subtype.val (fun _ ↦ rfl) hpos

/-- The actual midpoint kernel on an instance, used without any factorization
assumption in the commit-observation experiment below. -/
def instanceMidpointKernel {backgroundSize : ℕ} [Nonempty (HardVocabulary K backgroundSize)]
    (P : HardLocalParameters K backgroundSize) (I : InstanceIndex N K) :
    BatchKernel N (HardVocabulary K backgroundSize) :=
  (BatchKernel.ofTarget (target P I.1 I.2) (target_strictlyPositive P I.1 I.2)).midpoint
    (BatchKernel.ofOracle (selectedOracle P I.1 I.2))

/-- After a fixed retirement record, retain the still-hidden compatible
instance and then draw the actual midpoint commit values for that instance. -/
def commitObservationLaw {backgroundSize : ℕ} [Nonempty (HardVocabulary K backgroundSize)]
    (P : HardLocalParameters K backgroundSize) (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (h : History N (HardVocabulary K backgroundSize))
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) :
    FinDist ((_J : {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J}) ×
      (batch → HardVocabulary K backgroundSize)) := by
  let : Nonempty {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J} :=
    ⟨⟨I, r.compatible_commitUpdate I hI batch⟩⟩
  exact FinDist.sigmaJoint (FinDist.uniform _)
    (fun J ↦ (instanceMidpointKernel P J.1).law h batch fresh)

/-- All kernels in the actual post-retirement experiment are equal to the
witness's kernel, proved by matching-product locality, including normalization. -/
theorem commitObservationLaw_eq_constant {backgroundSize : ℕ}
    [Nonempty (HardVocabulary K backgroundSize)]
    (P : HardLocalParameters K backgroundSize) (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (h : History N (HardVocabulary K backgroundSize)) (hh : h.committed ⊆ r.retired)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) :
    letI : Nonempty {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J} :=
      ⟨⟨I, r.compatible_commitUpdate I hI batch⟩⟩
    r.commitObservationLaw P I hI h batch fresh =
      FinDist.sigmaJoint
        (FinDist.uniform {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J})
        (fun _ ↦ (instanceMidpointKernel P I).law h batch fresh) := by
  let : Nonempty {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J} :=
    ⟨⟨I, r.compatible_commitUpdate I hI batch⟩⟩
  ext w
  change (FinDist.uniform {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J}) w.1 *
      (instanceMidpointKernel P w.1.1).law h batch fresh w.2 =
    (FinDist.uniform {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J}) w.1 *
      (instanceMidpointKernel P I).law h batch fresh w.2
  have hk : (instanceMidpointKernel P I).law h batch fresh =
      (instanceMidpointKernel P w.1.1).law h batch fresh :=
    r.commitUpdate_midpointBatchLaw_eq P I hI h hh batch fresh w.1.1 w.1.2
  rw [hk]

/-- Every possible batch assignment has positive likelihood after retirement. -/
theorem commitObservation_eventMass_pos {backgroundSize : ℕ}
    [Nonempty (HardVocabulary K backgroundSize)]
    (P : HardLocalParameters K backgroundSize) (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (h : History N (HardVocabulary K backgroundSize)) (hh : h.committed ⊆ r.retired)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (z : batch → HardVocabulary K backgroundSize) :
    0 < (r.commitObservationLaw P I hI h batch fresh).eventMass (fun w ↦ w.2 = z) := by
  rw [r.commitObservationLaw_eq_constant P I hI h hh batch fresh,
    FinDist.sigmaJoint_constant_eventMass_snd]
  exact (instanceMidpointKernel P I).positive h batch fresh z

/-- Observing actual midpoint commit values after the retirement disclosure
leaves the uniform compatible-instance law unchanged. This checks the complete
one-step Bayes normalization, rather than merely equal unnormalized factors. -/
theorem commitObservation_posterior {backgroundSize : ℕ}
    [Nonempty (HardVocabulary K backgroundSize)]
    (P : HardLocalParameters K backgroundSize) (r : SurvivorRecord N K)
    (I : InstanceIndex N K) (hI : r.Compatible I)
    (h : History N (HardVocabulary K backgroundSize)) (hh : h.committed ⊆ r.retired)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (z : batch → HardVocabulary K backgroundSize) :
    letI : Nonempty {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J} :=
      ⟨⟨I, r.compatible_commitUpdate I hI batch⟩⟩
    (r.commitObservationLaw P I hI h batch fresh).conditionalMap (fun w ↦ w.2 = z)
      (r.commitObservation_eventMass_pos P I hI h hh batch fresh z) Sigma.fst =
      FinDist.uniform {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J} := by
  let : Nonempty {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J} :=
    ⟨⟨I, r.compatible_commitUpdate I hI batch⟩⟩
  let q := (instanceMidpointKernel P I).law h batch fresh
  have hq : 0 < q z := (instanceMidpointKernel P I).positive h batch fresh z
  have hpos : 0 < (FinDist.sigmaJoint
      (FinDist.uniform {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J})
      (fun _ ↦ q)).eventMass (fun w ↦ w.2 = z) := by
    rw [FinDist.sigmaJoint_constant_eventMass_snd]
    exact hq
  calc
    _ = (FinDist.sigmaJoint
        (FinDist.uniform {J : InstanceIndex N K // (r.commitUpdate I hI batch).Compatible J})
        (fun _ ↦ q)).conditionalMap (fun w ↦ w.2 = z) hpos Sigma.fst :=
      FinDist.conditionalMap_congr_dist
        (r.commitObservationLaw_eq_constant P I hI h hh batch fresh) _ _ _ Sigma.fst
    _ = _ := FinDist.sigmaJoint_constant_observation_posterior _ q z hq

end
end SurvivorRecord
end HardMatching
end ForestSampling
