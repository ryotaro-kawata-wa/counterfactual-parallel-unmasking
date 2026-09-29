import ForestSampling.HardCollisionAffinity
import ForestSampling.MatchingCollision

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace HardMatching

variable {N bankSize backgroundSize : ℕ}

/-- A region contains the whole matching edge whenever it contains one endpoint. -/
def RegionClosed (M : PerfectMatching N) (R : Finset (Position N)) : Prop :=
  ∀ i ∈ R, M.mate i ∈ R

/-- Two hard instances have the same disclosed matching and triggers on a region. -/
def AgreeOnRegion (M L : PerfectMatching N)
    (trigger other : Position N → Fin bankSize) (R : Finset (Position N)) : Prop :=
  (∀ i ∈ R, M.mate i = L.mate i) ∧ (∀ i ∈ R, trigger i = other i)

theorem RegionClosed.compl {M : PerfectMatching N} {R : Finset (Position N)}
    (hR : RegionClosed M R) {i : Position N} (hi : i ∉ R) : M.mate i ∉ R := by
  intro hm
  have hh := hR (M.mate i) hm
  rw [M.mate_mate i] at hh
  exact hi hh

theorem AgreeOnRegion.closed_right {M L : PerfectMatching N}
    {trigger other : Position N → Fin bankSize} {R : Finset (Position N)}
    (hagree : AgreeOnRegion M L trigger other R) (hR : RegionClosed M R) :
    RegionClosed L R := by
  intro i hi
  rw [← hagree.1 i hi]
  exact hR i hi

noncomputable section

/-- The probability of observations at the two endpoints of one edge.
The definition also accepts nonrepresentative positions for pointwise comparisons. -/
def edgeObservationMass (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize)) (i : Position N) : ℝ :=
  (P.edgeLaw (trigger i) (trigger (M.mate i))).eventMass
    (fun z ↦ (∀ a, y i = some a → z.1 = a) ∧
      (∀ b, y (M.mate i) = some b → z.2 = b))

/-- An entirely masked edge contributes a unit observation likelihood. -/
theorem edgeObservationMass_of_masked (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize)) (i : Position N)
    (hi : y i = none) (hm : y (M.mate i) = none) :
    edgeObservationMass P M trigger y i = 1 := by
  simp [edgeObservationMass, hi, hm, FinDist.eventMass_true]

/-- Exact observation likelihood factors over matching edges, expressed over
the fixed position type so two different hidden matchings can be compared. -/
theorem target_eventMass_agrees (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize)) :
    (target P M trigger).eventMass y.Agrees =
      ∏ i, if i < M.mate i then edgeObservationMass P M trigger y i else 1 := by
  classical
  let ep (e : M.EdgeIndex) := P.edgeLaw (trigger e.1) (trigger (M.mate e.1))
  let q := FinDist.piProduct ep
  let assemble := (M.pairEquiv (V := HardVocabulary bankSize backgroundSize)).symm
  have hevent (z : M.EdgeIndex → HardVocabulary bankSize backgroundSize ×
      HardVocabulary bankSize backgroundSize) :
      (y.Agrees ∘ assemble) z ↔ ∀ e, M.edgeAgrees y e (z e) :=
    M.agrees_fromPairs_iff y z
  calc
    _ = q.eventMass (y.Agrees ∘ assemble) :=
      FinDist.map_equiv_eventMass q assemble y.Agrees
    _ = q.eventMass (fun z ↦ ∀ e, M.edgeAgrees y e (z e)) :=
      q.eventMass_congr _ _ hevent
    _ = ∏ e : M.EdgeIndex, (ep e).eventMass (M.edgeAgrees y e) :=
      FinDist.piProduct_eventMass_forall ep (M.edgeAgrees y)
    _ = ∏ e : M.EdgeIndex, edgeObservationMass P M trigger y e.1 := by
      apply Finset.prod_congr rfl
      intro e _
      exact (ep e).eventMass_congr _ _ (fun _ ↦ Iff.rfl)
    _ = ∏ i ∈ M.representatives, edgeObservationMass P M trigger y i :=
      Finset.prod_coe_sort _ _
    _ = _ := by rw [PerfectMatching.representatives, Finset.prod_filter]

/-- Observations confined to a disclosed closed region have the same exact
likelihood in any two hard instances agreeing on that region. -/
theorem target_eventMass_agrees_eq_of_region
    (P : HardLocalParameters bankSize backgroundSize)
    (M L : PerfectMatching N) (trigger other : Position N → Fin bankSize)
    (R : Finset (Position N)) (hR : RegionClosed M R)
    (hagree : AgreeOnRegion M L trigger other R)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize))
    (hy : ∀ i, i ∉ R → y i = none) :
    (target P M trigger).eventMass y.Agrees =
      (target P L other).eventMass y.Agrees := by
  rw [target_eventMass_agrees, target_eventMass_agrees]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ R
  · have hmate := hagree.1 i hi
    have ht := hagree.2 i hi
    have htm := hagree.2 (M.mate i) (hR i hi)
    simp only [edgeObservationMass, ← hmate, ht, htm]
  · have hm := hR.compl hi
    have hlm := (hagree.closed_right hR).compl hi
    rw [edgeObservationMass_of_masked P M trigger y i (hy i hi) (hy _ hm),
      edgeObservationMass_of_masked P L other y i (hy i hi) (hy _ hlm)]
    simp

/-- The same locality statement for the committed-history event. -/
theorem target_eventMass_history_eq_of_region
    (P : HardLocalParameters bankSize backgroundSize)
    (M L : PerfectMatching N) (trigger other : Position N → Fin bankSize)
    (R : Finset (Position N)) (hR : RegionClosed M R)
    (hagree : AgreeOnRegion M L trigger other R)
    (h : History N (HardVocabulary bankSize backgroundSize)) (hh : h.committed ⊆ R) :
    (target P M trigger).eventMass h.Agrees =
      (target P L other).eventMass h.Agrees := by
  have hy (i : Position N) (hi : i ∉ R) : MaskedState.commitState h i = none := by
    have hc : i ∉ h.committed := fun hc ↦ hi (hh hc)
    simp [MaskedState.commitState, hc]
  calc
    _ = (target P M trigger).eventMass (MaskedState.commitState h).Agrees :=
      (FinDist.eventMass_congr _ _ _ (MaskedState.commitState_agrees_iff h)).symm
    _ = (target P L other).eventMass (MaskedState.commitState h).Agrees :=
      target_eventMass_agrees_eq_of_region P M L trigger other R hR hagree _ hy
    _ = _ := FinDist.eventMass_congr _ _ _ (MaskedState.commitState_agrees_iff h)

/-- Conditioning and reading a fresh batch is a ratio of two history-event
probabilities. This keeps the locality argument at the level of actual laws. -/
theorem jointBatchLaw_apply_history_ratio
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (h : History N V) (batch : Finset (Position N))
    (fresh : batch ⊆ h.uncommitted) (z : batch → V) :
    h.jointBatchLaw p hp batch z =
      p.eventMass (h.appendBatch batch fresh z).Agrees / p.eventMass h.Agrees := by
  calc
    _ = p.eventMass (fun x ↦ h.Agrees x ∧ (fun i : batch ↦ x i.1) = z) /
        p.eventMass h.Agrees :=
      FinDist.conditionalMap_apply_ratio p h.Agrees (h.probability_pos p hp)
        (fun x (i : batch) ↦ x i.1) z
    _ = _ := by
      congr 1
      exact p.eventMass_congr _ _ (fun x ↦ (h.agrees_appendBatch_iff batch fresh z x).symm)

/-- The full joint batch conditional is unchanged when survivor matching and
triggers vary outside a disclosed closed region containing history and batch. -/
theorem jointBatchLaw_eq_of_region
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize)
    (M L : PerfectMatching N) (trigger other : Position N → Fin bankSize)
    (R : Finset (Position N)) (hR : RegionClosed M R)
    (hagree : AgreeOnRegion M L trigger other R)
    (h : History N (HardVocabulary bankSize backgroundSize)) (hh : h.committed ⊆ R)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) (hb : batch ⊆ R) :
    h.jointBatchLaw (target P M trigger) (target_strictlyPositive P M trigger) batch =
      h.jointBatchLaw (target P L other) (target_strictlyPositive P L other) batch := by
  ext z
  rw [jointBatchLaw_apply_history_ratio _ _ h batch fresh z,
    jointBatchLaw_apply_history_ratio _ _ h batch fresh z,
    target_eventMass_history_eq_of_region P M L trigger other R hR hagree h hh,
    target_eventMass_history_eq_of_region P M L trigger other R hR hagree
      (h.appendBatch batch fresh z) (by
        simpa only [History.appendBatch_committed] using Finset.union_subset hh hb)]

/-- A requested row on a disclosed closed region is fixed by its local
matching and two trigger labels, even for arbitrary counterfactual queries. -/
theorem selectedRow_eq_of_region
    (P : HardLocalParameters bankSize backgroundSize)
    (M L : PerfectMatching N) (trigger other : Position N → Fin bankSize)
    (R : Finset (Position N)) (hR : RegionClosed M R)
    (hagree : AgreeOnRegion M L trigger other R)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize))
    (j : MaskedPosition y) (hj : j.1 ∈ R) :
    selectedRow P M trigger y j = selectedRow P L other y j := by
  have hm := hagree.1 j.1 hj
  have ht := hagree.2 j.1 hj
  have htm := hagree.2 (M.mate j.1) (hR j.1 hj)
  simp only [selectedRow, ← hm, ht, htm]

/-- The selected product commit law is fixed by the same disclosed region. -/
theorem commitDistribution_eq_of_region
    (P : HardLocalParameters bankSize backgroundSize)
    (M L : PerfectMatching N) (trigger other : Position N → Fin bankSize)
    (R : Finset (Position N)) (hR : RegionClosed M R)
    (hagree : AgreeOnRegion M L trigger other R)
    (h : History N (HardVocabulary bankSize backgroundSize))
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) (hb : batch ⊆ R) :
    (selectedOracle P M trigger).commitDistribution h batch fresh =
      (selectedOracle P L other).commitDistribution h batch fresh := by
  unfold FrozenOracle.commitDistribution
  congr 1
  funext j
  exact selectedRow_eq_of_region P M L trigger other R hR hagree
    (MaskedState.commitState h) (FrozenOracle.commitReadout h batch fresh j) (hb j.2)

/-- The actual normalized geometric midpoint commit kernel has no remaining
dependence on survivor data once all batch-touching edges are disclosed. -/
theorem midpointBatchLaw_eq_of_region
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize)
    (M L : PerfectMatching N) (trigger other : Position N → Fin bankSize)
    (R : Finset (Position N)) (hR : RegionClosed M R)
    (hagree : AgreeOnRegion M L trigger other R)
    (h : History N (HardVocabulary bankSize backgroundSize)) (hh : h.committed ⊆ R)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) (hb : batch ⊆ R) :
    ((BatchKernel.ofTarget (target P M trigger) (target_strictlyPositive P M trigger)).midpoint
      (BatchKernel.ofOracle (selectedOracle P M trigger))).law h batch fresh =
    ((BatchKernel.ofTarget (target P L other) (target_strictlyPositive P L other)).midpoint
      (BatchKernel.ofOracle (selectedOracle P L other))).law h batch fresh := by
  have hp := jointBatchLaw_eq_of_region P M L trigger other R hR hagree h hh batch fresh hb
  have hq := commitDistribution_eq_of_region P M L trigger other R hR hagree h batch fresh hb
  ext z
  simp only [BatchKernel.midpoint, BatchKernel.ofTarget, BatchKernel.ofOracle,
    FinDist.midpoint_apply]
  rw [hp, hq]

/-- No surviving endpoint hits, so every row outside the disclosed region
is the common marginal. Together with the fixed retired rows this determines
the complete frozen reply, rather than only its requested projections. -/
theorem readState_eq_of_region_no_hits
    (P : HardLocalParameters bankSize backgroundSize)
    (M L : PerfectMatching N) (trigger other : Position N → Fin bankSize)
    (R : Finset (Position N)) (hR : RegionClosed M R)
    (hagree : AgreeOnRegion M L trigger other R)
    (y : MaskedState N (HardVocabulary bankSize backgroundSize))
    (hmiss : ∀ i, i ∉ R → y i ≠ some (Sum.inl (trigger i)))
    (hmiss' : ∀ i, i ∉ R → y i ≠ some (Sum.inl (other i))) :
    (selectedOracle P M trigger).readState y = (selectedOracle P L other).readState y := by
  funext j
  by_cases hj : j.1 ∈ R
  · exact selectedRow_eq_of_region P M L trigger other R hR hagree y j hj
  · have hm := hmiss (M.mate j.1) (hR.compl hj)
    have hl := hmiss' (L.mate j.1) ((hagree.closed_right hR).compl hj)
    simp [FrozenOracle.readState, selectedRow, hm, hl]

/-- The distinguished preprocessing reply is common to every hard instance. -/
theorem readState_allMask_common
    (P : HardLocalParameters bankSize backgroundSize)
    (M : PerfectMatching N) (trigger : Position N → Fin bankSize) :
    (selectedOracle P M trigger).readState
      (MaskedState.allMask N (HardVocabulary bankSize backgroundSize)) =
      fun _ ↦ P.commonMarginal := by
  funext j
  simp [FrozenOracle.readState, selectedRow, MaskedState.allMask]

end
end HardMatching
end ForestSampling
