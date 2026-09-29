import ForestSampling.ProgramMidpoint
import ForestSampling.HardEdgeDistance

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Deterministic readouts cannot decrease affinity. -/
theorem affinity_map_ge (p q : FinDist α) (f : α → β) [DecidableEq β] :
    affinity p q ≤ affinity (p.map f) (q.map f) := by
  have hm (r : FinDist α) : r.bind (fun a ↦ dirac (f a)) = r.map f := by
    ext b
    simp only [bind_apply, dirac_apply, map_apply]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : b = f a
    · subst b
      simp
    · simp [ha, Ne.symm ha]
  have hh := affinity_bind_ge p q (fun a ↦ dirac (f a)) (fun a ↦ dirac (f a))
  simp only [affinity_self, mul_one, hm] at hh
  exact hh

/-- The first marginal of a binary independent product. -/
theorem prod_map_first (p : FinDist α) (q : FinDist β) [DecidableEq α] :
    (p.prod q).map Prod.fst = p := by
  ext a
  rw [map_apply, Fintype.sum_prod_type]
  simp only [prod_apply]
  have hi (b : α) : (∑ c, if b = a then p b * q c else 0) =
      if b = a then p b else 0 := by
    split <;> simp_all [← Finset.mul_sum, q.sum_mass]
  simp_rw [hi]
  exact Fintype.sum_ite_eq' _ _

/-- Separating a set of product coordinates preserves independence. -/
theorem piProduct_map_subtype_split {ι V : Type*} [Fintype ι] [Fintype V]
    [DecidableEq ι] [DecidableEq V] (p : ι → FinDist V)
    (S : ι → Prop) [DecidablePred S] :
    (piProduct p).map (Equiv.piEquivPiSubtypeProd S (fun _ ↦ V)) =
      (piProduct fun i : {i // S i} ↦ p i.1).prod
        (piProduct fun i : {i // ¬ S i} ↦ p i.1) := by
  ext z
  rw [map_equiv_apply]
  change (∏ i, p i ((Equiv.piEquivPiSubtypeProd S (fun _ ↦ V)).symm z i)) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype S]
  simp only [prod_apply, piProduct_apply]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
    simp [Equiv.piEquivPiSubtypeProd, i.2]

/-- Restricting an independent product to any subset of coordinates. -/
theorem piProduct_map_subtype {ι V : Type*} [Fintype ι] [Fintype V]
    [DecidableEq ι] [DecidableEq V] (p : ι → FinDist V)
    (S : ι → Prop) [DecidablePred S] :
    (piProduct p).map (fun x (i : {i // S i}) ↦ x i.1) =
      piProduct (fun i : {i // S i} ↦ p i.1) := by
  have hm := congrArg (fun r ↦ r.map Prod.fst)
    (piProduct_map_subtype_split p S)
  simpa only [map_comp, prod_map_first, Function.comp_def,
    Equiv.piEquivPiSubtypeProd_apply] using hm

/-- Injectively selecting coordinates of an independent finite product. -/
theorem piProduct_map_injective {ι κ V : Type*}
    [Fintype ι] [Fintype κ] [Fintype V]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq V]
    (p : ι → FinDist V) (f : κ → ι) (hf : Function.Injective f) :
    (piProduct p).map (fun x i ↦ x (f i)) = piProduct (fun i ↦ p (f i)) := by
  classical
  let S : ι → Prop := fun i ↦ ∃ j, f j = i
  let e : κ ≃ {i // S i} :=
    { toFun := fun j ↦ ⟨f j, j, rfl⟩
      invFun := fun i ↦ Classical.choose i.2
      left_inv := fun j ↦ hf (Classical.choose_spec (show S (f j) from ⟨j, rfl⟩))
      right_inv := fun i ↦ Subtype.ext (Classical.choose_spec i.2) }
  let reindex : ({i // S i} → V) ≃ (κ → V) :=
    { toFun := fun z i ↦ z (e i)
      invFun := fun x i ↦ x (e.symm i)
      left_inv := by intro z; funext i; simp
      right_inv := by intro x; funext i; simp }
  have hreindex : (piProduct (fun i : {i // S i} ↦ p i.1)).map reindex =
      piProduct (fun i ↦ p (f i)) := by
    ext x
    rw [map_equiv_apply]
    change (∏ i : {i // S i}, p i.1 (reindex.symm x i)) =
      ∏ i, p (f i) (x i)
    symm
    apply Fintype.prod_equiv e
    intro i
    change p (f i) (x i) = p (f i) (x (e.symm (e i)))
    rw [e.symm_apply_apply]
  calc
    _ = ((piProduct p).map (fun x (i : {i // S i}) ↦ x i.1)).map reindex := by
      rw [map_comp]
      congr 1
    _ = _ := by
      rw [piProduct_map_subtype p S]
      exact hreindex

/-- A product conditioned on separate coordinate events remains a product. -/
theorem piProduct_conditionOn_forall {ι V : Type*} [Fintype ι] [Fintype V]
    [DecidableEq ι] (p : ι → FinDist V) (E : ι → V → Prop)
    [∀ i, DecidablePred (E i)] (hE : ∀ i, 0 < (p i).eventMass (E i)) :
    (piProduct p).conditionOn (fun x ↦ ∀ i, E i (x i))
      (piProduct_eventMass_forall_pos p E hE) =
      piProduct (fun i ↦ (p i).conditionOn (E i) (hE i)) := by
  classical
  ext x
  by_cases hx : ∀ i, E i (x i)
  · rw [conditionOn_apply_of_mem (piProduct p) (fun x ↦ ∀ i, E i (x i)) _ hx,
      piProduct_apply, piProduct_eventMass_forall, piProduct_apply]
    simp only [conditionOn_apply_of_mem _ _ _ (hx _), Finset.prod_div_distrib]
  · rw [conditionOn_apply_of_not_mem _ _ _ hx, piProduct_apply]
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (conditionOn_apply_of_not_mem _ _ _ hi)

/-- Conditioning other independent coordinates leaves selected unconstrained
coordinates at their original product law. -/
theorem piProduct_conditionalMap_unconstrained {ι κ V : Type*}
    [Fintype ι] [Fintype κ] [Fintype V]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq V]
    (p : ι → FinDist V) (E : ι → V → Prop)
    [∀ i, DecidablePred (E i)] (hE : ∀ i, 0 < (p i).eventMass (E i))
    (f : κ → ι) (hf : Function.Injective f)
    (hfree : ∀ i v, E (f i) v) :
    (piProduct p).conditionalMap (fun x ↦ ∀ i, E i (x i))
      (piProduct_eventMass_forall_pos p E hE) (fun x i ↦ x (f i)) =
      piProduct (fun i ↦ p (f i)) := by
  unfold conditionalMap
  rw [piProduct_conditionOn_forall p E hE, piProduct_map_injective _ f hf]
  congr 1
  funext i
  have hmass : (p (f i)).eventMass (E (f i)) = 1 := by
    rw [(p (f i)).eventMass_congr _ (fun _ ↦ True)
      (fun v ↦ iff_true_intro (hfree i v))]
    exact eventMass_true _
  ext v
  simp [conditionOn, hfree, hmass]

/-- Grouping two independent coordinate families into independent pairs. -/
theorem piProduct_map_sum_pairs {ι V : Type*} [Fintype ι] [Fintype V]
    [DecidableEq ι] [DecidableEq V] (p : ι ⊕ ι → FinDist V) :
    (piProduct p).map (fun x i ↦ (x (Sum.inl i), x (Sum.inr i))) =
      piProduct (fun i ↦ (p (Sum.inl i)).prod (p (Sum.inr i))) := by
  let e : (ι ⊕ ι → V) ≃ (ι → V × V) :=
    { toFun := fun x i ↦ (x (Sum.inl i), x (Sum.inr i))
      invFun := fun z ↦ Sum.elim (fun i ↦ (z i).1) (fun i ↦ (z i).2)
      left_inv := by intro x; funext i; cases i <;> rfl
      right_inv := by intro z; rfl }
  change (piProduct p).map e = _
  ext z
  rw [map_equiv_apply]
  change (∏ i, p i (e.symm z i)) = ∏ i, p (Sum.inl i) (z i).1 * p (Sum.inr i) (z i).2
  rw [Fintype.prod_sum_type, Finset.prod_mul_distrib]
  rfl

end FinDist

namespace PerfectMatching

variable {N : ℕ} {V : Type*}

/-- Matching edges whose two endpoints are committed in this batch. -/
abbrev BatchEdge (M : PerfectMatching N) (batch : Finset (Position N)) :=
  {e : M.EdgeIndex // e.1 ∈ batch ∧ M.mate e.1 ∈ batch}

/-- Read both endpoint values of every edge wholly inside the batch. -/
def batchPairs (M : PerfectMatching N) (batch : Finset (Position N))
    (z : batch → V) : M.BatchEdge batch → V × V :=
  fun e ↦ (z ⟨e.1.1, e.2.1⟩, z ⟨M.mate e.1.1, e.2.2⟩)

/-- The two endpoint slots of the selected edges are distinct coordinates. -/
def batchEndpoint (M : PerfectMatching N) (batch : Finset (Position N)) :
    M.BatchEdge batch ⊕ M.BatchEdge batch → batch
  | .inl e => ⟨e.1.1, e.2.1⟩
  | .inr e => ⟨M.mate e.1.1, e.2.2⟩

theorem batchEndpoint_injective (M : PerfectMatching N) (batch : Finset (Position N)) :
    Function.Injective (M.batchEndpoint batch) := by
  intro a b hab
  cases a with
  | inl e =>
      cases b with
      | inl f =>
          have heq : e.1.1 = f.1.1 := congrArg (fun i : batch ↦ i.1) hab
          have hef : e = f := Subtype.ext (Subtype.ext heq)
          exact congrArg Sum.inl hef
      | inr f =>
          have heq : e.1.1 = M.mate f.1.1 := congrArg Subtype.val hab
          exact False.elim (M.mate_not_mem_representatives f.1.2 (heq ▸ e.1.2))
  | inr e =>
      cases b with
      | inl f =>
          have heq : M.mate e.1.1 = f.1.1 := congrArg Subtype.val hab
          exact False.elim (M.mate_not_mem_representatives e.1.2 (heq.symm ▸ f.1.2))
      | inr f =>
          have heq : M.mate e.1.1 = M.mate f.1.1 := congrArg (fun i : batch ↦ i.1) hab
          have hef : e = f := Subtype.ext (Subtype.ext (M.mate_mate.injective heq))
          exact congrArg Sum.inr hef

end PerfectMatching

namespace HardMatching

variable {N bankSize backgroundSize : ℕ}
noncomputable section

/-- Fresh batch coordinates are masked at the mandatory commit query. -/
theorem commitState_none_of_fresh
    {V : Type*} [DecidableEq V] (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (i : Position N) (hi : i ∈ batch) : MaskedState.commitState h i = none := by
  have hf := (h.mem_uncommitted_iff i).mp (fresh hi)
  simp [MaskedState.commitState, hf]

/-- The joint target law restricted to wholly internal batch edges is the
unconditioned product of their correlated edge laws. -/
theorem jointBatchLaw_map_batchPairs
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize) (M : PerfectMatching N)
    (trigger : Position N → Fin bankSize)
    (h : History N (HardVocabulary bankSize backgroundSize))
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) :
    (h.jointBatchLaw (target P M trigger) (target_strictlyPositive P M trigger) batch).map
      (M.batchPairs batch) =
      FinDist.piProduct (fun e : M.BatchEdge batch ↦
        P.edgeLaw (trigger e.1.1) (trigger (M.mate e.1.1))) := by
  classical
  let ep (e : M.EdgeIndex) := P.edgeLaw (trigger e.1) (trigger (M.mate e.1))
  let q := FinDist.piProduct ep
  let assemble := (M.pairEquiv (V := HardVocabulary bankSize backgroundSize)).symm
  let E (e : M.EdgeIndex) := M.edgeAgrees (MaskedState.commitState h) e
  have hE (e : M.EdgeIndex) : 0 < (ep e).eventMass (E e) :=
    M.edgeAgrees_eventMass_pos (MaskedState.commitState h) e (ep e)
      (P.edgeLaw_strictlyPositive _ _)
  have hevent (z : M.EdgeIndex → HardVocabulary bankSize backgroundSize ×
      HardVocabulary bankSize backgroundSize) :
      h.Agrees (assemble z) ↔ ∀ e, E e (z e) := by
    rw [← MaskedState.commitState_agrees_iff]
    exact M.agrees_fromPairs_iff (MaskedState.commitState h) z
  have htransport : 0 < q.eventMass (h.Agrees ∘ assemble) := by
    rw [q.eventMass_congr (h.Agrees ∘ assemble) (fun z ↦ ∀ e, E e (z e)) hevent]
    exact FinDist.piProduct_eventMass_forall_pos ep E hE
  let readout := fun (x : Configuration N (HardVocabulary bankSize backgroundSize))
      (e : M.BatchEdge batch) ↦ (x e.1.1, x (M.mate e.1.1))
  have hreadout (z : M.EdgeIndex → HardVocabulary bankSize backgroundSize ×
      HardVocabulary bankSize backgroundSize) :
      (readout ∘ assemble) z = fun e : M.BatchEdge batch ↦ z e.1 := by
    funext e
    exact congrFun (M.toPairs_fromPairs z) e.1
  have hfree (e : M.BatchEdge batch) (z : HardVocabulary bankSize backgroundSize ×
      HardVocabulary bankSize backgroundSize) : E e.1 z := by
    have hl := commitState_none_of_fresh h batch fresh e.1.1 e.2.1
    have hr := commitState_none_of_fresh h batch fresh (M.mate e.1.1) e.2.2
    simp [E, PerfectMatching.edgeAgrees, hl, hr]
  calc
    _ = (target P M trigger).conditionalMap h.Agrees
        (h.probability_pos _ (target_strictlyPositive P M trigger)) readout := by
      simp only [History.jointBatchLaw, FinDist.conditionalMap, FinDist.map_comp]
      rfl
    _ = q.conditionalMap (h.Agrees ∘ assemble) htransport (readout ∘ assemble) :=
      FinDist.map_equiv_conditionalMap q assemble h.Agrees htransport readout
    _ = q.conditionalMap (fun z ↦ ∀ e, E e (z e))
        (FinDist.piProduct_eventMass_forall_pos ep E hE)
        (fun z (e : M.BatchEdge batch) ↦ z e.1) :=
      FinDist.conditionalMap_congr q _ _ _ _ _ _ hevent hreadout
    _ = _ := FinDist.piProduct_conditionalMap_unconstrained ep E hE
      (fun e : M.BatchEdge batch ↦ e.1) Subtype.val_injective hfree

/-- On wholly internal batch edges, the selected oracle independently uses
the common marginal at both endpoints. -/
theorem commitDistribution_map_batchPairs
    (P : HardLocalParameters bankSize backgroundSize) (M : PerfectMatching N)
    (trigger : Position N → Fin bankSize)
    (h : History N (HardVocabulary bankSize backgroundSize))
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) :
    ((selectedOracle P M trigger).commitDistribution h batch fresh).map
      (M.batchPairs batch) =
      FinDist.piProduct (fun _ : M.BatchEdge batch ↦
        P.commonMarginal.prod P.commonMarginal) := by
  classical
  let rows (j : batch) := (selectedOracle P M trigger).row
    (MaskedState.commitState h) (FrozenOracle.commitReadout h batch fresh j)
  let f := M.batchEndpoint batch
  have hrow (j : M.BatchEdge batch ⊕ M.BatchEdge batch) : rows (f j) =
      P.commonMarginal := by
    cases j with
    | inl e =>
        have hm := commitState_none_of_fresh h batch fresh (M.mate e.1.1) e.2.2
        simp [rows, f, PerfectMatching.batchEndpoint, FrozenOracle.commitReadout,
          selectedRow, hm]
    | inr e =>
        have hm := commitState_none_of_fresh h batch fresh e.1.1 e.2.1
        simp [rows, f, PerfectMatching.batchEndpoint, FrozenOracle.commitReadout,
          selectedRow, M.mate_mate e.1.1, hm]
  calc
    _ = ((FinDist.piProduct rows).map
          (fun x j ↦ x (f j))).map
          (fun x (e : M.BatchEdge batch) ↦ (x (Sum.inl e), x (Sum.inr e))) := by
      rw [FinDist.map_comp]
      rfl
    _ = (FinDist.piProduct (fun _ : M.BatchEdge batch ⊕ M.BatchEdge batch ↦
          P.commonMarginal)).map
          (fun x e ↦ (x (Sum.inl e), x (Sum.inr e))) := by
      rw [FinDist.piProduct_map_injective rows f (M.batchEndpoint_injective batch)]
      simp_rw [hrow]
    _ = _ := FinDist.piProduct_map_sum_pairs _

/-- Every edge wholly inside a fresh batch contributes its actual one-edge
affinity loss. Projection discards the other coordinates, which can only
increase affinity, so no independence claim about those coordinates is needed. -/
theorem jointBatch_affinity_le_edgeAffinity_pow
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize) (M : PerfectMatching N)
    (trigger : Position N → Fin bankSize)
    (h : History N (HardVocabulary bankSize backgroundSize))
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (s t : Fin bankSize) :
    FinDist.affinity
        (h.jointBatchLaw (target P M trigger) (target_strictlyPositive P M trigger) batch)
        ((selectedOracle P M trigger).commitDistribution h batch fresh) ≤
      (FinDist.affinity (P.edgeLaw s t)
        (P.commonMarginal.prod P.commonMarginal)) ^ Fintype.card (M.BatchEdge batch) := by
  classical
  have hproj := FinDist.affinity_map_ge
    (h.jointBatchLaw (target P M trigger) (target_strictlyPositive P M trigger) batch)
    ((selectedOracle P M trigger).commitDistribution h batch fresh)
    (M.batchPairs batch)
  rw [jointBatchLaw_map_batchPairs P M trigger h batch fresh,
    commitDistribution_map_batchPairs P M trigger h batch fresh,
    FinDist.affinity_piProduct] at hproj
  have hconst (e : M.BatchEdge batch) :
      FinDist.affinity (P.edgeLaw (trigger e.1.1) (trigger (M.mate e.1.1)))
        (P.commonMarginal.prod P.commonMarginal) =
      FinDist.affinity (P.edgeLaw s t) (P.commonMarginal.prod P.commonMarginal) := by
    rw [P.edgeLaw_affinity_formula, P.edgeLaw_affinity_formula]
  simpa only [hconst, Finset.prod_const, Finset.card_univ] using hproj

/-- Equivalent loss notation, using the actual trigger-independent edge
Hellinger loss rather than an assumed scalar penalty. -/
theorem jointBatch_affinity_le_one_sub_loss_pow
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize) (M : PerfectMatching N)
    (trigger : Position N → Fin bankSize)
    (h : History N (HardVocabulary bankSize backgroundSize))
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (s t : Fin bankSize) :
    FinDist.affinity
        (h.jointBatchLaw (target P M trigger) (target_strictlyPositive P M trigger) batch)
        ((selectedOracle P M trigger).commitDistribution h batch fresh) ≤
      (1 - FinDist.sqHellinger (P.edgeLaw s t)
        (P.commonMarginal.prod P.commonMarginal)) ^ Fintype.card (M.BatchEdge batch) := by
  simpa only [FinDist.sqHellinger, sub_sub_cancel] using
    jointBatch_affinity_le_edgeAffinity_pow P M trigger h batch fresh s t

end
end HardMatching

namespace Program

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Count the actual matching edges whose two endpoints occur in one commit
batch along a retained execution. Each commit uses the program's chosen batch. -/
def retainedMatchingCollisionCount (M : PerfectMatching N) (O : FrozenOracle N V) :
    {h : History N V} → (p : Program N V h) → RetainedPath O p → ℕ
  | _, .done _, _ => 0
  | _, .query state _ next, path =>
      retainedMatchingCollisionCount M O (next (O.readState state)) path
  | _, .commit batch _ _ next, path =>
      Fintype.card (M.BatchEdge batch) +
        retainedMatchingCollisionCount M O (next path.1) path.2

end Program

namespace Sampler

variable {N : ℕ} {V Seed : Type*} [Fintype V] [DecidableEq V]

/-- The number of within-batch matching edges in one fixed-seed sampler
execution, using its actual preprocessing and frozen query replies. -/
def matchingCollisionCount (A : Sampler N V Seed) (M : PerfectMatching N)
    (w : Seed) (O : FrozenOracle N V)
    (path : Program.RetainedPath O
      (A.program w (O.readState (MaskedState.allMask N V)))) : ℕ :=
  Program.retainedMatchingCollisionCount M O
    (A.program w (O.readState (MaskedState.allMask N V))) path

end Sampler

namespace HardMatching
variable {N bankSize backgroundSize : ℕ}

/-- The actual retained-path product loses at least the one-edge affinity
factor for every matching edge committed internally along that path. -/
theorem retainedAffinityWeight_le_edgeAffinity_pow
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize) (M : PerfectMatching N)
    (trigger : Position N → Fin bankSize)
    (O : FrozenOracle N (HardVocabulary bankSize backgroundSize))
    {h : History N (HardVocabulary bankSize backgroundSize)}
    (p : Program N (HardVocabulary bankSize backgroundSize) h)
    (path : Program.RetainedPath O p) (s t : Fin bankSize) :
    Program.retainedAffinityWeight O
        (BatchKernel.ofTarget (target P M trigger) (target_strictlyPositive P M trigger))
        (BatchKernel.ofOracle (selectedOracle P M trigger)) p path ≤
      (FinDist.affinity (P.edgeLaw s t) (P.commonMarginal.prod P.commonMarginal)) ^
        Program.retainedMatchingCollisionCount M O p path := by
  induction p with
  | done complete => simp [Program.retainedAffinityWeight, Program.retainedMatchingCollisionCount]
  | query state respects next ih => exact ih (O.readState state) path
  | @commit h batch nonempty fresh next ih =>
      rw [Program.retainedAffinityWeight, Program.retainedMatchingCollisionCount, pow_add]
      exact mul_le_mul
        (jointBatch_affinity_le_edgeAffinity_pow P M trigger h batch fresh s t)
        (ih path.1 path.2)
        (Program.retainedAffinityWeight_nonneg O _ _ (next path.1) path.2)
        (pow_nonneg (FinDist.affinity_nonneg _ _) _)

/-- The checked one-edge distance gives exponential damping in the number
of actual internal-edge collisions, with the manuscript's constant twelve. -/
theorem retainedAffinityWeight_le_exp_collisions
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize) (M : PerfectMatching N)
    (trigger : Position N → Fin bankSize)
    (O : FrozenOracle N (HardVocabulary bankSize backgroundSize))
    {h : History N (HardVocabulary bankSize backgroundSize)}
    (p : Program N (HardVocabulary bankSize backgroundSize) h)
    (path : Program.RetainedPath O p) (s t : Fin bankSize) :
    Program.retainedAffinityWeight O
        (BatchKernel.ofTarget (target P M trigger) (target_strictlyPositive P M trigger))
        (BatchKernel.ofOracle (selectedOracle P M trigger)) p path ≤
      Real.exp (-(P.edgeCoupling ^ 2 / 12) *
        (Program.retainedMatchingCollisionCount M O p path : ℝ)) := by
  have hedge := (P.edgeLaw_sqHellinger_bounds s t).1
  have hbase : FinDist.affinity (P.edgeLaw s t)
      (P.commonMarginal.prod P.commonMarginal) ≤ Real.exp (-(P.edgeCoupling ^ 2 / 12)) := by
    have hexp := Real.add_one_le_exp (-(P.edgeCoupling ^ 2 / 12))
    unfold FinDist.sqHellinger at hedge
    linarith
  calc
    _ ≤ _ := retainedAffinityWeight_le_edgeAffinity_pow P M trigger O p path s t
    _ ≤ Real.exp (-(P.edgeCoupling ^ 2 / 12)) ^
        Program.retainedMatchingCollisionCount M O p path :=
      pow_le_pow_left₀ (FinDist.affinity_nonneg _ _) hbase _
    _ = _ := by rw [← Real.exp_nat_mul, mul_comm]

/-- The exponential collision bound for the actual sampler midpoint weight. -/
theorem midpointPathWeight_le_exp_collisions
    [Nonempty (HardVocabulary bankSize backgroundSize)]
    (P : HardLocalParameters bankSize backgroundSize) (M : PerfectMatching N)
    (trigger : Position N → Fin bankSize) {Seed : Type*}
    (A : Sampler N (HardVocabulary bankSize backgroundSize) Seed) (w : Seed)
    (path : Program.RetainedPath (selectedOracle P M trigger)
      (A.program w ((selectedOracle P M trigger).readState
        (MaskedState.allMask N (HardVocabulary bankSize backgroundSize)))))
    (s t : Fin bankSize) :
    A.midpointPathWeight (model P M trigger) w (selectedOracle P M trigger) path ≤
      Real.exp (-(P.edgeCoupling ^ 2 / 12) *
        (A.matchingCollisionCount M w (selectedOracle P M trigger) path : ℝ)) :=
  retainedAffinityWeight_le_exp_collisions P M trigger (selectedOracle P M trigger)
    (A.program w ((selectedOracle P M trigger).readState
      (MaskedState.allMask N (HardVocabulary bankSize backgroundSize)))) path s t

end HardMatching
end ForestSampling
