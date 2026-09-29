import ForestSampling.ProgramKL

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

/-!
# Conditional factorization of the actual forest model

This module derives residual independence from the stored rooted-factorization
identity. Conditional independence is not added as an assumption to the model.
-/

namespace FinDist

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Normalize strictly positive weights on a finite nonempty type. -/
def ofPositiveWeights (w : α → ℝ) (hw : ∀ a, 0 < w a) : FinDist α where
  mass a := w a / ∑ b, w b
  nonneg a := div_nonneg (hw a).le
    (Finset.sum_nonneg fun b _ ↦ (hw b).le)
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self (Finset.sum_pos (fun a _ ↦ hw a) Finset.univ_nonempty).ne'

@[simp]
theorem ofPositiveWeights_apply (w : α → ℝ) (hw : ∀ a, 0 < w a) (a : α) :
    ofPositiveWeights w hw a = w a / ∑ b, w b := rfl

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {Ω : C → Type*} [∀ c, Fintype (Ω c)] [∀ c, Nonempty (Ω c)]

/-- A normalized positive density proportional to blockwise weights is the
product of the separately normalized block laws. -/
theorem eq_piProduct_of_mass_product (p : FinDist (∀ c, Ω c))
    (weights : ∀ c, Ω c → ℝ) (hweights : ∀ c a, 0 < weights c a)
    (scale : ℝ) (hmass : ∀ x, p x = scale * ∏ c, weights c (x c)) :
    p = piProduct (fun c ↦ ofPositiveWeights (weights c) (hweights c)) := by
  classical
  have hnormalization : scale * (∏ c, ∑ a, weights c a) = 1 := by
    calc
      scale * (∏ c, ∑ a, weights c a) =
          scale * ∑ x : ∀ c, Ω c, ∏ c, weights c (x c) := by
        rw [Fintype.prod_sum]
      _ = ∑ x, scale * ∏ c, weights c (x c) := Finset.mul_sum _ _ _
      _ = ∑ x, p x := Finset.sum_congr rfl (fun x _ ↦ (hmass x).symm)
      _ = 1 := p.sum_mass
  have hZ : (∏ c, ∑ a, weights c a) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro c _
    exact (Finset.sum_pos (fun a _ ↦ hweights c a) Finset.univ_nonempty).ne'
  ext x
  rw [hmass, piProduct_apply]
  simp only [ofPositiveWeights_apply, Finset.prod_div_distrib]
  apply (eq_div_iff hZ).2
  calc
    (scale * ∏ c, weights c (x c)) * (∏ c, ∑ a, weights c a) =
        (scale * ∏ c, ∑ a, weights c a) * ∏ c, weights c (x c) := by ring
    _ = ∏ c, weights c (x c) := by rw [hnormalization, one_mul]

end

end FinDist

namespace History

variable {N : ℕ} {V : Type*} [DecidableEq V]

/-- Reassemble a full configuration from fixed history values and all fresh
residual values. -/
def fillResidual (h : History N V) (z : ResidualVertex h → V) : Configuration N V :=
  fun i ↦ if hi : i ∈ h.committed then h.value ⟨i, hi⟩
    else z ⟨i, (h.mem_uncommitted_iff i).2 hi⟩

theorem fillResidual_agrees (h : History N V) (z : ResidualVertex h → V) :
    h.Agrees (h.fillResidual z) := by
  intro i
  simp [fillResidual, i.2]

@[simp]
theorem fillResidual_apply_fresh (h : History N V) (z : ResidualVertex h → V)
    (i : ResidualVertex h) : h.fillResidual z i.1 = z i := by
  have hi := (h.mem_uncommitted_iff i.1).mp i.2
  simp [fillResidual, hi]

theorem fillResidual_eq_of_agrees (h : History N V) (x : Configuration N V)
    (hx : h.Agrees x) : h.fillResidual (fun i ↦ x i.1) = x := by
  funext i
  by_cases hi : i ∈ h.committed
  · simpa [fillResidual, hi] using (hx ⟨i, hi⟩).symm
  · simp [fillResidual, hi]

/-- A history and all residual values specify exactly one full assignment. -/
theorem agrees_and_residual_iff (h : History N V) (z : ResidualVertex h → V)
    (x : Configuration N V) :
    h.Agrees x ∧ (fun i : ResidualVertex h ↦ x i.1) = z ↔ x = h.fillResidual z := by
  constructor
  · rintro ⟨hx, hz⟩
    rw [← hz]
    exact (h.fillResidual_eq_of_agrees x hx).symm
  · intro hx
    subst x
    exact ⟨h.fillResidual_agrees z, funext (h.fillResidual_apply_fresh z)⟩

variable [Fintype V] [Nonempty V]

/-- The exact conditional law of all residual values, omitting the already
fixed coordinates from its outcome type. -/
noncomputable def residualLaw (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (h : History N V) : FinDist (ResidualVertex h → V) :=
  p.conditionalMap h.Agrees (h.probability_pos p hp) (fun x i ↦ x i.1)

/-- Its point mass is the filled target assignment divided by the probability
of the committed history. -/
theorem residualLaw_apply (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (h : History N V) (z : ResidualVertex h → V) :
    h.residualLaw p hp z = p (h.fillResidual z) / h.probability p := by
  classical
  have hevent : p.eventMass
      (fun x ↦ h.Agrees x ∧ (fun i : ResidualVertex h ↦ x i.1) = z) =
      p (h.fillResidual z) := by
    unfold FinDist.eventMass
    simp_rw [h.agrees_and_residual_iff z]
    exact Fintype.sum_ite_eq' _ _
  calc
    h.residualLaw p hp z = p.eventMass
        (fun x ↦ h.Agrees x ∧ (fun i : ResidualVertex h ↦ x i.1) = z) /
          p.eventMass h.Agrees :=
      p.conditionalMap_apply_ratio h.Agrees (h.probability_pos p hp)
        (fun x (i : ResidualVertex h) ↦ x i.1) z
    _ = p (h.fillResidual z) / h.probability p := by rw [hevent]; rfl

/-- Reading a fresh batch from the residual conditional recovers its joint
conditional law as defined by the actual reference evaluator. -/
theorem residualLaw_map_batch (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (h : History N V) (batch : Finset (Position N))
    (fresh : batch ⊆ h.uncommitted) :
    (h.residualLaw p hp).map (fun x (j : batch) ↦ x ⟨j.1, fresh j.2⟩) =
      h.jointBatchLaw p hp batch := by
  simp only [residualLaw, jointBatchLaw, FinDist.conditionalMap,
    FinDist.map_comp, Function.comp_def]

end History

namespace FiniteBlocks

variable {A C V : Type*} [Fintype A] [Fintype C] [DecidableEq C]

/-- Rearrange a finite assignment into its blocks, without introducing extra
coordinates or forgetting any values. -/
def splitEquiv (label : A → C) : (A → V) ≃ ((c : C) → ({a // label a = c} → V)) where
  toFun x c a := x a.1
  invFun z a := z (label a) ⟨a, rfl⟩
  left_inv _ := rfl
  right_inv z := by
    funext c a
    obtain ⟨a, ha⟩ := a
    subst c
    rfl

/-- Replace the values in one block while retaining a fixed background
outside it. This only defines local factors for the algebraic decomposition. -/
def fillBlock (label : A → C) (background : A → V)
    (c : C) (z : {a // label a = c} → V) : A → V :=
  fun a ↦ if ha : label a = c then z ⟨a, ha⟩ else background a

omit [Fintype A] [Fintype C] in
@[simp]
theorem fillBlock_apply (label : A → C) (background : A → V)
    (c : C) (z : {a // label a = c} → V) (a : A) (ha : label a = c) :
    fillBlock label background c z a = z ⟨a, ha⟩ := by
  simp [fillBlock, ha]

variable {J : Type*} [Fintype J]

/-- Group local factors according to the unique variable block on which
each one depends. -/
noncomputable def blockWeight (label : A → C) (background : A → V)
    (which : J → C) (factor : J → (A → V) → ℝ)
    (c : C) (z : {a // label a = c} → V) : ℝ :=
  ∏ j : {j // which j = c}, factor j.1 (fillBlock label background c z)

omit [Fintype A] in
theorem prod_eq_prod_blockWeight (label : A → C) (background : A → V)
    (which : J → C) (factor : J → (A → V) → ℝ)
    (hdepends : ∀ j x y,
      (∀ a, label a = which j → x a = y a) → factor j x = factor j y)
    (x : A → V) :
    (∏ j, factor j x) = ∏ c, blockWeight label background which factor c
      (splitEquiv label x c) := by
  classical
  rw [← Fintype.prod_fiberwise which (fun j ↦ factor j x)]
  apply Finset.prod_congr rfl
  intro c _
  unfold blockWeight
  apply Finset.prod_congr rfl
  intro j _
  apply hdepends j.1
  intro a ha
  have hac : label a = c := ha.trans j.2
  simp [fillBlock, hac, splitEquiv]

end FiniteBlocks

namespace FinDist

variable {C I V : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]
variable [Fintype V] [DecidableEq V]
variable {Ω : C → Type*} [∀ c, Fintype (Ω c)]

/-- Reading one arbitrary function from each of distinct independent blocks
gives the product of those readout laws. The block types may differ. -/
theorem piProduct_map_distinct_blocks (laws : ∀ c, FinDist (Ω c))
    (select : I → C) (hselect : Function.Injective select)
    (readout : (i : I) → Ω (select i) → V) :
    (piProduct laws).map (fun x i ↦ readout i (x (select i))) =
      piProduct (fun i ↦ (laws (select i)).map (readout i)) := by
  classical
  ext z
  let E : (c : C) → Ω c → Prop :=
    fun c y ↦ ∀ (i : I) (hi : select i = c), readout i (hi.symm ▸ y) = z i
  have hevent (x : ∀ c, Ω c) :
      (fun i ↦ readout i (x (select i))) = z ↔ ∀ c, E c (x c) := by
    constructor
    · intro hx c i hi
      subst c
      exact congrFun hx i
    · intro hx
      funext i
      exact hx (select i) i rfl
  have hselected (i : I) (y : Ω (select i)) :
      E (select i) y ↔ readout i y = z i := by
    constructor
    · intro hy
      exact hy i rfl
    · intro hy j hj
      have hji : j = i := hselect hj
      subst j
      simpa using hy
  have hunselected (c : C) (hc : c ∉ Set.range select) :
      (laws c).eventMass (E c) = 1 := by
    calc
      (laws c).eventMass (E c) = (laws c).eventMass (fun _ ↦ True) := by
        apply (laws c).eventMass_congr
        intro y
        constructor
        · intro _
          trivial
        · intro _ i hi
          exact False.elim (hc ⟨i, hi⟩)
      _ = 1 := (laws c).eventMass_true
  have hprod := Fintype.prod_of_injective select hselect
    (fun i ↦ (laws (select i)).eventMass (fun y ↦ readout i y = z i))
    (fun c ↦ (laws c).eventMass (E c)) hunselected
    (fun i ↦ (laws (select i)).eventMass_congr _ _ (fun y ↦ (hselected i y).symm))
  change (piProduct laws).eventMass
      (fun x ↦ (fun i ↦ readout i (x (select i))) = z) =
    ∏ i, (laws (select i)).eventMass (fun y ↦ readout i y = z i)
  rw [(piProduct laws).eventMass_congr _ _ hevent]
  exact (piProduct_eventMass_forall laws E).trans hprod.symm

end FinDist

namespace ForestModel

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The root marginal or parent-to-child kernel attached to one rooted vertex. -/
def vertexFactor (M : ForestModel N V) (j : Position N) (x : Configuration N V) : ℝ :=
  if j ∈ M.rooting.roots then M.marginal j (x j)
    else M.kernel (M.rooting.parent j) j (x (M.rooting.parent j)) (x j)

theorem vertexFactor_pos (M : ForestModel N V) (j : Position N)
    (x : Configuration N V) : 0 < M.vertexFactor j x := by
  unfold vertexFactor
  split
  · exact M.marginal_strictlyPositive j (x j)
  · rename_i hj
    exact M.kernel_positive (M.rooting.parent_adj j hj) _ _

/-- The stored forest factorization is a product of one local factor per
vertex. This is merely a reindexing of the model's actual assumption. -/
theorem target_eq_prod_vertexFactor (M : ForestModel N V) (x : Configuration N V) :
    M.target x = ∏ j, M.vertexFactor j x := by
  classical
  rw [M.factorizes x]
  unfold ForestFactorization.mass vertexFactor marginal
  rw [Finset.prod_ite]
  congr 1
  · congr 1
    ext j
    simp
  · congr 1
    ext j
    simp [Rooting.nonRoots]

/-- Assign a local factor to a residual block containing its varying endpoint.
If its child is committed but its parent is residual, retain the factor in
the parent's block. Fully committed factors are assigned to `none`. -/
def vertexBlock {C : Type*} (M : ForestModel N V) (h : History N V)
    (label : ResidualVertex h → C) (j : Position N) : Option C :=
  if hj : j ∈ h.uncommitted then some (label ⟨j, hj⟩)
    else if hp : M.rooting.parent j ∈ h.uncommitted then
      some (label ⟨M.rooting.parent j, hp⟩) else none

/-- An actual rooted factor depends only on the block to which it was assigned,
provided adjacent residual endpoints have the same block label. -/
theorem vertexFactor_depends_on_block {C : Type*} (M : ForestModel N V)
    (h : History N V) (label : ResidualVertex h → C)
    (hseparated : ∀ u v : ResidualVertex h,
      M.graph.Adj u.1 v.1 → label u = label v)
    (j : Position N) (x y : ResidualVertex h → V)
    (hagree : ∀ a : ResidualVertex h,
      some (label a) = M.vertexBlock h label j → x a = y a) :
    M.vertexFactor j (h.fillResidual x) = M.vertexFactor j (h.fillResidual y) := by
  have hchild : h.fillResidual x j = h.fillResidual y j := by
    by_cases hj : j ∈ h.committed
    · simp [History.fillResidual, hj]
    · have hju : j ∈ h.uncommitted := (h.mem_uncommitted_iff j).2 hj
      have hl := hagree ⟨j, hju⟩ (by simp [vertexBlock, hju])
      simpa [History.fillResidual, hj] using hl
  unfold vertexFactor
  split
  · rw [hchild]
  · rename_i hroot
    have hparent : h.fillResidual x (M.rooting.parent j) =
        h.fillResidual y (M.rooting.parent j) := by
      by_cases hp : M.rooting.parent j ∈ h.committed
      · simp [History.fillResidual, hp]
      · have hpu : M.rooting.parent j ∈ h.uncommitted :=
          (h.mem_uncommitted_iff _).2 hp
        have hblock : some (label ⟨M.rooting.parent j, hpu⟩) =
            M.vertexBlock h label j := by
          by_cases hju : j ∈ h.uncommitted
          · rw [vertexBlock, dif_pos hju]
            exact congrArg some
              (hseparated ⟨M.rooting.parent j, hpu⟩ ⟨j, hju⟩
                (M.rooting.parent_adj j hroot))
          · simp [vertexBlock, hju, hpu]
        have hl := hagree ⟨M.rooting.parent j, hpu⟩ hblock
        simpa [History.fillResidual, hp] using hl
    rw [hparent, hchild]

variable [Nonempty V]

/-- Actual forest conditionals factor over any finite partition that does not
split a residual edge. The extra `none` block is empty and holds only factors
whose endpoints are already committed. -/
theorem residualLaw_factorizes_over_blocks {C : Type*} [Fintype C] [DecidableEq C]
    (M : ForestModel N V) (h : History N V) (label : ResidualVertex h → C)
    (hseparated : ∀ u v : ResidualVertex h,
      M.graph.Adj u.1 v.1 → label u = label v) :
    ∃ laws : (c : Option C) → FinDist ({a : ResidualVertex h // some (label a) = c} → V),
      (h.residualLaw M.target M.target_positive).map
          (FiniteBlocks.splitEquiv (fun a ↦ some (label a))) =
        FinDist.piProduct laws := by
  classical
  let labels : ResidualVertex h → Option C := fun a ↦ some (label a)
  let background : ResidualVertex h → V := fun _ ↦ Classical.choice ‹Nonempty V›
  let factor : Position N → (ResidualVertex h → V) → ℝ :=
    fun j x ↦ M.vertexFactor j (h.fillResidual x)
  let weights : (c : Option C) → ({a : ResidualVertex h // labels a = c} → V) → ℝ :=
    FiniteBlocks.blockWeight labels background (M.vertexBlock h label) factor
  have hw : ∀ c z, 0 < weights c z := by
    intro c z
    apply Finset.prod_pos
    intro j _
    exact M.vertexFactor_pos j.1 _
  refine ⟨fun c ↦ FinDist.ofPositiveWeights (weights c) (hw c), ?_⟩
  apply FinDist.eq_piProduct_of_mass_product _ weights hw (1 / h.probability M.target)
  intro x
  rw [FinDist.map_equiv_apply, History.residualLaw_apply, M.target_eq_prod_vertexFactor]
  have hgroup := FiniteBlocks.prod_eq_prod_blockWeight labels background
    (M.vertexBlock h label) factor
    (fun j a b heq ↦ M.vertexFactor_depends_on_block h label hseparated j a b heq)
    ((FiniteBlocks.splitEquiv labels).symm x)
  simp only [Equiv.apply_symm_apply] at hgroup
  change (∏ j, factor j ((FiniteBlocks.splitEquiv labels).symm x)) /
      h.probability M.target = (1 / h.probability M.target) * ∏ c, weights c (x c)
  rw [hgroup]
  ring

/-- Selecting at most one coordinate from each separated residual block
produces conditionally independent singleton readouts. -/
theorem jointBatchLaw_factorizes_of_separated_labels
    {C : Type*} [Fintype C] [DecidableEq C]
    (M : ForestModel N V) (h : History N V) (label : ResidualVertex h → C)
    (hseparated : ∀ u v : ResidualVertex h,
      M.graph.Adj u.1 v.1 → label u = label v)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (hselect : Function.Injective (fun j : batch ↦ label ⟨j.1, fresh j.2⟩)) :
    h.jointBatchLaw M.target M.target_positive batch =
      FinDist.piProduct (h.jointBatchLaw M.target M.target_positive batch).piMarginal := by
  classical
  obtain ⟨laws, hlaws⟩ := M.residualLaw_factorizes_over_blocks h label hseparated
  let select : batch → Option C := fun j ↦ some (label ⟨j.1, fresh j.2⟩)
  have hselect' : Function.Injective select := by
    intro i j hij
    exact hselect (Option.some.inj hij)
  let readout : (j : batch) →
      ({a : ResidualVertex h // some (label a) = select j} → V) → V :=
    fun j z ↦ z ⟨⟨j.1, fresh j.2⟩, rfl⟩
  have hproject :
      (FinDist.piProduct laws).map (fun x (j : batch) ↦ readout j (x (select j))) =
        h.jointBatchLaw M.target M.target_positive batch := by
    rw [← hlaws, FinDist.map_comp]
    exact h.residualLaw_map_batch M.target M.target_positive batch fresh
  have hproduct : h.jointBatchLaw M.target M.target_positive batch =
      FinDist.piProduct (fun j ↦ (laws (select j)).map (readout j)) :=
    hproject.symm.trans (FinDist.piProduct_map_distinct_blocks laws select hselect' readout)
  have hmarg (j : batch) :
      (h.jointBatchLaw M.target M.target_positive batch).piMarginal j =
        (laws (select j)).map (readout j) := by
    rw [hproduct, FinDist.piMarginal_piProduct]
  calc
    h.jointBatchLaw M.target M.target_positive batch =
        FinDist.piProduct (fun j ↦ (laws (select j)).map (readout j)) := hproduct
    _ = FinDist.piProduct
        (h.jointBatchLaw M.target M.target_positive batch).piMarginal := by
      congr 1
      funext j
      exact (hmarg j).symm

/-- Structural safety means no two selected vertices lie in the same true
residual connected component. -/
def BatchStructurallySafe (M : ForestModel N V) (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) : Prop :=
  Function.Injective (fun j : batch ↦
    (residualGraph M.graph h).connectedComponentMk ⟨j.1, fresh j.2⟩)

/-- The actual residual graph implies conditional independence of a safe
batch, by the rooted target factorization proved above. -/
theorem jointBatchLaw_factorizes_of_safe (M : ForestModel N V) (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (hsafe : M.BatchStructurallySafe h batch fresh) :
    h.jointBatchLaw M.target M.target_positive batch =
      FinDist.piProduct (h.jointBatchLaw M.target M.target_positive batch).piMarginal := by
  classical
  let _ : Fintype (residualGraph M.graph h).ConnectedComponent := Fintype.ofFinite _
  apply M.jointBatchLaw_factorizes_of_separated_labels h
    (residualGraph M.graph h).connectedComponentMk _ batch fresh hsafe
  intro u v huv
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (G := residualGraph M.graph h) huv

/-- A safe true joint conditional equals the product of the target's exact
mandatory commit-state rows. This is the exact-hybrid safety bridge. -/
theorem jointBatchLaw_eq_exactCommit_of_safe (M : ForestModel N V) (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted)
    (hsafe : M.BatchStructurallySafe h batch fresh) :
    h.jointBatchLaw M.target M.target_positive batch =
      (FrozenOracle.exact M).commitDistribution h batch fresh := by
  rw [M.jointBatchLaw_factorizes_of_safe h batch fresh hsafe]
  change FinDist.piProduct _ = FinDist.piProduct _
  congr 1
  funext j
  change (h.jointBatchLaw M.target M.target_positive batch).map (fun z ↦ z j) =
    (MaskedState.commitState h).exactRow M.target M.target_positive
      (FrozenOracle.commitReadout h batch fresh j)
  rw [History.jointBatchLaw_map_eval, MaskedState.exactRow_commitState]
  rfl

omit [Nonempty V] in
/-- A singleton batch is structurally safe for every target forest. -/
theorem batchStructurallySafe_singleton (M : ForestModel N V) (h : History N V)
    (j : Position N) (fresh : {j} ⊆ h.uncommitted) :
    M.BatchStructurallySafe h {j} fresh := by
  intro a b _
  apply Subtype.ext
  exact (Finset.mem_singleton.mp a.2).trans (Finset.mem_singleton.mp b.2).symm

end ForestModel

namespace Program

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Every batch selected by this fixed-oracle program is safe in the actual
target residual graph. Query replies remain the frozen oracle's replies. -/
def StructurallySafe (M : ForestModel N V) (O : FrozenOracle N V) :
    {h : History N V} → Program N V h → Prop
  | _, .done _ => True
  | _, .query state _ next => StructurallySafe M O (next (O.readState state))
  | h, .commit batch _ fresh next =>
      M.BatchStructurallySafe h batch fresh ∧ ∀ z, StructurallySafe M O (next z)

/-- Graph-based structural safety implies the exact conditional factorization
property on every retained path; this implication is proved from the stored
forest factorization, rather than imposed as a stochastic assumption. -/
theorem pathBatchesFactorize_of_structurallySafe (M : ForestModel N V)
    (O : FrozenOracle N V) {h : History N V} (p : Program N V h)
    (hsafe : StructurallySafe M O p) (path : RetainedPath O p) :
    PathBatchesFactorize M.target M.target_positive O p path := by
  induction p with
  | done complete => trivial
  | query state respects next ih => exact ih (O.readState state) hsafe path
  | @commit h batch nonempty fresh next ih =>
      exact ⟨M.jointBatchLaw_factorizes_of_safe h batch fresh hsafe.1,
        ih path.1 (hsafe.2 path.1) path.2⟩

/-- Safe exact-singleton product commits reproduce the true target conditional
from every starting history, including arbitrary adaptive frozen queries. -/
theorem exactCommitEval_eq_conditionalLaw_of_safe (M : ForestModel N V)
    (O : FrozenOracle N V) {h : History N V} (p : Program N V h)
    (hsafe : StructurallySafe M O p) :
    exactCommitEval M O p = h.conditionalLaw M.target M.target_positive := by
  induction p with
  | @done h complete =>
      exact (h.conditionalLaw_of_complete M.target M.target_positive complete).symm
  | query state respects next ih => exact ih (O.readState state) hsafe
  | @commit h batch nonempty fresh next ih =>
      change ((FrozenOracle.exact M).commitDistribution h batch fresh).bind
        (fun z ↦ exactCommitEval M O (next z)) = _
      rw [← M.jointBatchLaw_eq_exactCommit_of_safe h batch fresh hsafe.1]
      calc
        (h.jointBatchLaw M.target M.target_positive batch).bind
            (fun z ↦ exactCommitEval M O (next z)) =
            (h.jointBatchLaw M.target M.target_positive batch).bind
              (fun z ↦ (h.appendBatch batch fresh z).conditionalLaw
                M.target M.target_positive) := by
          congr 1
          funext z
          exact ih z (hsafe.2 z)
        _ = h.conditionalLaw M.target M.target_positive :=
          h.jointBatchLaw_bind_conditionalLaw M.target M.target_positive batch fresh

end Program

namespace Sampler

variable {N : ℕ} {V Seed : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V]

/-- The exact-row hybrid of an actually structurally safe controller equals
the target law, for each fixed seed and frozen oracle. -/
theorem exactCommitOutputLaw_eq_target_of_safe (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V)
    (hsafe : Program.StructurallySafe M O
      (A.program w (O.readState (MaskedState.allMask N V)))) :
    A.exactCommitOutputLaw M w O = M.target := by
  unfold exactCommitOutputLaw
  rw [Program.exactCommitEval_eq_conditionalLaw_of_safe M O _ hsafe,
    History.conditionalLaw_empty]

/-- The manuscript's safe-controller TV guarantee, now using structural
independence derived from the actual forest factorization. -/
theorem output_tv_le_of_structurallySafe (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V)
    (oracleRadius : ℝ) (hN : 0 < N) (haccuracy : O.Accurate M oracleRadius)
    (hsafe : Program.StructurallySafe M O
      (A.program w (O.readState (MaskedState.allMask N V)))) :
    FinDist.tv M.target (A.outputLaw w O) ≤ oracleRadius := by
  have h := A.tv_exactCommitOutputLaw_le M w O oracleRadius hN haccuracy
  rwa [A.exactCommitOutputLaw_eq_target_of_safe M w O hsafe] at h

/-- Structural safety eliminates total correlation on every true-reference
path, including paths selected adaptively by frozen oracle replies. -/
theorem referenceTotalCorrelation_eq_zero_of_safe (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V)
    (hsafe : Program.StructurallySafe M O
      (A.program w (O.readState (MaskedState.allMask N V))))
    (path : Program.RetainedPath O
      (A.program w (O.readState (MaskedState.allMask N V)))) :
    A.referenceTotalCorrelation M w O path = 0 :=
  Program.retainedTotalCorrelation_eq_zero_of_factorizes M.target M.target_positive O _ path
    (Program.pathBatchesFactorize_of_structurallySafe M O _ hsafe path)

/-- A structurally safe sampler incurs only its singleton row-KL budget. -/
theorem output_klDivergence_le_of_structurallySafe (A : Sampler N V Seed)
    (M : ForestModel N V) (w : Seed) (O : FrozenOracle N V)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.klDivergence (y.exactRow M.target M.target_positive j) (O.row y j) ≤ κ)
    (hsafe : Program.StructurallySafe M O
      (A.program w (O.readState (MaskedState.allMask N V)))) :
    FinDist.klDivergence M.target (A.outputLaw w O) ≤ (N : ℝ) * κ := by
  have h := A.output_klDivergence_le_reference_failure_mass M w O κ hκ hrows
    (fun _ ↦ False) (fun path _ ↦
      Program.pathBatchesFactorize_of_structurallySafe M O _ hsafe path)
  simpa only [FinDist.eventMass, if_false, Finset.sum_const_zero, mul_zero, add_zero] using h

end Sampler

end ForestSampling
