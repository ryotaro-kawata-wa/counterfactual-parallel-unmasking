import ForestSampling.ObservedProgram
import ForestSampling.AdaptiveMidpoint

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling

universe u v w

namespace FinDist

variable {A : Type u} {B : Type v} {C : Type w}
  [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- Total variation is unchanged by a bijective relabeling. -/
theorem tv_map_equiv (p q : FinDist A) (e : A ≃ B) :
    tv (p.map e) (q.map e) = tv p q := by
  unfold tv
  rw [← e.sum_comp]
  simp only [map_equiv_apply, Equiv.symm_apply_apply]

@[simp]
theorem map_equiv_symm (p : FinDist A) (e : A ≃ B) :
    (p.map e).map e.symm = p := by
  rw [map_comp]
  have he : (e.symm : B → A) ∘ e = id := by funext a; simp
  rw [he, map_id]

/-- A point mass transports to the corresponding point mass. -/
theorem dirac_map_equiv (a : A) (e : A ≃ B) :
    (dirac a).map e = dirac (e a) := by
  ext b
  rw [map_equiv_apply]
  simp [dirac, Equiv.symm_apply_eq]

/-- Simultaneous bijective transport of the draw and its continuation. -/
theorem bind_map_equiv (p : FinDist A) (k : A → FinDist C) (e : A ≃ B)
    {D : Type*} [Fintype D] [DecidableEq D] (f : C ≃ D) :
    (p.map e).bind (fun b ↦ (k (e.symm b)).map f) = (p.bind k).map f := by
  ext d
  rw [map_equiv_apply]
  change (∑ b, p.map e b * (k (e.symm b)).map f d) = _
  simp only [map_equiv_apply]
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Coordinatewise relabeling preserves an independent product law. -/
theorem piProduct_map_equiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → FinDist A) (e : A ≃ B) :
    (piProduct p).map (Equiv.piCongrRight fun _ : ι ↦ e) =
      piProduct (fun i ↦ (p i).map e) := by
  ext z
  rw [map_equiv_apply]
  simp only [piProduct_apply, map_equiv_apply]
  rfl

end FinDist

/-! The same finite sampling problem under a public bijection of token
labels. Coordinates, committed sets, and resource counts remain fixed. -/
namespace VocabularyEquivalence

variable {N : ℕ} {V : Type u} {W : Type v}
  [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Pointwise token relabeling of a completed assignment. -/
def configuration (e : V ≃ W) : Configuration N V ≃ Configuration N W :=
  Equiv.piCongrRight fun _ ↦ e

@[simp] theorem configuration_apply (e : V ≃ W) (x : Configuration N V) (i : Position N) :
    configuration e x i = e (x i) := rfl

@[simp] theorem configuration_symm (e : V ≃ W) :
    (configuration (N := N) e).symm = configuration e.symm := rfl

/-- History relabeling leaves its committed coordinate set unchanged. -/
def history (e : V ≃ W) (h : History N V) : History N W where
  committed := h.committed
  value i := e (h.value i)

@[simp] theorem history_committed (e : V ≃ W) (h : History N V) :
    (history e h).committed = h.committed := rfl

@[simp] theorem history_uncommitted (e : V ≃ W) (h : History N V) :
    (history e h).uncommitted = h.uncommitted := rfl

@[simp] theorem history_symm (e : V ≃ W) (h : History N V) :
    history e.symm (history e h) = h := by
  cases h with
  | mk committed value =>
    simp only [history, Equiv.symm_apply_apply]

@[simp] theorem history_empty (e : V ≃ W) :
    history e (History.empty N V) = History.empty N W := by
  unfold history History.empty
  congr 1
  funext i
  exact False.elim (Finset.notMem_empty _ i.2)

/-- Relabeling commutes with recording the realized fresh batch. -/
theorem history_appendBatch (e : V ≃ W) (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) (z : batch → V) :
    history e (h.appendBatch batch fresh z) =
      (history e h).appendBatch batch fresh (fun i ↦ e (z i)) := by
  unfold history History.appendBatch
  congr 1
  funext i
  by_cases hi : i.1 ∈ h.committed <;> simp [hi]

@[simp] theorem history_completedConfiguration (e : V ≃ W) (h : History N V)
    (complete : h.committed = Finset.univ) :
    (history e h).completedConfiguration complete = configuration e (h.completedConfiguration complete) := rfl

/-- Mask symbols are fixed while observed tokens are relabeled. -/
def state (e : V ≃ W) (y : MaskedState N V) : MaskedState N W :=
  fun i ↦ (y i).map e

@[simp] theorem state_symm (e : V ≃ W) (y : MaskedState N V) :
    state e.symm (state e y) = y := by
  funext i
  cases hi : y i <;> simp [state, hi]

@[simp] theorem state_masked (e : V ≃ W) (y : MaskedState N V) :
    (state e y).masked = y.masked := by
  ext i
  simp [state]

@[simp] theorem state_allMask (e : V ≃ W) :
    state e (MaskedState.allMask N V) = MaskedState.allMask N W := rfl

@[simp] theorem state_commitState (e : V ≃ W) (h : History N V) :
    state e (MaskedState.commitState h) = MaskedState.commitState (history e h) := by
  funext i
  simp only [state, MaskedState.commitState, history]
  by_cases hi : i ∈ h.committed <;> simp [hi]

/-- The masked position itself is unchanged by token relabeling. -/
def maskedPosition (e : V ≃ W) (y : MaskedState N V) :
    MaskedPosition y ≃ MaskedPosition (state e y) where
  toFun j := ⟨j.1, by simpa using j.2⟩
  invFun j := ⟨j.1, by simpa using j.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem maskedPosition_val (e : V ≃ W) (y : MaskedState N V) (j : MaskedPosition y) :
    (maskedPosition e y j).1 = j.1 := rfl

/-- Relabeling preserves the mandatory agreement with committed values. -/
theorem state_respects (e : V ≃ W) (y : MaskedState N V) (h : History N V)
    (hy : y.RespectsHistory h) : (state e y).RespectsHistory (history e h) := by
  intro i
  change (y i.1).map e = some (e (h.value i))
  rw [hy i]
  rfl

/-- The public frozen oracle transported to the new token alphabet. -/
def oracle (e : V ≃ W) (O : FrozenOracle N V) : FrozenOracle N W where
  row y j := (O.row (state e.symm y) (maskedPosition e.symm y j)).map e
  row_positive y j := FinDist.map_strictlyPositive_of_surjective _
    (O.row_positive _ _) e e.surjective

/-- The explicit pullback-state and pushforward-row formula. -/
theorem oracle_row (e : V ≃ W) (O : FrozenOracle N V) (y : MaskedState N W)
    (j : MaskedPosition y) :
    (oracle e O).row y j = (O.row (state e.symm y) (maskedPosition e.symm y j)).map e := rfl

/-- On the corresponding submitted state, each corresponding row has
exactly its original probability masses with token names changed. -/
theorem oracle_row_state (e : V ≃ W) (O : FrozenOracle N V) (y : MaskedState N V)
    (j : MaskedPosition y) :
    (oracle e O).row (state e y) (maskedPosition e y j) = (O.row y j).map e := by
  change (O.row (state e.symm (state e y)) _).map e = _
  have row_congr : ∀ (y' : MaskedState N V) (hy : y' = y) (j' : MaskedPosition y'),
      j'.1 = j.1 → O.row y' j' = O.row y j := by
    intro y' hy j' hj
    subst y'
    congr 1
    exact Subtype.ext hj
  exact congrArg (fun p : FinDist V ↦ p.map e)
    (row_congr _ (state_symm e y) _ rfl)

/-- Transporting an oracle and then restoring its labels is exact. -/
@[simp] theorem oracle_symm (e : V ≃ W) (O : FrozenOracle N V) :
    oracle e.symm (oracle e O) = O := by
  have hr : (oracle e.symm (oracle e O)).row = O.row := by
    funext y j
    change ((oracle e O).row (state e y) (maskedPosition e y j)).map e.symm = _
    rw [oracle_row_state, FinDist.map_equiv_symm]
  have ext_oracle (O₁ O₂ : FrozenOracle N V) (heq : O₁.row = O₂.row) : O₁ = O₂ := by
    cases O₁
    cases O₂
    cases heq
    rfl
  exact ext_oracle _ _ hr

/-- The fresh-batch history identity in the direction used by a
controller translated to the new alphabet. -/
theorem history_appendBatch_pullback (e : V ≃ W) (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) (z : batch → W) :
    history e (h.appendBatch batch fresh (fun i ↦ e.symm (z i))) =
      (history e h).appendBatch batch fresh z := by
  rw [history_appendBatch]
  simp only [Equiv.apply_symm_apply]

/-- Probability rows returned at a commit transport coordinatewise. -/
theorem oracle_commitRows (e : V ≃ W) (O : FrozenOracle N V) (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) (j : batch) :
    (oracle e O).commitRows (history e h) batch fresh j =
      (O.commitRows h batch fresh j).map e := by
  have hx := oracle_row_state e O (MaskedState.commitState h)
    (FrozenOracle.commitReadout h batch fresh j)
  have row_congr (y y' : MaskedState N W) (hy : y = y')
      (j : MaskedPosition y) (j' : MaskedPosition y') (hj : j.1 = j'.1) :
      (oracle e O).row y j = (oracle e O).row y' j' := by
    subst y'
    have heq : j = j' := Subtype.ext hj
    subst j'
    rfl
  exact (row_congr _ _ (state_commitState e h) _
    (FrozenOracle.commitReadout (history e h) batch fresh j) rfl).symm.trans hx

/-- The actual independent commit draw has the transported product law. -/
theorem oracle_commitDistribution (e : V ≃ W) (O : FrozenOracle N V) (h : History N V)
    (batch : Finset (Position N)) (fresh : batch ⊆ h.uncommitted) :
    (oracle e O).commitDistribution (history e h) batch fresh =
      (O.commitDistribution h batch fresh).map (Equiv.piCongrRight fun _ : batch ↦ e) := by
  change FinDist.piProduct _ = (FinDist.piProduct _).map _
  rw [FinDist.piProduct_map_equiv]
  congr 1
  funext j
  exact oracle_commitRows e O h batch fresh j

end VocabularyEquivalence
end ForestSampling
