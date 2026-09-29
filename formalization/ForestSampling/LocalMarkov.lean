import ForestSampling.ForestConditionals

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

/-!
# The local Markov property of the actual forest law

The singleton conditional below is derived from the rooted factorization.
Every conditioning event is the actual masked-state agreement event.
-/

namespace FinDist

variable {V : Type*} [Fintype V] [Nonempty V]

/-- Positive relative weights determine a finite probability law uniquely. -/
theorem eq_ofPositiveWeights_of_cross_mul (p : FinDist V) (w : V → ℝ)
    (hw : ∀ a, 0 < w a)
    (hcross : ∀ a b, p a * w b = p b * w a) :
    p = ofPositiveWeights w hw := by
  ext a
  rw [ofPositiveWeights_apply]
  apply (eq_div_iff
    (Finset.sum_pos (fun b _ ↦ hw b) Finset.univ_nonempty).ne').2
  calc
    p a * (∑ b, w b) = ∑ b, p a * w b := Finset.mul_sum _ _ _
    _ = ∑ b, p b * w a := Finset.sum_congr rfl (fun b _ ↦ hcross a b)
    _ = (∑ b, p b) * w a := (Finset.sum_mul _ _ _).symm
    _ = w a := by rw [p.sum_mass, one_mul]

end FinDist

namespace MaskedState

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Fill a singled-out coordinate and retain all remaining coordinates. -/
def fillExcept (j : Position N) (a : V) (t : {i : Position N // i ≠ j} → V) :
    Configuration N V := (Equiv.piSplitAt j (fun _ : Position N ↦ V)).symm (a, t)

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem fillExcept_self (j : Position N) (a : V)
    (t : {i : Position N // i ≠ j} → V) : fillExcept j a t j = a := by
  simp [fillExcept, Equiv.piSplitAt]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem fillExcept_other (j : Position N) (a : V)
    (t : {i : Position N // i ≠ j} → V) (i : Position N) (hi : i ≠ j) :
    fillExcept j a t i = t ⟨i, hi⟩ := by
  simp [fillExcept, Equiv.piSplitAt, hi]

omit [Fintype V] [DecidableEq V] in
/-- Updating the singled-out coordinate only changes its explicit value. -/
theorem update_fillExcept (j : Position N) (a b : V)
    (t : {i : Position N // i ≠ j} → V) :
    Function.update (fillExcept j a t) j b = fillExcept j b t := by
  funext i
  by_cases hi : i = j
  · subst i; simp
  · simp [hi]

omit [Fintype V] [DecidableEq V] in
/-- Changing a masked coordinate preserves all submitted observations. -/
theorem agrees_fillExcept_iff (y : MaskedState N V) (j : Position N)
    (hj : y j = none) (a b : V) (t : {i : Position N // i ≠ j} → V) :
    y.Agrees (fillExcept j a t) ↔ y.Agrees (fillExcept j b t) := by
  have haux (a b : V) :
      y.Agrees (fillExcept j a t) → y.Agrees (fillExcept j b t) := by
    intro ha i c hic
    have hij : i ≠ j := by
      intro h; subst i; simp [hj] at hic
    simpa [hij] using ha i c hic
  exact ⟨haux a b, haux b a⟩

/-- Sum a singleton event over just the remaining coordinates. -/
theorem eventMass_agrees_eval (p : FinDist (Configuration N V))
    (y : MaskedState N V) (j : Position N) (a : V) :
    p.eventMass (fun x ↦ y.Agrees x ∧ x j = a) =
      ∑ t : {i : Position N // i ≠ j} → V,
        if y.Agrees (fillExcept j a t) then p (fillExcept j a t) else 0 := by
  classical
  unfold FinDist.eventMass
  rw [← (Equiv.piSplitAt j (fun _ : Position N ↦ V)).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  change (∑ b : V, if y.Agrees (fillExcept j b t) ∧
      fillExcept j b t j = a then p (fillExcept j b t) else 0) = _
  simp only [fillExcept_self]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [hba]
  · simp

variable [Nonempty V]

/-- If the unnormalized singleton fibers have common positive relative
weights, then the actual masked-state row is their normalized law. -/
theorem exactRow_eq_ofPositiveWeights (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (y : MaskedState N V) (j : Position N)
    (hj : y j = none) (w : V → ℝ) (hw : ∀ a, 0 < w a)
    (hcross : ∀ (t : {i : Position N // i ≠ j} → V) (a b : V),
      y.Agrees (fillExcept j a t) →
      p (fillExcept j a t) * w b = p (fillExcept j b t) * w a) :
    y.exactRow p hp ⟨j, (y.mem_masked_iff j).2 hj⟩ =
      FinDist.ofPositiveWeights w hw := by
  classical
  apply FinDist.eq_ofPositiveWeights_of_cross_mul
  intro a b
  simp only [exactRow, FinDist.conditionalMap_apply_ratio]
  rw [eventMass_agrees_eval, eventMass_agrees_eval]
  have hsum :
      (∑ t : {i : Position N // i ≠ j} → V,
        if y.Agrees (fillExcept j a t) then p (fillExcept j a t) else 0) * w b =
      (∑ t : {i : Position N // i ≠ j} → V,
        if y.Agrees (fillExcept j b t) then p (fillExcept j b t) else 0) * w a := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ha : y.Agrees (fillExcept j a t)
    · have hb := (y.agrees_fillExcept_iff j hj a b t).mp ha
      simp only [ha, hb, ite_true]
      exact hcross t a b ha
    · have hb : ¬ y.Agrees (fillExcept j b t) := by
        exact fun hb ↦ ha ((y.agrees_fillExcept_iff j hj a b t).mpr hb)
      simp [ha, hb]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, hsum]

end MaskedState

namespace ForestModel

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A local factor satisfies the singleton cross-product identity whenever
its two backgrounds agree at all neighbors of the updated vertex. -/
theorem vertexFactor_update_cross_mul (M : ForestModel N V)
    (j k : Position N) (x u : Configuration N V)
    (hneighbors : ∀ v, M.graph.Adj j v → x v = u v) (a b : V) :
    M.vertexFactor k (Function.update x j a) *
        M.vertexFactor k (Function.update u j b) =
      M.vertexFactor k (Function.update x j b) *
        M.vertexFactor k (Function.update u j a) := by
  classical
  by_cases hk : k ∈ M.rooting.roots
  · by_cases hkj : k = j
    · subst k
      simp [vertexFactor, hk, mul_comm]
    · simp [vertexFactor, hk, Function.update_of_ne hkj]
  · by_cases hkj : k = j
    · subst k
      have hpj := M.rooting.parent_ne_self hk
      have hp := hneighbors (M.rooting.parent j) (M.rooting.parent_adj j hk).symm
      simp [vertexFactor, hk, Function.update_of_ne hpj, hp, mul_comm]
    · by_cases hpj : M.rooting.parent k = j
      · have hchild := hneighbors k (by simpa [hpj] using M.rooting.parent_adj k hk)
        simp [vertexFactor, hk, hpj, Function.update_of_ne hkj, hchild, mul_comm]
      · simp [vertexFactor, hk, Function.update_of_ne hkj, Function.update_of_ne hpj]

/-- Cancellation of all nonincident factors gives a local cross-product
identity for the actual target density. -/
theorem target_update_cross_mul (M : ForestModel N V)
    (j : Position N) (x u : Configuration N V)
    (hneighbors : ∀ v, M.graph.Adj j v → x v = u v) (a b : V) :
    M.target (Function.update x j a) * M.target (Function.update u j b) =
      M.target (Function.update x j b) * M.target (Function.update u j a) := by
  simp only [M.target_eq_prod_vertexFactor, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun k _ ↦
    M.vertexFactor_update_cross_mul j k x u hneighbors a b)

variable [Nonempty V]

/-- Once every neighbor is fixed, the actual singleton row is the normalized
target density obtained by updating only that vertex in any compatible
background. Factors away from the vertex cancel in the normalization. -/
theorem exactRow_eq_of_neighbors_fixed (M : ForestModel N V)
    (y : MaskedState N V) (j : Position N) (hj : y j = none)
    (u : Configuration N V)
    (hneighbors : ∀ v, M.graph.Adj j v → ∃ a, y v = some a ∧ u v = a) :
    y.exactRow M.target M.target_positive ⟨j, (y.mem_masked_iff j).2 hj⟩ =
      FinDist.ofPositiveWeights (fun a ↦ M.target (Function.update u j a))
        (fun _ ↦ M.target_positive _) := by
  apply MaskedState.exactRow_eq_ofPositiveWeights M.target M.target_positive y j hj
  intro t a b hya
  have hlocal : ∀ v, M.graph.Adj j v → MaskedState.fillExcept j a t v = u v := by
    intro v hv
    obtain ⟨c, hyc, huc⟩ := hneighbors v hv
    exact (hya v c hyc).trans huc.symm
  simpa only [MaskedState.update_fillExcept] using
    M.target_update_cross_mul j (MaskedState.fillExcept j a t) u hlocal a b

/-- Two submitted states give exactly the same conditional row whenever the
readout is masked in both states and every graph neighbor is observed with
identical values. Other observations and masks may differ arbitrarily. -/
theorem exactRow_eq_of_neighbors_observed (M : ForestModel N V)
    (y z : MaskedState N V) (j : Position N)
    (hyj : y j = none) (hzj : z j = none)
    (hneighbors : ∀ v, M.graph.Adj j v →
      ∃ a, y v = some a ∧ z v = some a) :
    y.exactRow M.target M.target_positive ⟨j, (y.mem_masked_iff j).2 hyj⟩ =
      z.exactRow M.target M.target_positive ⟨j, (z.mem_masked_iff j).2 hzj⟩ := by
  let fallback : V := Classical.choice (inferInstance : Nonempty V)
  let u : Configuration N V := y.completion fallback
  have hy : ∀ v, M.graph.Adj j v → ∃ a, y v = some a ∧ u v = a := by
    intro v hv
    obtain ⟨a, hya, _⟩ := hneighbors v hv
    exact ⟨a, hya, y.completion_agrees fallback v a hya⟩
  have hz : ∀ v, M.graph.Adj j v → ∃ a, z v = some a ∧ u v = a := by
    intro v hv
    obtain ⟨a, hya, hza⟩ := hneighbors v hv
    exact ⟨a, hza, y.completion_agrees fallback v a hya⟩
  rw [M.exactRow_eq_of_neighbors_fixed y j hyj u hy,
    M.exactRow_eq_of_neighbors_fixed z j hzj u hz]

end ForestModel

end ForestSampling
