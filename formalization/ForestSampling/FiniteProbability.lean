import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

/-!
# Finite probability distributions

This file fixes the normalizations used in the paper and supplies the finite
probability operations needed by the model and oracle layers.  In particular,
`sqHellinger` is the paper's squared Hellinger distance

`1 - ∑ x, sqrt (p x * q x)`,

without the alternative factor of two sometimes used in the literature.
-/

universe u v w

/-- A probability mass function on a finite type, represented over `ℝ`. -/
structure FinDist (α : Type u) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_mass : ∑ x, mass x = 1

namespace FinDist

noncomputable section

variable {α : Type u} {β : Type v} {γ : Type w}
variable [Fintype α] [Fintype β] [Fintype γ]

instance : CoeFun (FinDist α) (fun _ ↦ α → ℝ) := ⟨FinDist.mass⟩

@[ext]
theorem ext {p q : FinDist α} (h : ∀ x, p x = q x) : p = q := by
  cases p
  cases q
  congr
  funext x
  exact h x

@[simp]
theorem mass_mk (f : α → ℝ) (hnonneg hsum) (x : α) :
    (FinDist.mk f hnonneg hsum : FinDist α) x = f x := rfl

/-- Strict positivity, corresponding to membership in `Δᵒ` in the paper. -/
def StrictlyPositive (p : FinDist α) : Prop := ∀ x, 0 < p x

theorem mass_le_one (p : FinDist α) (x : α) : p x ≤ 1 := by
  calc
    p x ≤ ∑ y, p y := by
      exact Finset.single_le_sum (fun y _ ↦ p.nonneg y) (Finset.mem_univ x)
    _ = 1 := p.sum_mass

/-- The mass assigned to a decidable event. -/
def eventMass (p : FinDist α) (E : α → Prop) [DecidablePred E] : ℝ :=
  ∑ x, if E x then p x else 0

theorem eventMass_nonneg (p : FinDist α) (E : α → Prop) [DecidablePred E] :
    0 ≤ p.eventMass E := by
  apply Finset.sum_nonneg
  intro x _
  split <;> simp_all [p.nonneg]

theorem eventMass_le_one (p : FinDist α) (E : α → Prop) [DecidablePred E] :
    p.eventMass E ≤ 1 := by
  calc
    p.eventMass E ≤ ∑ x, p x := by
      apply Finset.sum_le_sum
      intro x _
      split <;> simp_all [p.nonneg]
    _ = 1 := p.sum_mass

/-- Event mass depends only on the event, not on its chosen predicate
representation or decidability witness. -/
theorem eventMass_congr (p : FinDist α) (E F : α → Prop)
    [DecidablePred E] [DecidablePred F] (h : ∀ x, E x ↔ F x) :
    p.eventMass E = p.eventMass F := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x
  · simp [hx, (h x).mp hx]
  · have hFx : ¬F x := fun hF ↦ hx ((h x).mpr hF)
    simp [hx, hFx]

@[simp]
theorem eventMass_true (p : FinDist α) :
    p.eventMass (fun _ ↦ True) = 1 := by
  unfold eventMass
  simpa using p.sum_mass

theorem eventMass_pos_of_exists (p : FinDist α) (hp : p.StrictlyPositive)
    (E : α → Prop) [DecidablePred E] (hE : ∃ x, E x) :
    0 < p.eventMass E := by
  obtain ⟨x, hx⟩ := hE
  have hterm : 0 < (if E x then p x else 0) := by simp [hx, hp x]
  refine lt_of_lt_of_le hterm ?_
  have hnonneg : ∀ y ∈ (Finset.univ : Finset α),
      0 ≤ (if E y then p y else 0) := by
    intro y _
    by_cases hy : E y <;> simp [hy, p.nonneg y]
  simpa only [eventMass] using
    (Finset.single_le_sum hnonneg (Finset.mem_univ x))

/-- Push a finite distribution forward through a function. -/
def map (p : FinDist α) (f : α → β) [DecidableEq β] : FinDist β := by
  refine
    { mass := fun y ↦ ∑ x, if f x = y then p x else 0
      nonneg := ?_
      sum_mass := ?_ }
  · intro y
    apply Finset.sum_nonneg
    intro x _
    by_cases hxy : f x = y <;> simp [hxy, p.nonneg x]
  · calc
      (∑ y, ∑ x, if f x = y then p x else 0)
          = ∑ x, ∑ y, if f x = y then p x else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ x, p x := by simp
      _ = 1 := p.sum_mass

@[simp]
theorem map_apply (p : FinDist α) (f : α → β) (y : β) [DecidableEq β] :
    p.map f y = ∑ x, if f x = y then p x else 0 := rfl

@[simp]
theorem map_id (p : FinDist α) [DecidableEq α] : p.map id = p := by
  ext x
  change (∑ y, if id y = x then p y else 0) = p x
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

@[simp]
theorem map_comp (p : FinDist α) (f : α → β) (g : β → γ)
    [DecidableEq β] [DecidableEq γ] :
    (p.map f).map g = p.map (g ∘ f) := by
  classical
  ext z
  simp only [map_apply, Function.comp_apply]
  calc
    (∑ y, if g y = z then ∑ x, if f x = y then p x else 0 else 0)
        = ∑ y, ∑ x,
            if g y = z then (if f x = y then p x else 0) else 0 := by
              apply Finset.sum_congr rfl
              intro y _
              split <;> simp
    _ = ∑ x, ∑ y,
            if g y = z then (if f x = y then p x else 0) else 0 := by
              rw [Finset.sum_comm]
    _ = ∑ x, if g (f x) = z then p x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      calc
        (∑ y, if g y = z then (if f x = y then p x else 0) else 0)
            = ∑ y, if f x = y then (if g y = z then p x else 0) else 0 := by
                apply Finset.sum_congr rfl
                intro y _
                by_cases hfy : f x = y <;> by_cases hgy : g y = z <;>
                  simp [hfy, hgy]
        _ = if g (f x) = z then p x else 0 :=
          Fintype.sum_ite_eq (f x) (fun y ↦ if g y = z then p x else 0)

theorem map_strictlyPositive_of_surjective (p : FinDist α)
    (hp : p.StrictlyPositive) (f : α → β) [DecidableEq β]
    (hf : Function.Surjective f) : (p.map f).StrictlyPositive := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  have hterm : 0 < (if f x = f x then p x else 0) := by simp [hp x]
  refine lt_of_lt_of_le hterm ?_
  have hnonneg : ∀ z ∈ (Finset.univ : Finset α),
      0 ≤ (if f z = f x then p z else 0) := by
    intro z _
    by_cases hz : f z = f x <;> simp [hz, p.nonneg z]
  simpa only [map_apply] using
    (Finset.single_le_sum hnonneg (Finset.mem_univ x))

theorem map_equiv_apply (p : FinDist α) (e : α ≃ β)
    [DecidableEq β] (y : β) :
    p.map e y = p (e.symm y) := by
  rw [map_apply]
  rw [Finset.sum_eq_single (e.symm y)]
  · simp
  · intro x _ hx
    have hne : e x ≠ y := by
      intro heq
      apply hx
      exact e.injective (by simpa using heq)
    simp [hne]
  · simp

/-- Event masses are invariant under transport by an equivalence. -/
theorem map_equiv_eventMass (p : FinDist α) (e : α ≃ β)
    [DecidableEq β] (E : β → Prop) [DecidablePred E] :
    (p.map e).eventMass E = p.eventMass (E ∘ e) := by
  unfold eventMass
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_equiv_apply]
  simp

/-- Point mass at `a`. -/
def dirac (a : α) [DecidableEq α] : FinDist α where
  mass x := if x = a then 1 else 0
  nonneg x := by split <;> norm_num
  sum_mass := by
    rw [Fintype.sum_ite_eq']

@[simp]
theorem dirac_apply (a x : α) [DecidableEq α] :
    dirac a x = if x = a then 1 else 0 := rfl

/-- Finite probability monad bind (mixture of the laws `k x`). -/
def bind (p : FinDist α) (k : α → FinDist β) : FinDist β where
  mass y := ∑ x, p x * k x y
  nonneg y := Finset.sum_nonneg fun x _ ↦
    mul_nonneg (p.nonneg x) ((k x).nonneg y)
  sum_mass := by
    calc
      (∑ y, ∑ x, p x * k x y) = ∑ x, ∑ y, p x * k x y := by
        rw [Finset.sum_comm]
      _ = ∑ x, p x * ∑ y, k x y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
      _ = ∑ x, p x := by simp only [FinDist.sum_mass, mul_one]
      _ = 1 := p.sum_mass

@[simp]
theorem bind_apply (p : FinDist α) (k : α → FinDist β) (y : β) :
    p.bind k y = ∑ x, p x * k x y := rfl

@[simp]
theorem dirac_bind (a : α) [DecidableEq α] (k : α → FinDist β) :
    (dirac a).bind k = k a := by
  ext y
  rw [bind_apply]
  change (∑ x, (if x = a then 1 else 0) * k x y) = k a y
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_ite_eq']

/-- Conditioning on an event of positive mass. -/
def conditionOn (p : FinDist α) (E : α → Prop) [DecidablePred E]
    (hE : 0 < p.eventMass E) : FinDist α where
  mass x := if E x then p x / p.eventMass E else 0
  nonneg x := by
    split
    · exact div_nonneg (p.nonneg x) hE.le
    · exact le_rfl
  sum_mass := by
    classical
    calc
      (∑ x, if E x then p x / p.eventMass E else 0)
          = ∑ x, (if E x then p x else 0) / p.eventMass E := by
              apply Finset.sum_congr rfl
              intro x _
              split <;> simp
      _ = p.eventMass E / p.eventMass E := by
              rw [← Finset.sum_div]
              rfl
      _ = 1 := div_self (ne_of_gt hE)

@[simp]
theorem conditionOn_apply_of_mem (p : FinDist α) (E : α → Prop)
    [DecidablePred E] (hE : 0 < p.eventMass E) {x : α} (hx : E x) :
    p.conditionOn E hE x = p x / p.eventMass E := by simp [conditionOn, hx]

@[simp]
theorem conditionOn_apply_of_not_mem (p : FinDist α) (E : α → Prop)
    [DecidablePred E] (hE : 0 < p.eventMass E) {x : α} (hx : ¬ E x) :
    p.conditionOn E hE x = 0 := by simp [conditionOn, hx]

theorem conditionOn_pos_on_event (p : FinDist α) (hp : p.StrictlyPositive)
    (E : α → Prop) [DecidablePred E] (hE : 0 < p.eventMass E)
    {x : α} (hx : E x) :
    0 < p.conditionOn E hE x := by
  simp only [conditionOn_apply_of_mem p E hE hx]
  exact div_pos (hp x) hE

/-- The conditional law of a readout, obtained by conditioning and then mapping. -/
def conditionalMap (p : FinDist α) (E : α → Prop) [DecidablePred E]
    (hE : 0 < p.eventMass E) (readout : α → β) [DecidableEq β] : FinDist β :=
  (p.conditionOn E hE).map readout

theorem conditionalMap_strictlyPositive (p : FinDist α)
    (hp : p.StrictlyPositive) (E : α → Prop) [DecidablePred E]
    (hE : 0 < p.eventMass E) (readout : α → β) [DecidableEq β]
    (hreach : ∀ y, ∃ x, E x ∧ readout x = y) :
    (p.conditionalMap E hE readout).StrictlyPositive := by
  intro y
  obtain ⟨x, hxE, hxy⟩ := hreach y
  have hxpos : 0 < (if readout x = y then p.conditionOn E hE x else 0) := by
    simp [hxy, p.conditionOn_pos_on_event hp E hE hxE]
  refine lt_of_lt_of_le hxpos ?_
  have hnonneg : ∀ z ∈ (Finset.univ : Finset α),
      0 ≤ (if readout z = y then p.conditionOn E hE z else 0) := by
    intro z _
    by_cases hz : readout z = y <;>
      simp [hz, (p.conditionOn E hE).nonneg z]
  simpa only [conditionalMap, map_apply] using
    (Finset.single_le_sum hnonneg (Finset.mem_univ x))

/-- Conditional readouts commute with transport by an equivalence. -/
theorem map_equiv_conditionalMap (p : FinDist α) (e : α ≃ β)
    [DecidableEq β] (E : β → Prop) [DecidablePred E]
    (hE : 0 < p.eventMass (E ∘ e)) (g : β → γ) [DecidableEq γ] :
    (p.map e).conditionalMap E
        (by rw [p.map_equiv_eventMass e E]; exact hE) g =
      p.conditionalMap (E ∘ e) hE (g ∘ e) := by
  ext c
  unfold conditionalMap
  rw [map_apply, map_apply, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : g (e x) = c
  · simp only [hg, Function.comp_apply, ite_true]
    by_cases hx : E (e x)
    · rw [conditionOn_apply_of_mem _ E _ hx,
          conditionOn_apply_of_mem _ (E ∘ e) _ (by simpa)]
      rw [map_equiv_apply, p.map_equiv_eventMass e E]
      simp
    · rw [conditionOn_apply_of_not_mem _ E _ hx,
          conditionOn_apply_of_not_mem _ (E ∘ e) _ (by simpa)]
  · simp [hg, Function.comp_apply]

/-- Conditional readout laws are unchanged by pointwise-equivalent events
and pointwise-equal readout functions. -/
theorem conditionalMap_congr (p : FinDist α) (E F : α → Prop)
    [DecidablePred E] [DecidablePred F]
    (hE : 0 < p.eventMass E) (hF : 0 < p.eventMass F)
    (g k : α → β) [DecidableEq β]
    (hevent : ∀ x, E x ↔ F x) (hreadout : ∀ x, g x = k x) :
    p.conditionalMap E hE g = p.conditionalMap F hF k := by
  have hmass : p.eventMass E = p.eventMass F :=
    p.eventMass_congr E F hevent
  ext b
  unfold conditionalMap
  rw [map_apply, map_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [hreadout x]
  by_cases hx : E x
  · have hFx : F x := (hevent x).mp hx
    simp [conditionOn, hx, hFx, hmass]
  · have hFx : ¬F x := fun hF ↦ hx ((hevent x).mpr hF)
    simp [conditionOn, hx, hFx]

/-- Replacing a distribution by an equal one does not change a conditional
readout law.  The two positivity proofs may be syntactically different. -/
theorem conditionalMap_congr_dist {p q : FinDist α} (hpq : p = q)
    (E : α → Prop) [DecidablePred E]
    (hp : 0 < p.eventMass E) (hq : 0 < q.eventMass E)
    (g : α → β) [DecidableEq β] :
    p.conditionalMap E hp g = q.conditionalMap E hq g := by
  subst q
  rfl

/-- Conditioning on the sure event leaves every readout law unchanged. -/
theorem conditionalMap_true (p : FinDist α) (g : α → β)
    [DecidableEq β] :
    p.conditionalMap (fun _ ↦ True)
        (by rw [p.eventMass_true]; norm_num) g =
      p.map g := by
  ext b
  unfold conditionalMap
  rw [map_apply, map_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp [conditionOn, p.eventMass_true]

/-- Binary product distribution. -/
def prod (p : FinDist α) (q : FinDist β) : FinDist (α × β) where
  mass x := p x.1 * q x.2
  nonneg x := mul_nonneg (p.nonneg x.1) (q.nonneg x.2)
  sum_mass := by
    rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, p.sum_mass, q.sum_mass, one_mul]

@[simp]
theorem prod_apply (p : FinDist α) (q : FinDist β) (x : α × β) :
    p.prod q x = p x.1 * q x.2 := rfl

theorem prod_strictlyPositive {p : FinDist α} {q : FinDist β}
    (hp : p.StrictlyPositive) (hq : q.StrictlyPositive) :
    (p.prod q).StrictlyPositive := by
  intro x
  exact mul_pos (hp x.1) (hq x.2)

/-- The mass of a rectangular event under a binary product factors. -/
theorem prod_eventMass_and (p : FinDist α) (q : FinDist β)
    (E : α → Prop) (F : β → Prop) [DecidablePred E] [DecidablePred F] :
    (p.prod q).eventMass (fun x ↦ E x.1 ∧ F x.2) =
      p.eventMass E * q.eventMass F := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  change (∑ a, ∑ b, if E a ∧ F b then p a * q b else 0) =
    (∑ a, if E a then p a else 0) * ∑ b, if F b then q b else 0
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : E a <;> by_cases hb : F b <;> simp [ha, hb]

theorem prod_eventMass_and_pos (p : FinDist α) (q : FinDist β)
    (E : α → Prop) (F : β → Prop) [DecidablePred E] [DecidablePred F]
    (hE : 0 < p.eventMass E) (hF : 0 < q.eventMass F) :
    0 < (p.prod q).eventMass (fun x ↦ E x.1 ∧ F x.2) := by
  rw [p.prod_eventMass_and q E F]
  exact mul_pos hE hF

/-- Conditioning a binary product on a rectangular event and reading only
the left factor cancels the conditioned right factor. -/
theorem prod_conditionalMap_left (p : FinDist α) (q : FinDist β)
    (E : α → Prop) (F : β → Prop) [DecidablePred E] [DecidablePred F]
    (hE : 0 < p.eventMass E) (hF : 0 < q.eventMass F)
    (g : α → γ) [DecidableEq γ] :
    (p.prod q).conditionalMap (fun x ↦ E x.1 ∧ F x.2)
        (p.prod_eventMass_and_pos q E F hE hF) (fun x ↦ g x.1) =
      p.conditionalMap E hE g := by
  ext c
  unfold conditionalMap
  rw [map_apply, map_apply, Fintype.sum_prod_type]
  change
    (∑ a, ∑ b,
      if g a = c then
        (if E a ∧ F b then
          p a * q b /
            (p.prod q).eventMass (fun x ↦ E x.1 ∧ F x.2)
        else 0)
      else 0) =
    ∑ a, if g a = c then
      (if E a then p a / p.eventMass E else 0) else 0
  rw [p.prod_eventMass_and q E F]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hga : g a = c
  · by_cases ha : E a
    · simp only [hga, ite_true, ha, true_and]
      calc
        (∑ b, if F b then
            p a * q b / (p.eventMass E * q.eventMass F) else 0) =
            (p a / (p.eventMass E * q.eventMass F)) *
              ∑ b, if F b then q b else 0 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro b _
                by_cases hb : F b
                · simp only [hb, ite_true]
                  ring
                · simp [hb]
        _ = (p a / (p.eventMass E * q.eventMass F)) *
              q.eventMass F := rfl
        _ = p a / p.eventMass E := by
              have hEnz : p.eventMass E ≠ 0 := ne_of_gt hE
              have hFnz : q.eventMass F ≠ 0 := ne_of_gt hF
              field_simp
    · simp [hga, ha]
  · simp [hga]

/-- Product of a finite family of finite distributions. -/
def piProduct {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (p : ∀ i, FinDist (Ω i)) :
    FinDist (∀ i, Ω i) where
  mass x := ∏ i, p i (x i)
  nonneg x := Finset.prod_nonneg fun i _ ↦ (p i).nonneg (x i)
  sum_mass := by
    classical
    rw [← Fintype.prod_sum]
    simp only [FinDist.sum_mass, Finset.prod_const_one]

@[simp]
theorem piProduct_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (p : ∀ i, FinDist (Ω i)) (x : ∀ i, Ω i) :
    piProduct p x = ∏ i, p i (x i) := rfl

theorem piProduct_strictlyPositive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    {p : ∀ i, FinDist (Ω i)} (hp : ∀ i, (p i).StrictlyPositive) :
    (piProduct p).StrictlyPositive := by
  intro x
  exact Finset.prod_pos fun i _ ↦ hp i (x i)

/-- Every coordinate marginal of a finite product law is its corresponding
factor. -/
theorem piProduct_map_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (p : ∀ i, FinDist (Ω i)) (i : ι) :
    (piProduct p).map (fun x ↦ x i) = p i := by
  ext a
  rw [map_apply]
  change (∑ x : ∀ j, Ω j,
      if x i = a then ∏ j, p j (x j) else 0) = p i a
  rw [← (Equiv.piSplitAt i Ω).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Ω i, ∑ z : ∀ j : {j // j ≠ i}, Ω j,
        if ((Equiv.piSplitAt i Ω).symm (x, z)) i = a then
          ∏ j, p j (((Equiv.piSplitAt i Ω).symm (x, z)) j)
        else 0) =
        ∑ x : Ω i, ∑ z : ∀ j : {j // j ≠ i}, Ω j,
          if x = a then p i x * ∏ j : {j // j ≠ i}, p j (z j) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro z _
            rw [Fintype.prod_eq_mul_prod_subtype_ne
              (fun j ↦ p j (((Equiv.piSplitAt i Ω).symm (x, z)) j)) i]
            have hrest :
                (∏ j : {j // j ≠ i},
                    p j (((Equiv.piSplitAt i Ω).symm (x, z)) j)) =
                  ∏ j : {j // j ≠ i}, p j (z j) := by
              apply Finset.prod_congr rfl
              intro j _
              simp [Equiv.piSplitAt, j.2]
            rw [hrest]
            simp [Equiv.piSplitAt]
    _ = ∑ x : Ω i, if x = a then p i x else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hxa : x = a
          · simp only [hxa, ite_true]
            rw [← Finset.mul_sum, ← Fintype.prod_sum]
            simp only [FinDist.sum_mass, Finset.prod_const_one, mul_one]
          · simp [hxa]
    _ = p i a := by rw [Fintype.sum_ite_eq']

/-- Splitting one coordinate transports a finite product law to the binary
product of that coordinate and all remaining coordinates. -/
theorem piProduct_map_piSplitAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (p : ∀ i, FinDist (Ω i)) (i : ι) :
    (piProduct p).map (Equiv.piSplitAt i Ω) =
      (p i).prod (piProduct fun j : {j // j ≠ i} ↦ p j.1) := by
  ext z
  rw [map_equiv_apply]
  change
    (∏ j, p j (((Equiv.piSplitAt i Ω).symm z) j)) =
      p i z.1 * ∏ j : {j // j ≠ i}, p j.1 (z.2 j)
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun j ↦ p j (((Equiv.piSplitAt i Ω).symm z) j)) i]
  congr 1
  · simp [Equiv.piSplitAt]
  · apply Finset.prod_congr rfl
    intro j _
    simp [Equiv.piSplitAt, j.2]

/-- A coordinatewise event under a finite product has product probability. -/
theorem piProduct_eventMass_forall {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, FinDist (Ω i)) (E : ∀ i, Ω i → Prop)
    [∀ i, DecidablePred (E i)] :
    (piProduct p).eventMass (fun x ↦ ∀ i, E i (x i)) =
      ∏ i, (p i).eventMass (E i) := by
  classical
  unfold eventMass
  change
    (∑ x : ∀ i, Ω i, if (∀ i, E i (x i)) then ∏ i, p i (x i) else 0) =
      ∏ i, ∑ a : Ω i, if E i a then p i a else 0
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ i, E i (x i)
  · simp [hx]
  · rw [if_neg hx]
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem piProduct_eventMass_forall_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, FinDist (Ω i)) (E : ∀ i, Ω i → Prop)
    [∀ i, DecidablePred (E i)]
    (hE : ∀ i, 0 < (p i).eventMass (E i)) :
    0 < (piProduct p).eventMass (fun x ↦ ∀ i, E i (x i)) := by
  rw [piProduct_eventMass_forall]
  exact Finset.prod_pos fun i _ ↦ hE i

/-- After conditioning a finite product on coordinatewise events, any
readout of one coordinate is obtained by conditioning that factor alone. -/
theorem piProduct_conditionalMap_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (p : ∀ i, FinDist (Ω i)) (E : ∀ i, Ω i → Prop)
    [∀ i, DecidablePred (E i)]
    (hE : ∀ i, 0 < (p i).eventMass (E i))
    (i : ι) (g : Ω i → γ) [DecidableEq γ] :
    (piProduct p).conditionalMap (fun x ↦ ∀ j, E j (x j))
        (piProduct_eventMass_forall_pos p E hE) (fun x ↦ g (x i)) =
      (p i).conditionalMap (E i) (hE i) g := by
  classical
  let restP : FinDist (∀ j : {j // j ≠ i}, Ω j.1) :=
    piProduct fun j : {j // j ≠ i} ↦ p j.1
  let restE : (∀ j : {j // j ≠ i}, Ω j.1) → Prop :=
    fun z ↦ ∀ j, E j.1 (z j)
  let split := Equiv.piSplitAt i Ω
  let pairE : (Ω i × (∀ j : {j // j ≠ i}, Ω j.1)) → Prop :=
    fun z ↦ E i z.1 ∧ restE z.2
  let pairReadout : (Ω i × (∀ j : {j // j ≠ i}, Ω j.1)) → γ :=
    fun z ↦ g z.1
  have hrest : 0 < restP.eventMass restE := by
    exact piProduct_eventMass_forall_pos
      (fun j : {j // j ≠ i} ↦ p j.1)
      (fun j : {j // j ≠ i} ↦ E j.1)
      (fun j ↦ hE j.1)
  have hall :
      0 < (piProduct p).eventMass (fun x ↦ ∀ j, E j (x j)) :=
    piProduct_eventMass_forall_pos p E hE
  have hevent : ∀ x,
      (pairE ∘ split) x ↔ (∀ j, E j (x j)) := by
    intro x
    constructor
    · rintro ⟨hi, hother⟩ j
      by_cases hji : j = i
      · subst j
        exact hi
      · exact hother ⟨j, hji⟩
    · intro hx
      exact ⟨hx i, fun j ↦ hx j.1⟩
  have htransport :
      0 < (piProduct p).eventMass (pairE ∘ split) := by
    rw [(piProduct p).eventMass_congr (pairE ∘ split)
      (fun x ↦ ∀ j, E j (x j)) hevent]
    exact hall
  calc
    (piProduct p).conditionalMap (fun x ↦ ∀ j, E j (x j)) hall
        (fun x ↦ g (x i)) =
        (piProduct p).conditionalMap (pairE ∘ split) htransport
          (pairReadout ∘ split) := by
            exact conditionalMap_congr (piProduct p)
              (fun x ↦ ∀ j, E j (x j)) (pairE ∘ split) hall htransport
              (fun x ↦ g (x i)) (pairReadout ∘ split)
              (fun x ↦ (hevent x).symm) (by
                intro x
                simp [pairReadout, split, Equiv.piSplitAt_apply])
    _ = ((piProduct p).map split).conditionalMap pairE
          (by rw [(piProduct p).map_equiv_eventMass split pairE]
              exact htransport)
          pairReadout := by
            exact (map_equiv_conditionalMap (piProduct p) split pairE
              htransport pairReadout).symm
    _ = ((p i).prod restP).conditionalMap pairE
          ((p i).prod_eventMass_and_pos restP (E i) restE (hE i) hrest)
          pairReadout := by
            exact conditionalMap_congr_dist
              (piProduct_map_piSplitAt p i) pairE _ _ pairReadout
    _ = (p i).conditionalMap (E i) (hE i) g := by
          exact prod_conditionalMap_left (p i) restP (E i) restE
            (hE i) hrest g

/-- Hellinger affinity. -/
def affinity (p q : FinDist α) : ℝ :=
  ∑ x, Real.sqrt (p x * q x)

/-- Squared Hellinger distance with the normalization used in the paper. -/
def sqHellinger (p q : FinDist α) : ℝ :=
  1 - affinity p q

/-- Total-variation distance with the normalization used in the paper. -/
def tv (p q : FinDist α) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |p x - q x|

/-- Pearson's chi-square divergence; its second argument is intended to be positive. -/
def chiSquare (p q : FinDist α) : ℝ :=
  ∑ x, (p x - q x) ^ 2 / q x

theorem chiSquare_nonneg (p q : FinDist α) (hq : q.StrictlyPositive) :
    0 ≤ chiSquare p q := by
  unfold chiSquare
  exact Finset.sum_nonneg fun x _ ↦ div_nonneg (sq_nonneg _) (hq x).le

theorem affinity_nonneg (p q : FinDist α) : 0 ≤ affinity p q := by
  exact Finset.sum_nonneg fun x _ ↦ Real.sqrt_nonneg _

theorem sqrt_mul_le_average {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [Real.sqrt_mul ha]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
    sq_nonneg (Real.sqrt a - Real.sqrt b)]

theorem affinity_le_one (p q : FinDist α) : affinity p q ≤ 1 := by
  calc
    affinity p q ≤ ∑ x, (p x + q x) / 2 := by
      apply Finset.sum_le_sum
      intro x _
      exact sqrt_mul_le_average (p.nonneg x) (q.nonneg x)
    _ = 1 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, p.sum_mass, q.sum_mass]
      norm_num

@[simp]
theorem affinity_self (p : FinDist α) : affinity p p = 1 := by
  unfold affinity
  calc
    (∑ x, Real.sqrt (p x * p x)) = ∑ x, p x := by
      apply Finset.sum_congr rfl
      intro x _
      exact Real.sqrt_mul_self (p.nonneg x)
    _ = 1 := p.sum_mass

theorem sqHellinger_nonneg (p q : FinDist α) : 0 ≤ sqHellinger p q := by
  unfold sqHellinger
  linarith [affinity_le_one p q]

theorem sqHellinger_le_one (p q : FinDist α) : sqHellinger p q ≤ 1 := by
  unfold sqHellinger
  linarith [affinity_nonneg p q]

@[simp]
theorem sqHellinger_self (p : FinDist α) : sqHellinger p p = 0 := by
  simp [sqHellinger]

theorem tv_nonneg (p q : FinDist α) : 0 ≤ tv p q := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ ↦ abs_nonneg _)

@[simp]
theorem tv_self (p : FinDist α) : tv p p = 0 := by
  simp [tv]

theorem abs_sub_eq_add_sub_two_mul_min {a b : ℝ} :
    |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

theorem tv_eq_one_sub_sum_min (p q : FinDist α) :
    tv p q = 1 - ∑ x, min (p x) (q x) := by
  unfold tv
  have hsum :
      (∑ x, |p x - q x|) = ∑ x, (p x + q x - 2 * min (p x) (q x)) := by
    apply Finset.sum_congr rfl
    intro x _
    exact abs_sub_eq_add_sub_two_mul_min
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [p.sum_mass, q.sum_mass]
  ring

theorem min_le_sqrt_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ≤ Real.sqrt (a * b) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    rw [Real.le_sqrt ha (mul_nonneg ha hb)]
    nlinarith
  · rw [min_eq_right hba]
    rw [Real.le_sqrt hb (mul_nonneg ha hb)]
    nlinarith

theorem sqHellinger_le_tv (p q : FinDist α) : sqHellinger p q ≤ tv p q := by
  rw [tv_eq_one_sub_sum_min]
  unfold sqHellinger affinity
  have hsum : (∑ x, min (p x) (q x)) ≤ ∑ x, Real.sqrt (p x * q x) := by
    apply Finset.sum_le_sum
    intro x _
    exact min_le_sqrt_mul (p.nonneg x) (q.nonneg x)
  linarith

theorem sum_sq_sqrt_sub (p q : FinDist α) :
    (∑ x, |Real.sqrt (p x) - Real.sqrt (q x)| ^ 2) =
      2 * sqHellinger p q := by
  unfold sqHellinger affinity
  calc
    (∑ x, |Real.sqrt (p x) - Real.sqrt (q x)| ^ 2)
        = ∑ x, (p x + q x - 2 * Real.sqrt (p x * q x)) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [sq_abs, sub_sq, Real.sq_sqrt (p.nonneg x),
              Real.sq_sqrt (q.nonneg x), Real.sqrt_mul (p.nonneg x)]
            ring
    _ = (∑ x, p x) + (∑ x, q x) -
          2 * ∑ x, Real.sqrt (p x * q x) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * (1 - ∑ x, Real.sqrt (p x * q x)) := by
            rw [p.sum_mass, q.sum_mass]
            ring

/-- Pointwise square-root loss is bounded by the Pearson chi-square
integrand when the reference mass is positive. -/
theorem sq_sqrt_sub_le_chi_term {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (a - b) ^ 2 / b := by
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hsa_sq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have hsb_sq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  have hbase : b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [mul_nonneg hsa hsb]
  have hmul := mul_le_mul_of_nonneg_left hbase
    (sq_nonneg (Real.sqrt a - Real.sqrt b))
  apply (le_div_iff₀ hb).2
  calc
    (Real.sqrt a - Real.sqrt b) ^ 2 * b ≤
        (Real.sqrt a - Real.sqrt b) ^ 2 *
          (Real.sqrt a + Real.sqrt b) ^ 2 := hmul
    _ = (a - b) ^ 2 := by
          rw [← mul_pow]
          nlinarith

/-- With this development's normalization
`H²(p,q) = 1 - ∑ sqrt (p q)`, squared Hellinger distance is at most
one half of Pearson's chi-square divergence. -/
theorem sqHellinger_le_half_chiSquare (p q : FinDist α)
    (hq : q.StrictlyPositive) :
    sqHellinger p q ≤ chiSquare p q / 2 := by
  have hterm :
      (∑ x, |Real.sqrt (p x) - Real.sqrt (q x)| ^ 2) ≤
        ∑ x, (p x - q x) ^ 2 / q x := by
    apply Finset.sum_le_sum
    intro x _
    rw [sq_abs]
    exact sq_sqrt_sub_le_chi_term (p.nonneg x) (hq x)
  rw [sum_sq_sqrt_sub] at hterm
  unfold chiSquare
  linarith

theorem sum_sq_sqrt_add (p q : FinDist α) :
    (∑ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2) =
      2 + 2 * affinity p q := by
  unfold affinity
  calc
    (∑ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2)
        = ∑ x, (p x + q x + 2 * Real.sqrt (p x * q x)) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [add_sq, Real.sq_sqrt (p.nonneg x),
              Real.sq_sqrt (q.nonneg x), Real.sqrt_mul (p.nonneg x)]
            ring
    _ = (∑ x, p x) + (∑ x, q x) +
          2 * ∑ x, Real.sqrt (p x * q x) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 + 2 * ∑ x, Real.sqrt (p x * q x) := by
            rw [p.sum_mass, q.sum_mass]
            ring

theorem abs_mass_sub_factorization (p q : FinDist α) (x : α) :
    |p x - q x| =
      |Real.sqrt (p x) - Real.sqrt (q x)| *
        (Real.sqrt (p x) + Real.sqrt (q x)) := by
  have hp := Real.sq_sqrt (p.nonneg x)
  have hq := Real.sq_sqrt (q.nonneg x)
  calc
    |p x - q x|
        = |(Real.sqrt (p x) - Real.sqrt (q x)) *
            (Real.sqrt (p x) + Real.sqrt (q x))| := by
              congr 1
              nlinarith
    _ = |Real.sqrt (p x) - Real.sqrt (q x)| *
          |Real.sqrt (p x) + Real.sqrt (q x)| := abs_mul _ _
    _ = _ := by
      rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]

theorem tv_le_sqrt_two_mul_sqHellinger (p q : FinDist α) :
    tv p q ≤ Real.sqrt (2 * sqHellinger p q) := by
  let f : α → ℝ := fun x ↦ |Real.sqrt (p x) - Real.sqrt (q x)|
  let g : α → ℝ := fun x ↦ Real.sqrt (p x) + Real.sqrt (q x)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset α) f g
  have hf : (∑ x, f x ^ 2) = 2 * sqHellinger p q := by
    simpa [f] using sum_sq_sqrt_sub p q
  have hg : (∑ x, g x ^ 2) = 2 + 2 * affinity p q := by
    simpa [g] using sum_sq_sqrt_add p q
  have hg_le : (∑ x, g x ^ 2) ≤ 4 := by
    rw [hg]
    linarith [affinity_le_one p q]
  have hsqrt_g : Real.sqrt (∑ x, g x ^ 2) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num at hg_le ⊢
      exact hg_le
  have hsqrt_f_nonneg : 0 ≤ Real.sqrt (∑ x, f x ^ 2) := Real.sqrt_nonneg _
  have hsum : (∑ x, |p x - q x|) ≤
      Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ x, g x ^ 2) := by
    calc
      (∑ x, |p x - q x|) = ∑ x, f x * g x := by
        apply Finset.sum_congr rfl
        intro x _
        exact abs_mass_sub_factorization p q x
      _ ≤ _ := hcs
  have hbound : (∑ x, |p x - q x|) ≤ 2 * Real.sqrt (∑ x, f x ^ 2) := by
    calc
      (∑ x, |p x - q x|)
          ≤ Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ x, g x ^ 2) := hsum
      _ ≤ Real.sqrt (∑ x, f x ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left hsqrt_g hsqrt_f_nonneg
      _ = 2 * Real.sqrt (∑ x, f x ^ 2) := by ring
  unfold tv
  rw [hf] at hbound
  nlinarith

theorem tv_le_one (p q : FinDist α) : tv p q ≤ 1 := by
  rw [tv_eq_one_sub_sum_min]
  have hmin : 0 ≤ ∑ x, min (p x) (q x) := by
    exact Finset.sum_nonneg fun x _ ↦ le_min (p.nonneg x) (q.nonneg x)
  linarith

theorem affinity_comm (p q : FinDist α) : affinity p q = affinity q p := by
  unfold affinity
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm]

theorem sqHellinger_comm (p q : FinDist α) : sqHellinger p q = sqHellinger q p := by
  simp only [sqHellinger, affinity_comm]

theorem tv_comm (p q : FinDist α) : tv p q = tv q p := by
  unfold tv
  apply congrArg ((1 / 2 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro x _
  rw [abs_sub_comm]

theorem affinity_piProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (p q : ∀ i, FinDist (Ω i)) :
    affinity (piProduct p) (piProduct q) = ∏ i, affinity (p i) (q i) := by
  classical
  unfold affinity
  simp only [piProduct_apply]
  conv_lhs =>
    enter [2, x]
    rw [← Finset.prod_mul_distrib]
    rw [Real.sqrt_prod Finset.univ
      (fun i _ ↦ mul_nonneg ((p i).nonneg (x i)) ((q i).nonneg (x i)))]
  exact (Fintype.prod_sum
    (fun i x ↦ Real.sqrt ((p i) x * (q i) x))).symm

theorem one_sub_prod_one_sub_le_sum {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu0 : ∀ i ∈ s, 0 ≤ u i) (hu1 : ∀ i ∈ s, u i ≤ 1) :
    1 - ∏ i ∈ s, (1 - u i) ≤ ∑ i ∈ s, u i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hua0 : 0 ≤ u a := hu0 a (Finset.mem_insert_self a s)
      have hua1 : u a ≤ 1 := hu1 a (Finset.mem_insert_self a s)
      have hs0 : ∀ i ∈ s, 0 ≤ u i := fun i hi ↦ hu0 i (Finset.mem_insert_of_mem hi)
      have hs1 : ∀ i ∈ s, u i ≤ 1 := fun i hi ↦ hu1 i (Finset.mem_insert_of_mem hi)
      have hprod0 : 0 ≤ ∏ i ∈ s, (1 - u i) :=
        Finset.prod_nonneg fun i hi ↦ sub_nonneg.mpr (hs1 i hi)
      have hprod1 : (∏ i ∈ s, (1 - u i)) ≤ 1 :=
        Finset.prod_le_one
          (fun i hi ↦ sub_nonneg.mpr (hs1 i hi))
          (fun i hi ↦ by linarith [hs0 i hi])
      have hmul : u a * (∏ i ∈ s, (1 - u i)) ≤ u a := by
        simpa using mul_le_mul_of_nonneg_left hprod1 hua0
      have hih := ih hs0 hs1
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      nlinarith

theorem sqHellinger_piProduct_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (p q : ∀ i, FinDist (Ω i)) :
    sqHellinger (piProduct p) (piProduct q) ≤
      ∑ i, sqHellinger (p i) (q i) := by
  rw [sqHellinger, affinity_piProduct]
  have haff : ∀ i, affinity (p i) (q i) = 1 - sqHellinger (p i) (q i) := by
    intro i
    unfold sqHellinger
    ring
  simp_rw [haff]
  exact one_sub_prod_one_sub_le_sum Finset.univ
    (fun i ↦ sqHellinger (p i) (q i))
    (fun i _ ↦ sqHellinger_nonneg (p i) (q i))
    (fun i _ ↦ sqHellinger_le_one (p i) (q i))

end

end FinDist

end ForestSampling
