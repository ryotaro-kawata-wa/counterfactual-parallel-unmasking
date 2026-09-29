import ForestSampling.MatchingCollision
import ForestSampling.MatchingLaplaceConstants

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

universe u v

namespace FinDist

variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]

/-- Expectation of a real-valued function under a finite probability law. -/
noncomputable def expectation (p : FinDist α) (f : α → ℝ) : ℝ := ∑ a, p a * f a

@[simp]
theorem expectation_const (p : FinDist α) (c : ℝ) : p.expectation (fun _ ↦ c) = c := by
  unfold expectation
  rw [← Finset.sum_mul, p.sum_mass, one_mul]

/-- Finite expectations preserve pointwise inequalities. -/
theorem expectation_mono (p : FinDist α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    p.expectation f ≤ p.expectation g := by
  exact Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (h a) (p.nonneg a)

/-- A nonnegative function has nonnegative finite expectation. -/
theorem expectation_nonneg (p : FinDist α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ p.expectation f :=
  Finset.sum_nonneg fun a _ ↦ mul_nonneg (p.nonneg a) (h a)

/-- Pushforward and expectation obey the finite change-of-variables identity. -/
theorem expectation_map (p : FinDist α) (f : α → β) [DecidableEq β] (g : β → ℝ) :
    (p.map f).expectation g = p.expectation (g ∘ f) := by
  unfold expectation
  simp only [map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- Multiplying a conditional expectation by its positive event probability
recovers the unnormalized expectation on that event. -/
theorem eventMass_mul_conditionOn_expectation (p : FinDist α) (E : α → Prop)
    [DecidablePred E] (hE : 0 < p.eventMass E) (f : α → ℝ) :
    p.eventMass E * (p.conditionOn E hE).expectation f =
      ∑ a, if E a then p a * f a else 0 := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a
  · rw [conditionOn_apply_of_mem _ _ _ ha, if_pos ha]
    field_simp
  · simp [ha]

/-- The finite law of total expectation for a readout all of whose fibers have
positive probability. -/
theorem expectation_eq_sum_conditionOn (p : FinDist α) (g : α → β) [DecidableEq β]
    (hpos : ∀ b, 0 < p.eventMass (fun a ↦ g a = b)) (f : α → ℝ) :
    p.expectation f = ∑ b, p.eventMass (fun a ↦ g a = b) *
      (p.conditionOn (fun a ↦ g a = b) (hpos b)).expectation f := by
  simp_rw [eventMass_mul_conditionOn_expectation]
  rw [Finset.sum_comm]
  unfold expectation
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- Equivalent conditioning events give identical finite conditional laws,
independently of their decidability and positivity proof witnesses. -/
theorem conditionOn_congr_for_exposure (p : FinDist α) (E F : α → Prop)
    [DecidablePred E] [DecidablePred F] (hE : 0 < p.eventMass E)
    (hF : 0 < p.eventMass F) (h : ∀ a, E a ↔ F a) :
    p.conditionOn E hE = p.conditionOn F hF := by
  have hmass := p.eventMass_congr E F h
  ext a
  by_cases ha : E a
  · simp [conditionOn, ha, (h a).mp ha, hmass]
  · have hf : ¬ F a := fun hf ↦ ha ((h a).mpr hf)
    simp [conditionOn, ha, hf]

end FinDist

namespace MatchingOn

variable {α : Type u} [DecidableEq α]

/-- The exposed vertex predicate for a single edge with endpoints `a,b`. -/
def PairVertices (a b : α) (x : α) : Prop := x = a ∨ x = b

instance pairVerticesDecidablePred (a b : α) : DecidablePred (PairVertices a b) :=
  fun x ↦ inferInstanceAs (Decidable (x = a ∨ x = b))

/-- The vertex type left after exposing and deleting one matching edge. -/
abbrev PairSurvivors (a b : α) := {x // ¬ PairVertices a b x}

/-- The unique matching on the two distinct exposed endpoint labels. -/
def pairMatching (a b : α) (hab : a ≠ b) : MatchingOn {x // PairVertices a b x} where
  mate x := if x.1 = a then ⟨b, Or.inr rfl⟩ else ⟨a, Or.inl rfl⟩
  mate_ne_self x h := by
    by_cases hx : x.1 = a
    · simp only [if_pos hx] at h
      exact hab ((congrArg Subtype.val h).trans hx).symm
    · simp only [if_neg hx] at h
      exact hx (congrArg Subtype.val h).symm
  mate_mate x := by
    apply Subtype.ext
    by_cases hx : x.1 = a
    · simp [hx, Ne.symm hab]
    · have hb : x.1 = b := x.2.resolve_left hx
      simp [hb, Ne.symm hab]

/-- Extending a specified exposed edge is equivalent to the corresponding
single mate equation; involutivity supplies the equation at its other endpoint. -/
theorem extends_pairMatching_iff (M : MatchingOn α) (a b : α) (hab : a ≠ b) :
    M.Extends (pairMatching a b hab) ↔ M.mate a = b := by
  constructor
  · intro h
    simpa [pairMatching] using h ⟨a, Or.inl rfl⟩
  · intro h x
    have hback : M.mate b = a := by simpa [h] using M.mate_mate a
    rcases x with ⟨x, hx | hx⟩
    · subst x
      simp [pairMatching, h]
    · subst x
      simp [pairMatching, Ne.symm hab, hback]

/-- Any two distinct vertices can be paired in a nonempty matching space:
relabel an existing matching by swapping the old mate with the desired mate. -/
theorem exists_mate_eq [Nonempty (MatchingOn α)] (a b : α) (hab : a ≠ b) :
    ∃ M : MatchingOn α, M.mate a = b := by
  obtain ⟨M⟩ := ‹Nonempty (MatchingOn α)›
  let e := Equiv.swap (M.mate a) b
  have hfix : e.symm a = a := by
    simp [e, Equiv.swap_apply_of_ne_of_ne (M.mate_ne_self a).symm hab]
  refine ⟨M.transport e, ?_⟩
  change e (M.mate (e.symm a)) = b
  rw [hfix]
  exact Equiv.swap_apply_left _ _

/-- Deleting any realizable exposed edge leaves an inhabited matching space. -/
theorem pairSurvivors_matching_nonempty [Nonempty (MatchingOn α)]
    (a b : α) (hab : a ≠ b) : Nonempty (MatchingOn (PairSurvivors a b)) := by
  obtain ⟨M, hM⟩ := exists_mate_eq a b hab
  have hext := (extends_pairMatching_iff M a b hab).2 hM
  exact ⟨M.restrict (fun x ↦ ¬ PairVertices a b x)
    (M.closed_compl _ hext.closed)⟩

variable [Fintype α]

/-- A distinct endpoint pair has exactly two labels. -/
theorem card_pairVertices (a b : α) (hab : a ≠ b) :
    Fintype.card {x // PairVertices a b x} = 2 := by
  rw [Fintype.card_subtype]
  have hset : Finset.univ.filter (PairVertices a b) = {a, b} := by
    ext x
    simp [PairVertices]
  rw [hset, Finset.card_pair hab]

/-- Exposing an edge removes exactly its two distinct endpoints. -/
theorem card_pairSurvivors (a b : α) (hab : a ≠ b) :
    Fintype.card (PairSurvivors a b) = Fintype.card α - 2 := by
  rw [Fintype.card_subtype_compl, card_pairVertices a b hab]

variable [Nonempty (MatchingOn α)]

/-- Every prospective non-self mate has positive probability. -/
theorem mate_eventMass_pos (a b : α) (hab : a ≠ b) :
    0 < (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate a = b) := by
  rw [uniform_mate_probability a b hab]
  have htwo : 2 ≤ Fintype.card α := by
    let : Nontrivial α := ⟨⟨a, b, hab⟩⟩
    exact Fintype.one_lt_card
  have hden : (0 : ℝ) < ((Fintype.card α - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < Fintype.card α - 1)
  exact div_pos zero_lt_one hden

/-- The uniform residual law after exposing the edge `{a,b}`. -/
noncomputable def pairSurvivorUniform (a b : α) (hab : a ≠ b) :
    FinDist (MatchingOn (PairSurvivors a b)) := by
  letI := pairSurvivors_matching_nonempty a b hab
  exact FinDist.uniform _

/-- Conditioning on one mate equation gives exactly the residual uniform
matching law glued to the exposed pair. -/
theorem uniform_conditionOn_mate (a b : α) (hab : a ≠ b) :
    (FinDist.uniform (MatchingOn α)).conditionOn (fun M ↦ M.mate a = b)
        (mate_eventMass_pos a b hab) =
      (pairSurvivorUniform a b hab).map
        (glue (PairVertices a b) (pairMatching a b hab)) := by
  let : Nonempty (MatchingOn (PairSurvivors a b)) := pairSurvivors_matching_nonempty a b hab
  change _ = (FinDist.uniform (MatchingOn (PairSurvivors a b))).map _
  calc
    _ = (FinDist.uniform (MatchingOn α)).conditionOn
        (fun M ↦ M.Extends (pairMatching a b hab))
        (extends_eventMass_pos (PairVertices a b) (pairMatching a b hab)) := by
      apply FinDist.conditionOn_congr_for_exposure
      intro M
      exact (extends_pairMatching_iff M a b hab).symm
    _ = _ := uniform_conditionOn_extends (PairVertices a b) (pairMatching a b hab)

end MatchingOn


namespace FinDist

variable {α : Type u} [Fintype α]

/-- Constants factor out of finite expectations. -/
theorem expectation_const_mul (p : FinDist α) (c : ℝ) (f : α → ℝ) :
    p.expectation (fun a ↦ c * f a) = c * p.expectation f := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

end FinDist

namespace MatchingOn

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Each internal matching edge contributes two endpoint indicators, so half
their sum is the internal-edge count, represented as a real number. -/
noncomputable def internalEdges (M : MatchingOn α) (S : Finset α) : ℝ :=
  (∑ a, if a ∈ S ∧ M.mate a ∈ S then (1 : ℝ) else 0) / 2

/-- Internal-edge counts are nonnegative. -/
theorem internalEdges_nonneg (M : MatchingOn α) (S : Finset α) :
    0 ≤ M.internalEdges S := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun a _ ↦ by split <;> norm_num
  · norm_num

/-- Gluing two disjoint matching components adds their internal-edge counts. -/
theorem internalEdges_glue (P : α → Prop) [DecidablePred P]
    (L : MatchingOn {a // P a}) (R : MatchingOn {a // ¬ P a}) (S : Finset α) :
    (glue P L R).internalEdges S =
      L.internalEdges (S.subtype P) + R.internalEdges (S.subtype fun a ↦ ¬ P a) := by
  unfold internalEdges
  rw [← Fintype.sum_subtype_add_sum_subtype P, add_div]
  congr 1
  · apply congrArg (fun z : ℝ ↦ z / 2)
    apply Finset.sum_congr rfl
    intro a _
    simp [glue, a.2]
  · apply congrArg (fun z : ℝ ↦ z / 2)
    apply Finset.sum_congr rfl
    intro a _
    simp [glue, a.2]

/-- If one exposed endpoint is in `S`, the exposed edge contributes one
exactly when its other endpoint is also in `S`. -/
theorem internalEdges_pair (a b : α) (hab : a ≠ b) (S : Finset α) (ha : a ∈ S) :
    (pairMatching a b hab).internalEdges (S.subtype (PairVertices a b)) =
      if b ∈ S then 1 else 0 := by
  have hf : ∀ x : {x // PairVertices a b x},
      (if x ∈ S.subtype (PairVertices a b) ∧
          (pairMatching a b hab).mate x ∈ S.subtype (PairVertices a b)
        then (1 : ℝ) else 0) = if b ∈ S then 1 else 0 := by
    rintro ⟨x, hx | hx⟩
    · subst x
      simp [pairMatching, ha]
    · subst x
      simp [pairMatching, Ne.symm hab, ha]
  unfold internalEdges
  simp_rw [hf]
  rw [Finset.sum_const, Finset.card_univ, card_pairVertices a b hab]
  by_cases hb : b ∈ S <;> simp [hb]

/-- Exact deterministic internal-edge recurrence after one edge exposure. -/
theorem internalEdges_glue_pair (a b : α) (hab : a ≠ b)
    (R : MatchingOn (PairSurvivors a b)) (S : Finset α) (ha : a ∈ S) :
    (glue (PairVertices a b) (pairMatching a b hab) R).internalEdges S =
      (if b ∈ S then 1 else 0) + R.internalEdges (S.subtype fun x ↦ ¬ PairVertices a b x) := by
  rw [internalEdges_glue, internalEdges_pair a b hab S ha]

omit [Fintype α] in
/-- Restricting a finite set to the survivors deletes the two exposed labels. -/
theorem card_subtype_pairSurvivors (a b : α) (S : Finset α) :
    (S.subtype fun x ↦ ¬ PairVertices a b x).card = ((S.erase a).erase b).card := by
  rw [Finset.card_subtype]
  congr 1
  ext x
  simp [PairVertices, and_assoc, and_left_comm, and_comm]

omit [Fintype α] in
/-- At most two selected starting vertices are lost in one exposure. -/
theorem card_subtype_pairSurvivors_lower (a b : α) (S : Finset α) :
    S.card - 2 ≤ (S.subtype fun x ↦ ¬ PairVertices a b x).card := by
  rw [card_subtype_pairSurvivors]
  have h₁ := Finset.pred_card_le_card_erase (s := S) (a := a)
  have h₂ := Finset.pred_card_le_card_erase (s := S.erase a) (a := b)
  omega

omit [Fintype α] in
/-- If the chosen starting point is outside a target set, at most one target
vertex is lost when exposing its matching edge. -/
theorem card_subtype_pairSurvivors_lower_of_notMem (a b : α) (S : Finset α)
    (ha : a ∉ S) : S.card - 1 ≤ (S.subtype fun x ↦ ¬ PairVertices a b x).card := by
  rw [card_subtype_pairSurvivors, Finset.erase_eq_of_notMem ha]
  exact Finset.pred_card_le_card_erase

variable [Nonempty (MatchingOn α)]

/-- The Laplace transform of the number of internal edges of a fixed set under
the uniform matching law. -/
noncomputable def internalLaplace (S : Finset α) (s : ℝ) : ℝ :=
  (FinDist.uniform (MatchingOn α)).expectation (fun M ↦ Real.exp (-s * M.internalEdges S))

/-- A nonnegative Laplace parameter gives a transform bounded by one. -/
theorem internalLaplace_le_one (S : Finset α) (s : ℝ) (hs : 0 ≤ s) :
    internalLaplace S s ≤ 1 := by
  calc
    _ ≤ (FinDist.uniform (MatchingOn α)).expectation (fun _ ↦ 1) := by
      apply FinDist.expectation_mono
      intro M
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs)
        (M.internalEdges_nonneg S))
    _ = 1 := FinDist.expectation_const _ 1

/-- The conditional transform after exposing a single edge factors into its
known contribution and the exact uniform residual transform. -/
theorem conditionOn_mate_internalLaplace (a b : α) (hab : a ≠ b)
    (S : Finset α) (ha : a ∈ S) (s : ℝ) :
    ((FinDist.uniform (MatchingOn α)).conditionOn (fun M ↦ M.mate a = b)
      (mate_eventMass_pos a b hab)).expectation (fun M ↦ Real.exp (-s * M.internalEdges S)) =
      Real.exp (-s * (if b ∈ S then 1 else 0)) *
        (pairSurvivorUniform a b hab).expectation
          (fun M ↦ Real.exp (-s * M.internalEdges (S.subtype fun x ↦ ¬ PairVertices a b x))) := by
  rw [uniform_conditionOn_mate, FinDist.expectation_map]
  change (pairSurvivorUniform a b hab).expectation
    (fun M ↦ Real.exp (-s * (glue (PairVertices a b) (pairMatching a b hab) M).internalEdges S)) = _
  simp_rw [internalEdges_glue_pair a b hab _ S ha, mul_add, Real.exp_add]
  exact FinDist.expectation_const_mul _ _ _

end MatchingOn


namespace FinDist

variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]

/-- Expectation of a readout function is the weighted sum over its fibers. -/
theorem expectation_readout (p : FinDist α) (g : α → β) [DecidableEq β] (f : β → ℝ) :
    p.expectation (fun a ↦ f (g a)) =
      ∑ b, p.eventMass (fun a ↦ g a = b) * f b := by
  calc
    _ = (p.map g).expectation f := (p.expectation_map g f).symm
    _ = _ := by simp only [expectation, map_apply, eventMass]

omit [Fintype β] in
/-- The probability of a finite target set is the sum of its disjoint readout
fiber probabilities. -/
theorem eventMass_mem (p : FinDist α) (g : α → β) [DecidableEq β] (B : Finset β) :
    p.eventMass (fun a ↦ g a ∈ B) = ∑ b ∈ B, p.eventMass (fun a ↦ g a = b) := by
  symm
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : g a ∈ B
  · rw [Finset.sum_eq_single (g a)]
    · simp [ha]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp [ha]
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b hb
    rw [if_neg]
    intro h
    apply ha
    simpa [h] using hb

/-- The expectation of an affine indicator is its corresponding affine event
probability. -/
theorem expectation_affine_indicator (p : FinDist α) (E : α → Prop)
    [DecidablePred E] (c : ℝ) :
    p.expectation (fun a ↦ 1 - c * (if E a then 1 else 0)) =
      1 - c * p.eventMass E := by
  unfold expectation eventMass
  calc
    (∑ a, p a * (1 - c * (if E a then 1 else 0))) =
        (∑ a, p a) - c * ∑ a, if E a then p a else 0 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : E a
      · simp only [ha, ite_true, mul_one]
        ring
      · simp [ha]
    _ = _ := by rw [p.sum_mass]

/-- The Bernoulli Laplace identity does not require independence from any
other variable; it is an identity for one finite event. -/
theorem expectation_exp_indicator (p : FinDist α) (E : α → Prop)
    [DecidablePred E] (s : ℝ) :
    p.expectation (fun a ↦ Real.exp (-s * (if E a then 1 else 0))) =
      1 - (1 - Real.exp (-s)) * p.eventMass E := by
  have hf : (fun a ↦ Real.exp (-s * (if E a then 1 else 0))) =
      (fun a ↦ 1 - (1 - Real.exp (-s)) * (if E a then 1 else 0)) := by
    funext a
    by_cases ha : E a <;> simp [ha]
  rw [hf]
  exact p.expectation_affine_indicator E _

end FinDist

namespace MatchingOn

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- A matching's mate readout cannot take the starting vertex as its value. -/
def mateReadout (a : α) (M : MatchingOn α) : {b // b ≠ a} :=
  ⟨M.mate a, M.mate_ne_self a⟩

/-- Summing an arbitrary mate-dependent factor against the mate fiber masses
recovers its expectation under the original matching law. -/
theorem sum_mate_factor (p : FinDist (MatchingOn α)) (a : α) (f : α → ℝ) :
    (∑ b : {b // b ≠ a}, p.eventMass (fun M ↦ M.mate a = b.1) * f b.1) =
      p.expectation (fun M ↦ f (M.mate a)) := by
  calc
    _ = ∑ b : {b // b ≠ a}, p.eventMass (fun M ↦ mateReadout a M = b) * f b.1 := by
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      apply FinDist.eventMass_congr
      intro M
      constructor
      · intro h; exact Subtype.ext h
      · intro h; exact congrArg Subtype.val h
    _ = p.expectation (fun M ↦ f (mateReadout a M).1) :=
      (p.expectation_readout (mateReadout a) (fun b ↦ f b.1)).symm
    _ = _ := rfl

variable [Nonempty (MatchingOn α)]

/-- A vertex's mate hits a set excluding that vertex with probability exactly
its cardinality divided by the number of possible mates. -/
theorem uniform_mate_mem (a : α) (B : Finset α) (ha : a ∉ B) :
    (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate a ∈ B) =
      (B.card : ℝ) / ((Fintype.card α - 1 : ℕ) : ℝ) := by
  rw [FinDist.eventMass_mem]
  calc
    (∑ b ∈ B, (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate a = b)) =
        ∑ _b ∈ B, 1 / ((Fintype.card α - 1 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply uniform_mate_probability
      intro h
      apply ha
      simpa [h] using hb
    _ = _ := by simp [div_eq_mul_inv]

/-- Exact one-edge recursion for the internal-edge Laplace transform, summing
over every prospective mate with its actual fiber probability. -/
theorem internalLaplace_eq_sum_mate (S : Finset α) (a : α) (ha : a ∈ S) (s : ℝ) :
    internalLaplace S s = ∑ b : {b // b ≠ a},
      (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate a = b.1) *
      (Real.exp (-s * (if b.1 ∈ S then 1 else 0)) *
        (pairSurvivorUniform a b.1 b.2.symm).expectation
          (fun M ↦ Real.exp (-s * M.internalEdges
            (S.subtype fun x ↦ ¬ PairVertices a b.1 x)))) := by
  let p := FinDist.uniform (MatchingOn α)
  have hevent (b : {b // b ≠ a}) :
      p.eventMass (fun M ↦ mateReadout a M = b) =
        p.eventMass (fun M ↦ M.mate a = b.1) := by
    apply FinDist.eventMass_congr
    intro M
    exact Subtype.ext_iff
  have hpos (b : {b // b ≠ a}) : 0 < p.eventMass (fun M ↦ mateReadout a M = b) := by
    rw [hevent]
    exact mate_eventMass_pos a b.1 b.2.symm
  rw [internalLaplace, FinDist.expectation_eq_sum_conditionOn _ (mateReadout a) hpos]
  apply Finset.sum_congr rfl
  intro b _
  rw [hevent]
  congr 1
  have hcond : p.conditionOn (fun M ↦ mateReadout a M = b) (hpos b) =
      p.conditionOn (fun M ↦ M.mate a = b.1) (mate_eventMass_pos a b.1 b.2.symm) := by
    apply FinDist.conditionOn_congr_for_exposure
    intro M
    exact Subtype.ext_iff
  rw [hcond]
  exact conditionOn_mate_internalLaplace a b.1 b.2.symm S ha s

end MatchingOn


namespace MatchingOn

/-- Exposing up to `m` edges from a starting set of size at least `2m` leaves
at least `r` prospective target mates.  Successive conditioning gives this
power bound without assuming that the exposure successes are independent. -/
theorem internalLaplace_le_exposure_power (m n r : ℕ) (hn : 0 < n)
    (s : ℝ) (hs : 0 ≤ s) :
    ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nonempty (MatchingOn α)]
      (S A B : Finset α), A ⊆ S → B ⊆ S → Disjoint A B →
      2 * m ≤ A.card → m + r ≤ B.card → Fintype.card α ≤ n →
      internalLaplace S s ≤ (1 - (1 - Real.exp (-s)) * (r : ℝ) / (n : ℝ)) ^ m := by
  induction m with
  | zero =>
      intro α _ _ _ S A B _ _ _ _ _ _
      simpa using internalLaplace_le_one S s hs
  | succ m ih =>
      intro α _ _ _ S A B hAS hBS hAB hA hB hcard
      let c : ℝ := 1 - (1 - Real.exp (-s)) * (r : ℝ) / (n : ℝ)
      obtain ⟨hd0, hd1⟩ := MatchingLaplaceConstants.deficit_bounds hs
      have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hrn : r ≤ n := by
        have hbcard := Finset.card_le_univ B
        omega
      have hrreal : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
      have hc : 0 ≤ c := by
        have har : (1 - Real.exp (-s)) * (r : ℝ) ≤ (n : ℝ) := by
          have hm := mul_le_mul_of_nonneg_right hd1 (Nat.cast_nonneg r)
          linarith
        exact sub_nonneg.mpr ((div_le_one hnreal).mpr har)
      have hAnonempty : A.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, haA⟩ := hAnonempty
      have haS := hAS haA
      have haB : a ∉ B := fun hb ↦ Finset.disjoint_left.mp hAB haA hb
      have htwo : 2 ≤ Fintype.card α := by
        have hacard := Finset.card_le_univ A
        omega
      have hden : (0 : ℝ) < ((Fintype.card α - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < Fintype.card α - 1)
      have hprob : (r : ℝ) / (n : ℝ) ≤
          (B.card : ℝ) / ((Fintype.card α - 1 : ℕ) : ℝ) := by
        apply (div_le_div_iff₀ hnreal hden).mpr
        have hdle : ((Fintype.card α - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (by omega : Fintype.card α - 1 ≤ n)
        have hrB : (r : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast (by omega : r ≤ B.card)
        exact (mul_le_mul_of_nonneg_left hdle (Nat.cast_nonneg r)).trans
          (mul_le_mul_of_nonneg_right hrB hnreal.le)
      have hbranch (b : {b // b ≠ a}) :
          Real.exp (-s * (if b.1 ∈ S then 1 else 0)) *
            (pairSurvivorUniform a b.1 b.2.symm).expectation
              (fun M ↦ Real.exp (-s * M.internalEdges
                (S.subtype fun x ↦ ¬ PairVertices a b.1 x))) ≤
          Real.exp (-s * (if b.1 ∈ B then 1 else 0)) * c ^ m := by
        let : Nonempty (MatchingOn (PairSurvivors a b.1)) :=
          pairSurvivors_matching_nonempty a b.1 b.2.symm
        let P := fun x ↦ ¬ PairVertices a b.1 x
        have hAS' : A.subtype P ⊆ S.subtype P := by
          intro x hx
          exact Finset.mem_subtype.mpr (hAS (Finset.mem_subtype.mp hx))
        have hBS' : B.subtype P ⊆ S.subtype P := by
          intro x hx
          exact Finset.mem_subtype.mpr (hBS (Finset.mem_subtype.mp hx))
        have hAB' : Disjoint (A.subtype P) (B.subtype P) := by
          rw [Finset.disjoint_left]
          intro x hx hy
          exact Finset.disjoint_left.mp hAB (Finset.mem_subtype.mp hx) (Finset.mem_subtype.mp hy)
        have hA' : 2 * m ≤ (A.subtype P).card := by
          have hh := card_subtype_pairSurvivors_lower a b.1 A
          change A.card - 2 ≤ (A.subtype P).card at hh
          omega
        have hB' : m + r ≤ (B.subtype P).card := by
          have hh := card_subtype_pairSurvivors_lower_of_notMem a b.1 B haB
          change B.card - 1 ≤ (B.subtype P).card at hh
          omega
        have hcard' : Fintype.card (PairSurvivors a b.1) ≤ n := by
          rw [card_pairSurvivors a b.1 b.2.symm]
          omega
        have hres := ih (S.subtype P) (A.subtype P) (B.subtype P) hAS' hBS' hAB' hA' hB' hcard'
        change (pairSurvivorUniform a b.1 b.2.symm).expectation
          (fun M ↦ Real.exp (-s * M.internalEdges (S.subtype P))) ≤ c ^ m at hres
        have hfactor : Real.exp (-s * (if b.1 ∈ S then 1 else 0)) ≤
            Real.exp (-s * (if b.1 ∈ B then 1 else 0)) := by
          by_cases hb : b.1 ∈ B
          · simp [hb, hBS hb]
          · simp only [if_neg hb, mul_zero, Real.exp_zero]
            apply Real.exp_le_one_iff.mpr
            exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (by split <;> norm_num)
        exact (mul_le_mul_of_nonneg_left hres (Real.exp_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hfactor (pow_nonneg hc m))
      rw [internalLaplace_eq_sum_mate S a haS s]
      change _ ≤ c ^ (m + 1)
      calc
        _ ≤ ∑ b : {b // b ≠ a},
            (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate a = b.1) *
              (Real.exp (-s * (if b.1 ∈ B then 1 else 0)) * c ^ m) := by
          apply Finset.sum_le_sum
          intro b _
          exact mul_le_mul_of_nonneg_left (hbranch b) (FinDist.eventMass_nonneg _ _)
        _ = (∑ b : {b // b ≠ a},
            (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate a = b.1) *
              Real.exp (-s * (if b.1 ∈ B then 1 else 0))) * c ^ m := by
          simp only [mul_assoc, Finset.sum_mul]
        _ = (1 - (1 - Real.exp (-s)) *
            ((B.card : ℝ) / ((Fintype.card α - 1 : ℕ) : ℝ))) * c ^ m := by
          rw [sum_mate_factor (FinDist.uniform (MatchingOn α)) a
            (fun b ↦ Real.exp (-s * (if b ∈ B then 1 else 0))),
            FinDist.expectation_exp_indicator, uniform_mate_mem a B haB]
        _ ≤ c * c ^ m := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hc m)
          have hh := mul_le_mul_of_nonneg_left hprob hd0
          dsimp [c]
          simpa only [mul_div_assoc] using sub_le_sub_left hh 1
        _ = c ^ (m + 1) := by rw [pow_succ]; ring

end MatchingOn


namespace MatchingOn

variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty (MatchingOn α)]

/-- One exposed endpoint already bounds the full transform by the Bernoulli
factor for hitting one of the other selected vertices. -/
theorem internalLaplace_le_single_edge (S : Finset α) (a : α) (ha : a ∈ S)
    (s : ℝ) (hs : 0 ≤ s) :
    internalLaplace S s ≤
      1 - (1 - Real.exp (-s)) * ((S.card - 1 : ℕ) : ℝ) /
        ((Fintype.card α - 1 : ℕ) : ℝ) := by
  have hprob : (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate a ∈ S) =
      ((S.card - 1 : ℕ) : ℝ) / ((Fintype.card α - 1 : ℕ) : ℝ) := by
    calc
      _ = (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate a ∈ S.erase a) := by
        apply FinDist.eventMass_congr
        intro M
        simp [Finset.mem_erase, M.mate_ne_self a]
      _ = _ := by
        rw [uniform_mate_mem a (S.erase a) (Finset.notMem_erase _ _),
          Finset.card_erase_of_mem ha]
  rw [internalLaplace_eq_sum_mate S a ha s]
  calc
    _ ≤ ∑ b : {b // b ≠ a},
        (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate a = b.1) *
          Real.exp (-s * (if b.1 ∈ S then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro b _
      apply mul_le_mul_of_nonneg_left _ (FinDist.eventMass_nonneg _ _)
      let : Nonempty (MatchingOn (PairSurvivors a b.1)) :=
        pairSurvivors_matching_nonempty a b.1 b.2.symm
      have hres : (pairSurvivorUniform a b.1 b.2.symm).expectation
          (fun M ↦ Real.exp (-s * M.internalEdges
            (S.subtype fun x ↦ ¬ PairVertices a b.1 x))) ≤ 1 :=
        internalLaplace_le_one _ s hs
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hres
        (Real.exp_nonneg (-s * (if b.1 ∈ S then 1 else 0)))
    _ = _ := by
      rw [sum_mate_factor (FinDist.uniform (MatchingOn α)) a
        (fun b ↦ Real.exp (-s * (if b ∈ S then 1 else 0))),
        FinDist.expectation_exp_indicator, hprob]
      ring

/-- The manuscript's uniform-matching internal-edge Laplace estimate, with
its finite constant `1/32`.  The bound includes the zero Laplace parameter. -/
theorem internalLaplace_le_exp (S : Finset α) (s : ℝ) (hs : 0 ≤ s)
    (hn : 2 ≤ Fintype.card α) :
    internalLaplace S s ≤
      Real.exp (-((1 - Real.exp (-s)) * ((S.card - 1 : ℕ) : ℝ) ^ 2 /
        (32 * (Fintype.card α : ℝ)))) := by
  by_cases hkSmall : S.card ≤ 1
  · have hz : S.card - 1 = 0 := by omega
    simpa [hz] using internalLaplace_le_one S s hs
  have hkTwo : 2 ≤ S.card := by omega
  by_cases hkThree : S.card ≤ 3
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    exact (internalLaplace_le_single_edge S a ha s hs).trans
      (MatchingLaplaceConstants.small_batch_factor_le_exp S.card (Fintype.card α)
        hkTwo hkThree (Finset.card_le_univ S) (1 - Real.exp (-s))
        (MatchingLaplaceConstants.deficit_bounds hs).1)
  have hkFour : 4 ≤ S.card := by omega
  obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq (Nat.div_le_self S.card 2)
  let B := S \ A
  have hBS : B ⊆ S := Finset.sdiff_subset
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  have hBcard : B.card = (S.card + 1) / 2 := by
    dsimp [B]
    rw [Finset.card_sdiff_of_subset hAS, hAcard]
    omega
  have hA : 2 * (S.card / 4) ≤ A.card := by omega
  have hB : S.card / 4 + ((S.card + 1) / 2 - S.card / 4) ≤ B.card := by omega
  have hpower := internalLaplace_le_exposure_power (S.card / 4) (Fintype.card α)
    ((S.card + 1) / 2 - S.card / 4) (by omega) s hs S A B hAS hBS hAB hA hB (le_refl _)
  exact hpower.trans (MatchingLaplaceConstants.quarter_exposure_power_le_exp
    S.card (Fintype.card α) hkFour (Finset.card_le_univ S) s hs)

end MatchingOn

namespace PerfectMatching

variable {N : ℕ}

/-- The internal matching-edge count on the original position-indexed type,
represented as half the number of selected endpoints whose mates are selected. -/
noncomputable def internalEdges (M : PerfectMatching N) (S : Finset (Position N)) : ℝ :=
  ((MatchingOn.finEquiv N).symm M).internalEdges S

/-- The constant-32 internal-edge Laplace bound for the existing hard-family
matching representation and its previously verified uniform prior. -/
theorem uniform_internalLaplace_le_exp (hN : Even N) (hn : 2 ≤ N)
    (S : Finset (Position N)) (s : ℝ) (hs : 0 ≤ s) :
    (uniform hN).expectation (fun M ↦ Real.exp (-s * M.internalEdges S)) ≤
      Real.exp (-((1 - Real.exp (-s)) * ((S.card - 1 : ℕ) : ℝ) ^ 2 /
        (32 * (N : ℝ)))) := by
  let : Nonempty (PerfectMatching N) := nonempty_of_even hN
  let : Nonempty (MatchingOn (Position N)) :=
    Nonempty.map (MatchingOn.finEquiv N).symm inferInstance
  have hmap : (FinDist.uniform (MatchingOn (Position N))).map (MatchingOn.finEquiv N) =
      uniform hN := FinDist.uniform_map_equiv _
  rw [← hmap, FinDist.expectation_map]
  change MatchingOn.internalLaplace S s ≤ _
  simpa only [Fintype.card_fin] using
    MatchingOn.internalLaplace_le_exp S s hs (by simpa using hn)

end PerfectMatching


namespace PerfectMatching

variable {N : ℕ}

/-- Number of matching edges whose two endpoints lie in `S`, counting each
edge once by its smaller endpoint. -/
def internalEdgeCount (M : PerfectMatching N) (S : Finset (Position N)) : ℕ :=
  (M.representatives.filter fun i ↦ i ∈ S ∧ M.mate i ∈ S).card

/-- The half-endpoint count used in the exposure induction is exactly the
natural number of internal matching edges. -/
theorem internalEdges_eq_card (M : PerfectMatching N) (S : Finset (Position N)) :
    M.internalEdges S = (M.internalEdgeCount S : ℝ) := by
  let F := S.filter fun i ↦ M.mate i ∈ S
  let R := F.filter fun i ↦ i < M.mate i
  let L := F.filter fun i ↦ ¬ i < M.mate i
  have hclosed : ∀ i ∈ F, M.mate i ∈ F := by
    intro i hi
    obtain ⟨hiS, hmS⟩ := Finset.mem_filter.mp hi
    change M.mate i ∈ S.filter (fun j ↦ M.mate j ∈ S)
    exact Finset.mem_filter.mpr ⟨hmS, by simpa [M.mate_mate i] using hiS⟩
  have hRL : R.card = L.card := by
    apply Finset.card_bij (fun i _ ↦ M.mate i)
    · intro i hi
      obtain ⟨hiF, hiLt⟩ := Finset.mem_filter.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨hclosed i hiF, ?_⟩
      intro hmLt
      rw [M.mate_mate i] at hmLt
      exact (lt_asymm hiLt hmLt).elim
    · intro i _ j _ h
      exact M.mate_mate.injective h
    · intro j hj
      obtain ⟨hjF, hjLt⟩ := Finset.mem_filter.mp hj
      refine ⟨M.mate j, ?_, M.mate_mate j⟩
      apply Finset.mem_filter.mpr
      refine ⟨hclosed j hjF, ?_⟩
      simpa [M.mate_mate j] using M.mate_lt_of_not_lt hjLt
  have hcard : F.card = 2 * R.card := by
    have hp := F.card_filter_add_card_filter_not (fun i ↦ i < M.mate i)
    change R.card + L.card = F.card at hp
    omega
  have hR : R = M.representatives.filter (fun i ↦ i ∈ S ∧ M.mate i ∈ S) := by
    ext i
    simp [R, F, representatives, and_left_comm, and_comm]
  have hsum : (∑ i : Position N, if i ∈ S ∧ M.mate i ∈ S then (1 : ℝ) else 0) =
      (F.card : ℝ) := by
    have hF : Finset.univ.filter (fun i ↦ i ∈ S ∧ M.mate i ∈ S) = F := by
      ext i
      simp [F]
    rw [← Finset.sum_filter, hF]
    simp
  change (∑ i : Position N, if i ∈ S ∧ M.mate i ∈ S then (1 : ℝ) else 0) / 2 =
    ((M.representatives.filter fun i ↦ i ∈ S ∧ M.mate i ∈ S).card : ℝ)
  rw [hsum, ← hR, hcard]
  push_cast
  ring

/-- The manuscript's matching-collision Laplace estimate with the literal
integer number of internal edges and the stated finite constant `1/32`. -/
theorem uniform_internalEdgeCount_laplace (hN : Even N) (hn : 2 ≤ N)
    (S : Finset (Position N)) (s : ℝ) (hs : 0 ≤ s) :
    (uniform hN).expectation (fun M ↦ Real.exp (-s * (M.internalEdgeCount S : ℝ))) ≤
      Real.exp (-((1 - Real.exp (-s)) * ((S.card - 1 : ℕ) : ℝ) ^ 2 /
        (32 * (N : ℝ)))) := by
  simpa only [internalEdges_eq_card] using uniform_internalLaplace_le_exp hN hn S s hs

end PerfectMatching

end ForestSampling
