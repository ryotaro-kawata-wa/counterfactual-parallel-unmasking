import ForestSampling.MatchingCombinatorics

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

universe u v

/-!
# Restricting and extending exposed matchings

This module supplies the finite matching-space machinery needed by the
uniform-matching exposure argument.  It does not yet assert the manuscript's
Laplace bound or identify a complete adaptive transcript with an exposure event.
-/

/-- A perfect matching on an arbitrary vertex type, represented by a
fixed-point-free involution.  This permits survivor sets to retain their
original labels instead of being repeatedly renumbered. -/
structure MatchingOn (α : Type u) where
  mate : α → α
  mate_ne_self : ∀ a, mate a ≠ a
  mate_mate : Function.Involutive mate

namespace MatchingOn

variable {α : Type u} {β : Type v}

/-- A matching is determined by its mate function. -/
@[ext]
theorem ext {M L : MatchingOn α} (h : ∀ a, M.mate a = L.mate a) : M = L := by
  cases M
  cases L
  congr
  exact funext h

theorem mate_injective : Function.Injective (mate : MatchingOn α → α → α) := by
  intro M L h
  exact ext fun a ↦ congrFun h a

instance [Fintype α] [DecidableEq α] : DecidableEq (MatchingOn α) := mate_injective.decidableEq

instance [Finite α] : Finite (MatchingOn α) := Finite.of_injective mate mate_injective

noncomputable instance [Fintype α] : Fintype (MatchingOn α) := Fintype.ofFinite _

/-- The arbitrary-label representation agrees exactly with the existing
position-indexed matching representation used by the hard target law. -/
def finEquiv (N : ℕ) : MatchingOn (Position N) ≃ PerfectMatching N where
  toFun M := ⟨M.mate, M.mate_ne_self, M.mate_mate⟩
  invFun M := ⟨M.mate, M.mate_ne_self, M.mate_mate⟩
  left_inv M := by cases M; rfl
  right_inv M := by cases M; rfl

/-- Transport a matching along a bijection of its vertex labels. -/
def transport (M : MatchingOn α) (e : α ≃ β) : MatchingOn β where
  mate b := e (M.mate (e.symm b))
  mate_ne_self b h := by
    apply M.mate_ne_self (e.symm b)
    exact e.injective (by simpa using h)
  mate_mate b := by
    simp only [Equiv.symm_apply_apply]
    rw [M.mate_mate (e.symm b), e.apply_symm_apply]

/-- Vertex equivalences induce equivalences of their matching spaces. -/
def congr (e : α ≃ β) : MatchingOn α ≃ MatchingOn β where
  toFun M := M.transport e
  invFun M := M.transport e.symm
  left_inv M := by ext a; simp [transport]
  right_inv M := by ext b; simp [transport]

/-- A vertex predicate is closed when it contains both endpoints of every
matching edge that touches it. -/
def Closed (M : MatchingOn α) (P : α → Prop) : Prop :=
  ∀ a, P a → P (M.mate a)

/-- The complement of a union of complete matching edges is also closed. -/
theorem closed_compl (M : MatchingOn α) (P : α → Prop) (hP : M.Closed P) :
    M.Closed (fun a ↦ ¬ P a) := by
  intro a ha hm
  have hp := hP (M.mate a) hm
  rw [M.mate_mate a] at hp
  exact ha hp

/-- Restrict a matching to a mate-closed set of surviving labels. -/
def restrict (M : MatchingOn α) (P : α → Prop) (hP : M.Closed P) :
    MatchingOn {a // P a} where
  mate a := ⟨M.mate a.1, hP a.1 a.2⟩
  mate_ne_self a h := M.mate_ne_self a.1 (congrArg Subtype.val h)
  mate_mate a := Subtype.ext (M.mate_mate a.1)

/-- Glue independent matchings on a set and its complement into the unique
matching having the specified mate maps on both sides. -/
def glue (P : α → Prop) [DecidablePred P]
    (L : MatchingOn {a // P a}) (R : MatchingOn {a // ¬ P a}) : MatchingOn α where
  mate a := if ha : P a then (L.mate ⟨a, ha⟩).1 else (R.mate ⟨a, ha⟩).1
  mate_ne_self a h := by
    by_cases ha : P a
    · simp only [dif_pos ha] at h
      exact L.mate_ne_self ⟨a, ha⟩ (Subtype.ext h)
    · simp only [dif_neg ha] at h
      exact R.mate_ne_self ⟨a, ha⟩ (Subtype.ext h)
  mate_mate a := by
    by_cases ha : P a
    · have hb := (L.mate ⟨a, ha⟩).2
      simp only [dif_pos ha, dif_pos hb]
      exact congrArg Subtype.val (L.mate_mate ⟨a, ha⟩)
    · have hb := (R.mate ⟨a, ha⟩).2
      simp only [dif_neg ha, dif_neg hb]
      exact congrArg Subtype.val (R.mate_mate ⟨a, ha⟩)

/-- A full matching extends a fixed exposed matching if it agrees with its
mate map at every exposed vertex. -/
def Extends {P : α → Prop} (M : MatchingOn α) (L : MatchingOn {a // P a}) : Prop :=
  ∀ a : {a // P a}, M.mate a.1 = (L.mate a).1

/-- Agreement with an exposed matching makes its vertex set closed. -/
theorem Extends.closed {P : α → Prop} {M : MatchingOn α} {L : MatchingOn {a // P a}}
    (h : M.Extends L) : M.Closed P := by
  intro a ha
  rw [h ⟨a, ha⟩]
  exact (L.mate ⟨a, ha⟩).2

/-- Gluing always extends the prescribed exposed edges. -/
theorem glue_extends (P : α → Prop) [DecidablePred P]
    (L : MatchingOn {a // P a}) (R : MatchingOn {a // ¬ P a}) :
    (glue P L R).Extends L := by
  intro a
  simp [glue, a.2]

/-- Every matching of the surviving vertices has exactly one extension by a
fixed exposed matching.  This bijection is the combinatorial basis of uniform
conditional survivor laws. -/
def extensionEquiv (P : α → Prop) [DecidablePred P] (L : MatchingOn {a // P a}) :
    {M : MatchingOn α // M.Extends L} ≃ MatchingOn {a // ¬ P a} where
  toFun M := M.1.restrict (fun a ↦ ¬ P a) (M.1.closed_compl P M.2.closed)
  invFun R := ⟨glue P L R, glue_extends P L R⟩
  left_inv M := by
    apply Subtype.ext
    ext a
    by_cases ha : P a
    · simpa [glue, ha] using (M.2 ⟨a, ha⟩).symm
    · simp [glue, ha, restrict]
  right_inv R := by
    ext a
    simp [restrict, glue, a.2]

end MatchingOn


namespace FinDist

variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]

/-- Transport along a finite-type equivalence preserves the uniform law. -/
theorem uniform_map_equiv [Nonempty α] [Nonempty β] [DecidableEq β] (e : α ≃ β) :
    (uniform α).map e = uniform β := by
  ext b
  rw [map_equiv_apply]
  simp [uniform_apply, Fintype.card_congr e]

/-- Under a finite uniform law, an event's mass is the fraction of points
contained in that event. -/
theorem uniform_eventMass [Nonempty α] (E : α → Prop) [DecidablePred E] :
    (uniform α).eventMass E = (Fintype.card {a // E a} : ℝ) / Fintype.card α := by
  unfold eventMass
  simp only [uniform_apply]
  rw [← Finset.sum_filter]
  simp [Fintype.card_subtype, div_eq_mul_inv, nsmul_eq_mul]

/-- A nonempty event has positive mass under a finite uniform law. -/
theorem uniform_eventMass_pos [Nonempty α] (E : α → Prop) [DecidablePred E]
    [Nonempty {a // E a}] : 0 < (uniform α).eventMass E := by
  obtain ⟨a⟩ := ‹Nonempty {a // E a}›
  exact (uniform α).eventMass_pos_of_exists (uniform_strictlyPositive α) E ⟨a.1, a.2⟩

/-- Conditioning a uniform law on a nonempty event gives the uniform law on
that event, embedded back into the ambient sample space. -/
theorem uniform_conditionOn_eq_map_subtype [Nonempty α] [DecidableEq α]
    (E : α → Prop) [DecidablePred E] [Nonempty {a // E a}]
    (hE : 0 < (uniform α).eventMass E) :
    (uniform α).conditionOn E hE = (uniform {a // E a}).map Subtype.val := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsub : (Fintype.card {a // E a} : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext a
  by_cases ha : E a
  · rw [conditionOn_apply_of_mem _ _ _ ha, uniform_apply, uniform_eventMass,
      map_apply, Finset.sum_eq_single ⟨a, ha⟩]
    · simp only [ite_true, uniform_apply]
      field_simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Subtype.ext h)
    · simp
  · rw [conditionOn_apply_of_not_mem _ _ _ ha, map_apply]
    symm
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro h
    exact ha (h ▸ b.2)

end FinDist

namespace MatchingOn

variable {α : Type u} [Fintype α] [DecidableEq α]
variable (P : α → Prop) [DecidablePred P] (L : MatchingOn {a // P a})

/-- Agreement with the finite exposed mate map is a decidable event. -/
instance extendsDecidablePred : DecidablePred (fun M : MatchingOn α ↦ M.Extends L) := by
  intro M
  unfold Extends
  infer_instance

omit [Fintype α] [DecidableEq α] in
/-- Any survivor matching provides a full matching extending the exposed edges. -/
theorem extension_nonempty [Nonempty (MatchingOn {a // ¬ P a})] :
    Nonempty {M : MatchingOn α // M.Extends L} :=
  Nonempty.map (extensionEquiv P L).symm inferInstance

/-- A realizable exposed matching is a positive-probability event under the
ambient uniform matching law. -/
theorem extends_eventMass_pos [Nonempty (MatchingOn α)]
    [Nonempty (MatchingOn {a // ¬ P a})] :
    0 < (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.Extends L) := by
  let : Nonempty {M : MatchingOn α // M.Extends L} := extension_nonempty P L
  exact FinDist.uniform_eventMass_pos _

/-- Conditional on a fixed collection of exposed complete edges, the full
uniform matching law is exactly obtained by gluing those edges to a uniform
matching of the surviving labels.  This is an equality of finite laws, not
merely an equality of mate expectations. -/
theorem uniform_conditionOn_extends [Nonempty (MatchingOn α)]
    [Nonempty (MatchingOn {a // ¬ P a})] :
    (FinDist.uniform (MatchingOn α)).conditionOn (fun M ↦ M.Extends L)
        (extends_eventMass_pos P L) =
      (FinDist.uniform (MatchingOn {a // ¬ P a})).map (glue P L) := by
  let : Nonempty {M : MatchingOn α // M.Extends L} := extension_nonempty P L
  rw [FinDist.uniform_conditionOn_eq_map_subtype]
  have htransport := FinDist.uniform_map_equiv (extensionEquiv P L).symm
  rw [← htransport, FinDist.map_comp]
  rfl

end MatchingOn


namespace FinDist

variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]

/-- A finite pushforward assigns an event exactly its preimage probability. -/
theorem map_eventMass (p : FinDist α) (f : α → β) [DecidableEq β]
    (E : β → Prop) [DecidablePred E] :
    (p.map f).eventMass E = p.eventMass (E ∘ f) := by
  unfold eventMass
  simp only [map_apply]
  calc
    (∑ b, if E b then ∑ a, if f a = b then p a else 0 else 0) =
        ∑ b, ∑ a, if E b then (if f a = b then p a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : E b <;> simp [hb]
    _ = ∑ a, ∑ b, if E b then (if f a = b then p a else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ a, if (E ∘ f) a then p a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (f a)]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp

end FinDist

namespace MatchingOn

variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty (MatchingOn α)]

/-- Uniform matching edge probabilities are invariant under relabeling, for
arbitrary finite vertex labels. -/
theorem uniform_mate_relabel (e : Equiv.Perm α) (i j : α) :
    (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate (e i) = e j) =
      (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate i = j) := by
  have htransport := (FinDist.uniform (MatchingOn α)).map_equiv_eventMass (congr e)
    (fun M ↦ M.mate (e i) = e j)
  rw [FinDist.uniform_map_equiv] at htransport
  refine htransport.trans ?_
  apply FinDist.eventMass_congr
  intro M
  simp [congr, transport]

/-- Distinct prospective mates have equal probabilities under the arbitrary-label
uniform matching law. -/
theorem uniform_mate_eq_of_ne (i j k : α) (hij : i ≠ j) (hik : i ≠ k) :
    (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate i = j) =
      (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate i = k) := by
  have he := uniform_mate_relabel (Equiv.swap j k) i j
  simpa only [Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_left] using he.symm

/-- Self-matching is impossible under the arbitrary-label uniform law. -/
theorem uniform_mate_self (i : α) :
    (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate i = i) = 0 := by
  unfold FinDist.eventMass
  apply Finset.sum_eq_zero
  intro M _
  rw [if_neg (M.mate_ne_self i)]

/-- The arbitrary-label mate probabilities are normalized. -/
theorem sum_uniform_mate (i : α) :
    (∑ j, (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate i = j)) = 1 := by
  unfold FinDist.eventMass
  rw [Finset.sum_comm]
  calc
    (∑ M, ∑ j, if M.mate i = j then FinDist.uniform (MatchingOn α) M else 0) =
        ∑ M, FinDist.uniform (MatchingOn α) M := by
      apply Finset.sum_congr rfl
      intro M _
      simp
    _ = 1 := (FinDist.uniform (MatchingOn α)).sum_mass

/-- In any inhabited finite matching space, a vertex's mate is uniform on the
other vertex labels.  This formulation applies directly to survivor subtypes. -/
theorem uniform_mate_probability (i j : α) (hij : i ≠ j) :
    (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate i = j) =
      1 / ((Fintype.card α - 1 : ℕ) : ℝ) := by
  let mass : α → ℝ := fun k ↦ (FinDist.uniform (MatchingOn α)).eventMass (fun M ↦ M.mate i = k)
  have hzero : mass i = 0 := uniform_mate_self i
  have hconstant : ∀ k ∈ Finset.univ.erase i, mass k = mass j := by
    intro k hk
    exact uniform_mate_eq_of_ne i k j (Finset.mem_erase.mp hk).1.symm hij
  have hsum : ((Fintype.card α - 1 : ℕ) : ℝ) * mass j = 1 := by
    calc
      ((Fintype.card α - 1 : ℕ) : ℝ) * mass j = ∑ _k ∈ Finset.univ.erase i, mass j := by
        simp [nsmul_eq_mul]
      _ = ∑ k ∈ Finset.univ.erase i, mass k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hconstant k hk).symm
      _ = ∑ k, mass k := by
        simpa only [hzero, add_zero] using
          (Finset.sum_erase_add Finset.univ mass (Finset.mem_univ i))
      _ = 1 := sum_uniform_mate i
  have htwo : 2 ≤ Fintype.card α := by
    let : Nontrivial α := ⟨⟨i, j, hij⟩⟩
    exact Fintype.one_lt_card
  have hden : ((Fintype.card α - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card α - 1 ≠ 0)
  apply (eq_div_iff hden).2
  simpa [mul_comm] using hsum

/-- After fixing exposed complete edges, each survivor's mate is exactly
uniform among the other survivors.  The exposed-edge event has been identified
explicitly; no adaptive-transcript invariant is assumed or claimed here. -/
theorem conditioned_mate_probability (P : α → Prop) [DecidablePred P]
    (L : MatchingOn {a // P a}) [Nonempty (MatchingOn {a // ¬ P a})]
    (i j : {a // ¬ P a}) (hij : i ≠ j) :
    ((FinDist.uniform (MatchingOn α)).conditionOn (fun M ↦ M.Extends L)
      (extends_eventMass_pos P L)).eventMass (fun M ↦ M.mate i.1 = j.1) =
        1 / ((Fintype.card {a // ¬ P a} - 1 : ℕ) : ℝ) := by
  rw [uniform_conditionOn_extends, FinDist.map_eventMass]
  calc
    (FinDist.uniform (MatchingOn {a // ¬ P a})).eventMass
        ((fun M : MatchingOn α ↦ M.mate i.1 = j.1) ∘ glue P L) =
        (FinDist.uniform (MatchingOn {a // ¬ P a})).eventMass (fun M ↦ M.mate i = j) := by
      apply FinDist.eventMass_congr
      intro M
      change (glue P L M).mate i.1 = j.1 ↔ M.mate i = j
      simp [glue, i.2, Subtype.ext_iff]
    _ = 1 / ((Fintype.card {a // ¬ P a} - 1 : ℕ) : ℝ) := uniform_mate_probability i j hij

end MatchingOn

end ForestSampling
