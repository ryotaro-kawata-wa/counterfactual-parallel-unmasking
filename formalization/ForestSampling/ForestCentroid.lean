import ForestSampling.ForestModel

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling.ForestCentroid

/-!
# Centroids of actual finite trees

A centroid is obtained by minimizing the sum of graph distances. Deleting
that vertex leaves only components of size at most half the original size.
-/

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Delete one vertex, retaining the true induced graph on all other vertices. -/
abbrev deleteVertex (G : SimpleGraph A) (v : A) : SimpleGraph {w : A // w ≠ v} :=
  G.induce {w | w ≠ v}

omit [Fintype A] [DecidableEq A] in
/-- In an acyclic graph, every path already has the shortest possible length. -/
theorem path_length_eq_dist (G : SimpleGraph A) (hG : G.IsAcyclic)
    {u v : A} (p : G.Walk u v) (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq, hdist⟩ := p.reachable.exists_path_of_dist
  have heq : p = q := congrArg Subtype.val
    ((hG.subsingleton_path u v).elim (⟨p, hp⟩ : G.Path u v) ⟨q, hq⟩)
  exact heq ▸ hdist

omit [Fintype A] [DecidableEq A] in
/-- Every component after deleting a vertex of a connected graph contains a
neighbor of that vertex. This statement does not require acyclicity. -/
theorem component_has_neighbor (G : SimpleGraph A) (hG : G.Connected)
    (v : A) (C : (deleteVertex G v).ConnectedComponent) :
    ∃ u : {w : A // w ≠ v}, G.Adj v u.1 ∧ u ∈ C.supp := by
  classical
  obtain ⟨w, hw⟩ := C.nonempty_supp
  obtain ⟨p, hp⟩ := hG.exists_isPath v w.1
  have hnil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne w.2.symm
  have hpcons : (p.tail.cons (p.adj_snd hnil)).IsPath := by
    rw [p.cons_tail_eq hnil]
    exact hp
  have htail := (SimpleGraph.Walk.cons_isPath_iff (p.adj_snd hnil) p.tail).mp hpcons
  have hav : ∀ a ∈ p.tail.support, a ∈ ({a | a ≠ v} : Set A) := by
    intro a ha hav
    exact htail.2 (hav ▸ ha)
  let u' : {a : A // a ≠ v} := ⟨p.snd, (p.adj_snd hnil).ne.symm⟩
  have hr : (deleteVertex G v).Reachable u' w :=
    (p.tail.induce {a | a ≠ v} hav).reachable
  refine ⟨u', p.adj_snd hnil, ?_⟩
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff C u').mpr
    ((SimpleGraph.ConnectedComponent.sound hr).trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff C w).mp hw))

omit [Fintype A] [DecidableEq A] in
/-- A path avoiding the deleted vertex must approach its component through
that component's incident neighbor. Acyclicity makes the prefixed path unique. -/
theorem dist_eq_add_one_in_deleted_component (G : SimpleGraph A)
    (hG : G.IsAcyclic) (v : A) (u w : {a : A // a ≠ v})
    (hu : G.Adj v u.1) (hr : (deleteVertex G v).Reachable u w) :
    G.dist v w.1 = G.dist u.1 w.1 + 1 := by
  classical
  obtain ⟨p, hp⟩ := hr.exists_isPath
  let e : deleteVertex G v ↪g G := SimpleGraph.Embedding.induce _
  let q : G.Walk u.1 w.1 := p.map e.toHom
  have hq : q.IsPath := hp.map e.injective
  have hvq : v ∉ q.support := by
    change v ∉ (p.map e.toHom).support
    rw [SimpleGraph.Walk.support_map]
    intro hv
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hv
    exact a.2 ha
  have hpref : (q.cons hu).IsPath := hq.cons hvq
  have h1 := path_length_eq_dist G hG (q.cons hu) hpref
  have h2 := path_length_eq_dist G hG q hq
  simpa only [SimpleGraph.Walk.length_cons, h2] using h1.symm

/-- Vertices of a deleted-graph component, represented in the original type. -/
noncomputable def componentVertices (G : SimpleGraph A) (v : A)
    (C : (deleteVertex G v).ConnectedComponent) : Finset A := by
  classical
  exact C.supp.toFinset.map (Function.Embedding.subtype (fun a : A ↦ a ≠ v))

/-- The representation preserves the actual connected-component cardinality. -/
theorem componentVertices_card (G : SimpleGraph A) (v : A)
    (C : (deleteVertex G v).ConnectedComponent) :
    (componentVertices G v C).card = Nat.card C := by
  classical
  rw [componentVertices, Finset.card_map, Set.toFinset_card, Nat.card_eq_fintype_card]
  simp only [← Nat.card_eq_fintype_card]
  rfl

/-- A centroid halves every component left by deleting it. -/
def IsCentroid (G : SimpleGraph A) (v : A) : Prop :=
  ∀ C : (deleteVertex G v).ConnectedComponent, 2 * Nat.card C ≤ Nat.card A

/-- Any vertex minimizing total distance is a centroid of a finite tree. -/
theorem isCentroid_of_minimal_distance_sum (G : SimpleGraph A) (hG : G.IsTree)
    (v : A) (hmin : ∀ u, (∑ a, G.dist v a) ≤ ∑ a, G.dist u a) :
    IsCentroid G v := by
  classical
  intro C
  obtain ⟨u, hu, huC⟩ := component_has_neighbor G hG.connected v C
  let S := componentVertices G v C
  have hstep (a : A) : G.dist u.1 a + 2 * (if a ∈ S then 1 else 0) ≤
      G.dist v a + 1 := by
    by_cases ha : a ∈ S
    · simp only [ha, ite_true, mul_one]
      change a ∈ C.supp.toFinset.map (Function.Embedding.subtype (fun a : A ↦ a ≠ v)) at ha
      obtain ⟨w, hw, hwa⟩ := Finset.mem_map.mp ha
      have hwC : w ∈ C.supp := Set.mem_toFinset.mp hw
      have hdist := dist_eq_add_one_in_deleted_component G hG.isAcyclic v u w hu
        (C.reachable_of_mem_supp huC hwC)
      change w.1 = a at hwa
      rw [hwa] at hdist
      omega
    · simp only [ha, ite_false, mul_zero, add_zero]
      have htriangle := hG.connected.dist_triangle (u := u.1) (v := v) (w := a)
      have hdist : G.dist u.1 v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu.symm
      rw [hdist] at htriangle
      omega
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) ↦ hstep a)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one] at hsum
  have hcard : (∑ a : A, if a ∈ S then 1 else 0) = S.card := by simp
  rw [hcard] at hsum
  have hminu := hmin u.1
  have hbound : 2 * S.card ≤ Fintype.card A := by omega
  change 2 * Nat.card C ≤ Nat.card A
  simpa only [S, componentVertices_card, ← Nat.card_eq_fintype_card] using hbound

/-- Every nonempty finite tree has an actual vertex whose removal halves
all remaining connected components. -/
theorem exists_centroid (G : SimpleGraph A) (hG : G.IsTree) :
    ∃ v, IsCentroid G v := by
  classical
  let : Nonempty A := hG.nonempty
  obtain ⟨v, _, hv⟩ := Finset.univ.exists_min_image (fun v ↦ ∑ a, G.dist v a)
    Finset.univ_nonempty
  exact ⟨v, isCentroid_of_minimal_distance_sum G hG v (fun u ↦ hv u (Finset.mem_univ u))⟩

/-- Choose one genuine centroid in each component of a finite forest. -/
noncomputable def componentCentroid (G : SimpleGraph A) (hG : G.IsAcyclic)
    (C : G.ConnectedComponent) : C := by
  classical
  exact Classical.choose (exists_centroid C.toSimpleGraph (hG.isTree_connectedComponent C))

/-- Every chosen component vertex satisfies the actual half-size condition. -/
theorem componentCentroid_spec (G : SimpleGraph A) (hG : G.IsAcyclic)
    (C : G.ConnectedComponent) :
    IsCentroid C.toSimpleGraph (componentCentroid G hG C) := by
  classical
  exact Classical.choose_spec (exists_centroid C.toSimpleGraph (hG.isTree_connectedComponent C))

/-- Batch one chosen vertex from each actual connected component. The
separation statements hold for any choice, including a smallest-label rule. -/
noncomputable def componentBatch (G : SimpleGraph A)
    (pick : (C : G.ConnectedComponent) → C) : Finset A := by
  classical
  letI := Fintype.ofFinite G.ConnectedComponent
  exact Finset.univ.image (fun C ↦ (pick C).1)

/-- Membership records precisely which component selected the vertex. -/
theorem mem_componentBatch (G : SimpleGraph A)
    (pick : (C : G.ConnectedComponent) → C) (v : A) :
    v ∈ componentBatch G pick ↔ ∃ C, (pick C).1 = v := by
  classical
  simp [componentBatch]

omit [Fintype A] [DecidableEq A] in
/-- A selected vertex lies in the component that selected it. -/
theorem component_of_pick (G : SimpleGraph A)
    (pick : (C : G.ConnectedComponent) → C) (C : G.ConnectedComponent) :
    G.connectedComponentMk (pick C).1 = C := (pick C).2

omit [Fintype A] [DecidableEq A] in
/-- Different components necessarily select different vertices. -/
theorem pick_injective (G : SimpleGraph A)
    (pick : (C : G.ConnectedComponent) → C) :
    Function.Injective (fun C ↦ (pick C).1) := by
  intro C D h
  have heq := congrArg G.connectedComponentMk h
  simpa only [component_of_pick] using heq

/-- The selected batch contains exactly one vertex per connected component. -/
theorem componentBatch_card (G : SimpleGraph A)
    (pick : (C : G.ConnectedComponent) → C) :
    (componentBatch G pick).card = Nat.card G.ConnectedComponent := by
  classical
  rw [componentBatch, Finset.card_image_of_injective _ (pick_injective G pick)]
  simp only [Finset.card_univ, ← Nat.card_eq_fintype_card]

/-- Two selected vertices can be connected only if they are the same vertex.
This is the structural batch-independence condition needed by exact commits. -/
theorem componentBatch_separated (G : SimpleGraph A)
    (pick : (C : G.ConnectedComponent) → C) (u v : A)
    (hu : u ∈ componentBatch G pick) (hv : v ∈ componentBatch G pick)
    (hr : G.Reachable u v) : u = v := by
  obtain ⟨C, rfl⟩ := (mem_componentBatch G pick u).mp hu
  obtain ⟨D, rfl⟩ := (mem_componentBatch G pick v).mp hv
  have hCD := SimpleGraph.ConnectedComponent.sound hr
  simp only [component_of_pick] at hCD
  subst D
  rfl

/-- Every original vertex is connected to a member of the selected batch,
so a nonempty forest always makes progress. -/
theorem componentBatch_covers (G : SimpleGraph A)
    (pick : (C : G.ConnectedComponent) → C) (v : A) :
    ∃ u ∈ componentBatch G pick, G.Reachable v u := by
  let C := G.connectedComponentMk v
  refine ⟨(pick C).1, (mem_componentBatch G pick _).mpr ⟨C, rfl⟩, ?_⟩
  exact SimpleGraph.ConnectedComponent.exact (component_of_pick G pick C).symm

/-- A nonempty current graph yields a nonempty selected batch. -/
theorem componentBatch_nonempty (G : SimpleGraph A)
    (pick : (C : G.ConnectedComponent) → C) [Nonempty A] :
    (componentBatch G pick).Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty A›
  obtain ⟨u, hu, _⟩ := componentBatch_covers G pick v
  exact ⟨u, hu⟩

/-- After deleting the chosen centroids (and possibly other vertices), every
remaining component has at most half as many vertices as its actual parent
component. The proof embeds it into a child of the parent's deleted centroid. -/
theorem component_halves_after_deleting_centroids (G : SimpleGraph A)
    (pick : (D : G.ConnectedComponent) → D)
    (hcent : ∀ D, IsCentroid D.toSimpleGraph (pick D))
    (S : Finset A) (havoid : Disjoint S (componentBatch G pick))
    (C : (G.induce (S : Set A)).ConnectedComponent) :
    2 * Nat.card C ≤ Nat.card (C.map (SimpleGraph.Embedding.induce (S : Set A)).toHom) := by
  classical
  let H := G.induce (S : Set A)
  let e : H ↪g G := SimpleGraph.Embedding.induce (S : Set A)
  let D := C.map e.toHom
  have hparent (x : C) : G.connectedComponentMk x.1.1 = D := by
    calc
      G.connectedComponentMk x.1.1 = (H.connectedComponentMk x.1).map e.toHom := rfl
      _ = C.map e.toHom := congrArg (fun c ↦ c.map e.toHom) x.2
  have hne (x : C) : (⟨x.1.1, hparent x⟩ : D) ≠ pick D := by
    intro heq
    have heqv := congrArg Subtype.val heq
    have hmem : (pick D).1 ∈ componentBatch G pick :=
      (mem_componentBatch G pick _).mpr ⟨D, rfl⟩
    exact Finset.disjoint_left.mp havoid x.1.2 (heqv ▸ hmem)
  let f : C.toSimpleGraph →g deleteVertex D.toSimpleGraph (pick D) :=
    { toFun := fun x ↦ ⟨⟨x.1.1, hparent x⟩, hne x⟩
      map_rel' := fun h ↦ h }
  let w : C := ⟨C.nonempty_supp.choose, C.nonempty_supp.choose_spec⟩
  let E := (deleteVertex D.toSimpleGraph (pick D)).connectedComponentMk (f w)
  have hchild (x : C) : f x ∈ E.supp := by
    exact SimpleGraph.ConnectedComponent.sound
      ((C.connected_toSimpleGraph x w).some.map f).reachable
  let lift : C → E := fun x ↦ ⟨f x, hchild x⟩
  have hinj : Function.Injective lift := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : E ↦ z.1.1.1) hxy
  have hcard : Nat.card C ≤ Nat.card E := Nat.card_le_card_of_injective lift hinj
  exact (Nat.mul_le_mul_left 2 hcard).trans (hcent D E)

/-- In particular, deleting precisely the centroid batch halves each actual
parent component. This is the one-layer statement needed for recursion. -/
theorem component_halves_after_centroid_batch (G : SimpleGraph A)
    (pick : (D : G.ConnectedComponent) → D)
    (hcent : ∀ D, IsCentroid D.toSimpleGraph (pick D))
    (C : (G.induce ((Finset.univ \ componentBatch G pick : Finset A) : Set A)).ConnectedComponent) :
    2 * Nat.card C ≤ Nat.card
      (C.map (SimpleGraph.Embedding.induce
        ((Finset.univ \ componentBatch G pick : Finset A) : Set A)).toHom) :=
  component_halves_after_deleting_centroids G pick hcent _ Finset.sdiff_disjoint C

end ForestSampling.ForestCentroid
