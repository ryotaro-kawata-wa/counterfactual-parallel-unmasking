import ForestSampling.ForestPeeling
import ForestSampling.ForestCentroid
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.ForestIteration

/-- The public logarithmic number of completed peeling phases. -/
noncomputable def phaseCap (N D : ℕ) : ℕ :=
  ⌈max (Real.log (2 * (N : ℝ) / (D + 1))) 0 / Real.log ((D : ℝ) / 8)⌉₊

/-- The public number of centroid layers, including the strict final margin. -/
noncomputable def centroidDepth (N : ℕ) : ℕ := ⌈Real.logb 2 (N + 1 : ℕ)⌉₊

/-- The ceiling in the phase cap gives the required geometric reduction,
including the case in which the initial high-degree upper bound is at most one. -/
theorem phaseCap_geometric (N D : ℕ) (hN : 0 < N) (hD : 9 ≤ D) :
    (8 / (D : ℝ)) ^ phaseCap N D * (2 * (N : ℝ) / (D + 1)) ≤ 1 := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hb : 1 < (D : ℝ) / 8 := by rw [lt_div_iff₀ (by norm_num)]; exact_mod_cast hD
  have hx : 0 < 2 * (N : ℝ) / (D + 1) := by positivity
  have hlog : 0 < Real.log ((D : ℝ) / 8) := Real.log_pos hb
  have hpow : 2 * (N : ℝ) / (D + 1) ≤ ((D : ℝ) / 8) ^ phaseCap N D := by
    rw [← Real.rpow_natCast]
    apply (Real.logb_le_iff_le_rpow hb hx).mp
    calc
      Real.logb ((D : ℝ) / 8) (2 * (N : ℝ) / (D + 1)) ≤
          max (Real.log (2 * (N : ℝ) / (D + 1))) 0 / Real.log ((D : ℝ) / 8) := by
        exact div_le_div_of_nonneg_right (le_max_left _ _) hlog.le
      _ ≤ (phaseCap N D : ℝ) := Nat.le_ceil _
  calc
    (8 / (D : ℝ)) ^ phaseCap N D * (2 * (N : ℝ) / (D + 1)) ≤
        (8 / (D : ℝ)) ^ phaseCap N D * ((D : ℝ) / 8) ^ phaseCap N D := by gcongr
    _ = 1 := by
      rw [← mul_pow]
      have heq : 8 / (D : ℝ) * ((D : ℝ) / 8) = 1 := by field_simp
      rw [heq]
      simp

/-- The manuscript's threshold range makes the phase cap positive. This
condition is essential when converting a sum of strict per-phase bounds
into a strict total bound. -/
theorem phaseCap_pos (N D : ℕ) (hD : 9 ≤ D) (hND : D + 1 < 2 * N) :
    0 < phaseCap N D := by
  rw [phaseCap, Nat.ceil_pos]
  have hb : 1 < (D : ℝ) / 8 := by
    rw [lt_div_iff₀ (by norm_num)]
    exact_mod_cast hD
  have hx : 1 < 2 * (N : ℝ) / (D + 1) := by
    rw [lt_div_iff₀ (by positivity)]
    exact_mod_cast (by simpa using hND)
  exact div_pos ((Real.log_pos hx).trans_le (le_max_left _ _)) (Real.log_pos hb)

/-- The public cap reserves two rounds beyond the real successful-path
estimate, as in the manuscript. -/
noncomputable def hardRoundCap (N D : ℕ) : ℕ :=
  ⌈4 * (N : ℝ) * phaseCap N D / D⌉₊ + centroidDepth N + 2

/-- Bounds on actual peeling and centroid rounds place the completed work
strictly before the reserved final-round guard. -/
theorem rounds_lt_reserved (N D p t : ℕ)
    (hp : (p : ℝ) ≤ 4 * (N : ℝ) * phaseCap N D / D)
    (ht : t ≤ centroidDepth N) : p + t < hardRoundCap N D - 1 := by
  have hc : p ≤ ⌈4 * (N : ℝ) * phaseCap N D / D⌉₊ := by
    exact_mod_cast hp.trans (Nat.le_ceil _)
  unfold hardRoundCap
  omega

/-- An integer sequence with a strict initial estimate preserves that strict
estimate under a positive geometric contraction. -/
theorem geometric_count_lt (a : ℕ → ℕ) (q b : ℝ) (hq : 0 < q)
    (h0 : (a 0 : ℝ) < b) (k : ℕ)
    (hstep : ∀ i < k, (a (i + 1) : ℝ) ≤ q * a i) :
    (a k : ℝ) < q ^ k * b := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
      have hi := ih (fun i hi ↦ hstep i (by omega))
      calc
        (a (k + 1) : ℝ) ≤ q * a k := hstep k (by omega)
        _ < q * (q ^ k * b) := mul_lt_mul_of_pos_left hi hq
        _ = q ^ (k + 1) * b := by rw [pow_succ]; ring

/-- The manuscript's exact phase cap exhausts every actual high-degree count
once the forest count and successful-phase inequalities have been established. -/
theorem high_count_zero_at_phaseCap (a : ℕ → ℕ) (N D : ℕ)
    (hN : 0 < N) (hD : 9 ≤ D)
    (h0 : (a 0 : ℝ) < 2 * (N : ℝ) / (D + 1))
    (hstep : ∀ i < phaseCap N D, (a (i + 1) : ℝ) ≤ (8 / (D : ℝ)) * a i) :
    a (phaseCap N D) = 0 := by
  have hq : 0 < 8 / (D : ℝ) := by positivity
  have hlt := (geometric_count_lt a _ _ hq h0 _ hstep).trans_le (phaseCap_geometric N D hN hD)
  have hn : a (phaseCap N D) < 1 := by exact_mod_cast hlt
  omega

/-- The ceiling of the binary logarithm is strictly beyond the number of
vertices, so integral component sizes vanish at the final layer. -/
theorem lt_two_pow_centroidDepth (N : ℕ) : N < 2 ^ centroidDepth N := by
  rw [centroidDepth, ← Nat.cast_ofNat (R := ℝ) (n := 2), Real.natCeil_logb_natCast]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.le_pow_clog (by decide) (N + 1))

section Graphs

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable {G : SimpleGraph A} {H : SimpleGraph B} [DecidableRel G.Adj] [DecidableRel H.Adj]

omit [DecidableEq A] [DecidableEq B] in
/-- A graph embedding injects each actual neighbor set into its image's
neighbor set. This applies to every induced restriction used below. -/
theorem degree_le_of_embedding (e : H ↪g G) (v : B) : H.degree v ≤ G.degree (e v) := by
  classical
  simp only [← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective (fun w : H.neighborSet v ↦
    (⟨e w.1, e.map_rel_iff.mpr w.2⟩ : G.neighborSet (e v)))
    (fun x y h ↦ Subtype.ext (e.injective (congrArg Subtype.val h)))

omit [DecidableEq A] [DecidableEq B] in
/-- High-degree vertices of an embedded graph inject into genuine high-degree
vertices of the ambient graph. -/
theorem high_card_le_of_embedding (e : H ↪g G) (D : ℕ) :
    (ForestPeeling.highVertices H D).card ≤ (ForestPeeling.highVertices G D).card := by
  classical
  have hsub : (ForestPeeling.highVertices H D).map e.toEmbedding ⊆ ForestPeeling.highVertices G D := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    exact (ForestPeeling.mem_highVertices G D _).mpr
      (((ForestPeeling.mem_highVertices H D w).mp hw).trans_le (degree_le_of_embedding e w))
  simpa using Finset.card_le_card hsub

omit [DecidableEq B] in
/-- Avoiding the selected peel vertices embeds the next graph into the exact
post-peeling induced graph, so successful screening gives the actual contraction. -/
theorem high_card_after_peeling (e : H ↪g G) (hG : G.IsAcyclic) (D : ℕ)
    (rows : A → Finset A) (hrows : ForestPeeling.ScreenContract G D rows)
    (havoid : ∀ v, e v ∉ ForestPeeling.peelSet D rows) :
    D * (ForestPeeling.highVertices H D).card ≤ 4 * (ForestPeeling.highVertices G D).card := by
  classical
  let S := Finset.univ \ ForestPeeling.peelSet D rows
  let f : H ↪g G.induce (S : Set A) :=
    { toFun := fun v ↦ ⟨e v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, havoid v⟩⟩
      inj' := fun x y h ↦ e.injective (congrArg Subtype.val h)
      map_rel_iff' := e.map_rel_iff }
  have hcard := high_card_le_of_embedding f D
  rw [ForestPeeling.highVertices_induce_card] at hcard
  exact (Nat.mul_le_mul_left D hcard).trans (ForestPeeling.next_high_contraction hG hrows)

omit [Fintype B] [DecidableEq B] [DecidableRel G.Adj] [DecidableRel H.Adj] in
/-- A component embedded away from every chosen centroid lies in one of the
actual half-size children of its parent component. -/
theorem component_halves_of_embedding (e : H ↪g G)
    (pick : (C : G.ConnectedComponent) → C)
    (hcent : ∀ C, ForestCentroid.IsCentroid C.toSimpleGraph (pick C))
    (havoid : ∀ v, e v ∉ ForestCentroid.componentBatch G pick)
    (C : H.ConnectedComponent) :
    2 * Nat.card C ≤ Nat.card (C.map e.toHom) := by
  classical
  let D := C.map e.toHom
  have hparent (x : C) : G.connectedComponentMk (e x.1) = D := by
    change (H.connectedComponentMk x.1).map e.toHom = C.map e.toHom
    rw [x.2]
  have hne (x : C) : (⟨e x.1, hparent x⟩ : D) ≠ pick D := by
    intro heq
    have hv : e x.1 = (pick D).1 := congrArg Subtype.val heq
    apply havoid x.1
    rw [hv]
    exact (ForestCentroid.mem_componentBatch G pick _).mpr ⟨D, rfl⟩
  let f : C.toSimpleGraph →g ForestCentroid.deleteVertex D.toSimpleGraph (pick D) :=
    { toFun := fun x ↦ ⟨⟨e x.1, hparent x⟩, hne x⟩
      map_rel' := fun h ↦ e.map_rel_iff.mpr h }
  let w : C := ⟨C.nonempty_supp.choose, C.nonempty_supp.choose_spec⟩
  let E := (ForestCentroid.deleteVertex D.toSimpleGraph (pick D)).connectedComponentMk (f w)
  have hchild (x : C) : f x ∈ E.supp :=
    SimpleGraph.ConnectedComponent.sound ((C.connected_toSimpleGraph x w).some.map f).reachable
  let lift : C → E := fun x ↦ ⟨f x, hchild x⟩
  have hinj : Function.Injective lift := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun z : E ↦ z.1.1.1) hxy
  exact (Nat.mul_le_mul_left 2 (Nat.card_le_card_of_injective lift hinj)).trans (hcent D E)

end Graphs

/-- An actual sequence of remaining original-label vertex sets. The only
structural field says that vertices are deleted and never reintroduced. -/
structure DeletionSequence (A : Type*) where
  remaining : ℕ → Finset A
  nested : ∀ i, remaining (i + 1) ⊆ remaining i

namespace DeletionSequence

variable {A : Type*} [Fintype A] [DecidableEq A]
variable (S : DeletionSequence A) (G : SimpleGraph A) [DecidableRel G.Adj]

/-- The graph at a phase is the true graph induced by its remaining vertices. -/
abbrev graph (i : ℕ) := G.induce (S.remaining i : Set A)

/-- The inclusion of consecutive actual residual graphs. -/
def stepEmbedding (i : ℕ) : S.graph G (i + 1) ↪g S.graph G i :=
  G.induceHomOfLE (fun _ hv ↦ S.nested i hv)

/-- The actual number of high-degree vertices at the indicated phase. -/
def highCount (D i : ℕ) : ℕ := (ForestPeeling.highVertices (S.graph G i) D).card

omit [Fintype A] in
/-- Successful rows and deletion of their frozen peel set imply the sharp
contraction for the actual next remaining vertex set. -/
theorem peeling_contraction (hG : G.IsAcyclic) (D i : ℕ)
    (rows : ↥(S.remaining i : Set A) → Finset (S.remaining i : Set A))
    (hrows : ForestPeeling.ScreenContract (S.graph G i) D rows)
    (havoid : ∀ v : (S.remaining (i + 1) : Set A),
      S.stepEmbedding G i v ∉ ForestPeeling.peelSet D rows) :
    D * S.highCount G D (i + 1) ≤ 4 * S.highCount G D i :=
  high_card_after_peeling (S.stepEmbedding G i) (hG.induce _) D rows hrows havoid

omit [Fintype A] in
/-- The real public contraction follows from genuine residual-graph degrees. -/
theorem peeling_contraction_public (hG : G.IsAcyclic) (D i : ℕ) (hD : 0 < D)
    (rows : ↥(S.remaining i : Set A) → Finset (S.remaining i : Set A))
    (hrows : ForestPeeling.ScreenContract (S.graph G i) D rows)
    (havoid : ∀ v : (S.remaining (i + 1) : Set A),
      S.stepEmbedding G i v ∉ ForestPeeling.peelSet D rows) :
    (S.highCount G D (i + 1) : ℝ) ≤ (8 / (D : ℝ)) * S.highCount G D i := by
  have hnat := S.peeling_contraction G hG D i rows hrows havoid
  have hreal : (D : ℝ) * S.highCount G D (i + 1) ≤ 4 * S.highCount G D i := by
    exact_mod_cast hnat
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  calc
    (S.highCount G D (i + 1) : ℝ) ≤ (4 * S.highCount G D i) / D := by
      apply (le_div_iff₀ hDp).mpr
      nlinarith
    _ ≤ (8 / (D : ℝ)) * S.highCount G D i := by
      rw [div_mul_eq_mul_div]
      gcongr
      norm_num

omit [DecidableEq A] in
/-- The initial residual high-degree count satisfies the strict forest bound,
even when the sequence starts after some vertices have already been deleted. -/
theorem initial_highCount_lt (hG : G.IsAcyclic) (D : ℕ) [Nonempty A] :
    (S.highCount G D 0 : ℝ) < 2 * (Fintype.card A : ℝ) / (D + 1) := by
  have hc := high_card_le_of_embedding
    (SimpleGraph.Embedding.induce (S.remaining 0 : Set A) : S.graph G 0 ↪g G) D
  have hi := ForestPeeling.initial_high_count (G := G) hG D
  have hm : (D + 1) * S.highCount G D 0 < 2 * Fintype.card A :=
    (Nat.mul_le_mul_left (D + 1) hc).trans_lt hi
  apply (lt_div_iff₀ (show (0 : ℝ) < D + 1 by positivity)).mpr
  exact_mod_cast (by simpa [Nat.mul_comm] using hm)

/-- By the exact logarithmic phase cap, successful screens leave no genuine
high-degree vertices. No assumed numerical recurrence occurs in the hypotheses. -/
theorem highCount_zero_at_phaseCap (hG : G.IsAcyclic) (D : ℕ) (hD : 9 ≤ D)
    (rows : ∀ i, ↥(S.remaining i : Set A) → Finset (S.remaining i : Set A))
    (hrows : ∀ i < phaseCap (Fintype.card A) D,
      ForestPeeling.ScreenContract (S.graph G i) D (rows i))
    (havoid : ∀ i < phaseCap (Fintype.card A) D, ∀ v : (S.remaining (i + 1) : Set A),
      S.stepEmbedding G i v ∉ ForestPeeling.peelSet D (rows i)) :
    S.highCount G D (phaseCap (Fintype.card A) D) = 0 := by
  classical
  cases isEmpty_or_nonempty A
  · simp [highCount, ForestPeeling.highVertices]
  · exact high_count_zero_at_phaseCap (S.highCount G D) (Fintype.card A) D
      Fintype.card_pos hD (S.initial_highCount_lt G hG D)
      (fun i hi ↦ S.peeling_contraction_public G hG D i (by omega) (rows i)
        (hrows i hi) (havoid i hi))

omit [Fintype A] [DecidableEq A] in
/-- Zero actual high-degree count certifies the degree premise needed by the
last successful screen to recover every row exactly. -/
theorem degree_le_of_highCount_zero (D i : ℕ) (hz : S.highCount G D i = 0)
    (v : (S.remaining i : Set A)) : (S.graph G i).degree v ≤ D := by
  have he : ForestPeeling.highVertices (S.graph G i) D = ∅ := Finset.card_eq_zero.mp hz
  by_contra h
  have hv := (ForestPeeling.mem_highVertices (S.graph G i) D v).mpr (Nat.lt_of_not_ge h)
  simp [he] at hv

/-- The extra final screen is exact at every remaining vertex after the cap. -/
theorem final_rows_exact (hG : G.IsAcyclic) (D : ℕ) (hD : 9 ≤ D)
    (rows : ∀ i, ↥(S.remaining i : Set A) → Finset (S.remaining i : Set A))
    (hrows : ∀ i ≤ phaseCap (Fintype.card A) D,
      ForestPeeling.ScreenContract (S.graph G i) D (rows i))
    (havoid : ∀ i < phaseCap (Fintype.card A) D, ∀ v : (S.remaining (i + 1) : Set A),
      S.stepEmbedding G i v ∉ ForestPeeling.peelSet D (rows i)) :
    ∀ v, rows (phaseCap (Fintype.card A) D) v =
      (S.graph G (phaseCap (Fintype.card A) D)).neighborFinset v := by
  intro v
  apply (hrows _ le_rfl).exact_low
  exact S.degree_le_of_highCount_zero G D _
    (S.highCount_zero_at_phaseCap G hG D hD rows (fun i hi ↦ hrows i hi.le) havoid) v

/-- A frozen peel set is small in original-label cardinality, including an
empty residual graph. Strictness uses only a nonempty ambient vertex type. -/
theorem peel_card_lt (hG : G.IsAcyclic) (D i : ℕ) [Nonempty A]
    (rows : ↥(S.remaining i : Set A) → Finset (S.remaining i : Set A))
    (hrows : ForestPeeling.ScreenContract (S.graph G i) D rows) :
    D * (ForestPeeling.peelSet D rows).card < 4 * Fintype.card A := by
  classical
  cases isEmpty_or_nonempty (S.remaining i : Set A)
  · simp only [Finset.card_eq_zero.mpr (Finset.eq_empty_of_isEmpty _), Nat.mul_zero]
    exact Nat.mul_pos (by decide) Fintype.card_pos
  · have h := ForestPeeling.peelSet_card_bound (hG.induce (S.remaining i : Set A)) hrows
    exact h.trans_le (Nat.mul_le_mul_left 4
      (Fintype.card_le_of_injective Subtype.val Subtype.val_injective))

/-- Summing the actual frozen sets gives the manuscript's `4*N*J/D` total,
with one singleton commit per selected vertex and no geometric-sum shortcut. -/
theorem sum_peel_card_lt (hG : G.IsAcyclic) (D k : ℕ) (hk : 0 < k) [Nonempty A]
    (rows : ∀ i, ↥(S.remaining i : Set A) → Finset (S.remaining i : Set A))
    (hrows : ∀ i < k, ForestPeeling.ScreenContract (S.graph G i) D (rows i)) :
    D * (∑ i ∈ Finset.range k, (ForestPeeling.peelSet D (rows i)).card) <
      4 * Fintype.card A * k := by
  rw [Finset.mul_sum]
  calc
    ∑ i ∈ Finset.range k, D * (ForestPeeling.peelSet D (rows i)).card <
        ∑ _i ∈ Finset.range k, 4 * Fintype.card A := by
      apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hk))
      intro i hi
      exact S.peel_card_lt G hG D i (rows i) (hrows i (Finset.mem_range.mp hi))
    _ = 4 * Fintype.card A * k := by simp [Nat.mul_comm]

/-- The real-valued total has precisely the paper's constant and handles all
positive numbers of completed phases. -/
theorem sum_peel_card_lt_div (hG : G.IsAcyclic) (D k : ℕ) (hD : 0 < D) (hk : 0 < k)
    [Nonempty A]
    (rows : ∀ i, ↥(S.remaining i : Set A) → Finset (S.remaining i : Set A))
    (hrows : ∀ i < k, ForestPeeling.ScreenContract (S.graph G i) D (rows i)) :
    ((∑ i ∈ Finset.range k, (ForestPeeling.peelSet D (rows i)).card) : ℝ) <
      4 * Fintype.card A * k / D := by
  apply (lt_div_iff₀ (show (0 : ℝ) < D by exact_mod_cast hD)).mpr
  have h := S.sum_peel_card_lt G hG D k hk rows hrows
  exact_mod_cast (by simpa [Nat.mul_comm] using h)

/-- A nonstrict total is valid for every prefix, including zero phases and
an empty ambient type. It is useful for a controller's uniform fuel invariant. -/
theorem sum_peel_card_le_div (hG : G.IsAcyclic) (D k : ℕ) (hD : 0 < D)
    (rows : ∀ i, ↥(S.remaining i : Set A) → Finset (S.remaining i : Set A))
    (hrows : ∀ i < k, ForestPeeling.ScreenContract (S.graph G i) D (rows i)) :
    ((∑ i ∈ Finset.range k, (ForestPeeling.peelSet D (rows i)).card) : ℝ) ≤
      4 * Fintype.card A * k / D := by
  classical
  rcases k with _ | k
  · simp
  cases isEmpty_or_nonempty A
  · simp [Finset.eq_empty_of_isEmpty]
  · exact (S.sum_peel_card_lt_div G hG D (k + 1) hD (by omega) rows hrows).le

/-- Combining the actual frozen peel sets with the centroid depth leaves
strict room before the hard guard, even for the generalized zero-phase case. -/
theorem peel_plus_centroid_lt_reserved (hG : G.IsAcyclic) (D : ℕ) (hD : 0 < D)
    (rows : ∀ i, ↥(S.remaining i : Set A) → Finset (S.remaining i : Set A))
    (hrows : ∀ i < phaseCap (Fintype.card A) D,
      ForestPeeling.ScreenContract (S.graph G i) D (rows i))
    (t : ℕ) (ht : t ≤ centroidDepth (Fintype.card A)) :
    (∑ i ∈ Finset.range (phaseCap (Fintype.card A) D),
      (ForestPeeling.peelSet D (rows i)).card) + t < hardRoundCap (Fintype.card A) D - 1 :=
  rounds_lt_reserved _ _ _ _ (by
    simpa only [Nat.cast_sum] using S.sum_peel_card_le_div G hG D _ hD rows hrows) ht

omit [Fintype A] [DecidableRel G.Adj] in
/-- Every component of the actual residual graph has a well-defined parent
through the inclusion embedding. Successful centroid deletion halves its size. -/
theorem centroid_component_halves (i : ℕ)
    (pick : (C : (S.graph G i).ConnectedComponent) → C)
    (hcent : ∀ C, ForestCentroid.IsCentroid C.toSimpleGraph (pick C))
    (havoid : ∀ v : (S.remaining (i + 1) : Set A),
      S.stepEmbedding G i v ∉ ForestCentroid.componentBatch (S.graph G i) pick)
    (C : (S.graph G (i + 1)).ConnectedComponent) :
    2 * Nat.card C ≤ Nat.card (C.map (S.stepEmbedding G i).toHom) :=
  component_halves_of_embedding (S.stepEmbedding G i) pick hcent havoid C

omit [DecidableRel G.Adj] in
/-- Iterating actual centroid deletions bounds each surviving component by
`N / 2^k`; the statement uses integer multiplication to retain strictness. -/
theorem centroid_component_bound (k : ℕ)
    (pick : ∀ i, (C : (S.graph G i).ConnectedComponent) → C)
    (hcent : ∀ i < k, ∀ C, ForestCentroid.IsCentroid C.toSimpleGraph (pick i C))
    (havoid : ∀ i < k, ∀ v : (S.remaining (i + 1) : Set A),
      S.stepEmbedding G i v ∉ ForestCentroid.componentBatch (S.graph G i) (pick i))
    (C : (S.graph G k).ConnectedComponent) :
    2 ^ k * Nat.card C ≤ Fintype.card A := by
  induction k with
  | zero =>
      simp only [pow_zero, one_mul]
      exact (Nat.card_le_card_of_injective (fun x : C ↦ x.1.1)
        (fun x y h ↦ Subtype.ext (Subtype.ext h))).trans_eq (Nat.card_eq_fintype_card)
  | succ k ih =>
      have hp := ih (fun i hi ↦ hcent i (by omega)) (fun i hi ↦ havoid i (by omega))
        (C.map (S.stepEmbedding G k).toHom)
      have hh := S.centroid_component_halves G k (pick k) (hcent k (by omega))
        (havoid k (by omega)) C
      calc
        2 ^ (k + 1) * Nat.card C = 2 ^ k * (2 * Nat.card C) := by rw [pow_succ]; ring
        _ ≤ 2 ^ k * Nat.card (C.map (S.stepEmbedding G k).toHom) := Nat.mul_le_mul_left _ hh
        _ ≤ Fintype.card A := hp

omit [DecidableRel G.Adj] in
/-- The exact public binary-logarithmic depth leaves the actual remaining
vertex set empty after successful component-centroid batches. -/
theorem remaining_empty_at_centroidDepth
    (pick : ∀ i, (C : (S.graph G i).ConnectedComponent) → C)
    (hcent : ∀ i < centroidDepth (Fintype.card A), ∀ C,
      ForestCentroid.IsCentroid C.toSimpleGraph (pick i C))
    (havoid : ∀ i < centroidDepth (Fintype.card A), ∀ v : (S.remaining (i + 1) : Set A),
      S.stepEmbedding G i v ∉ ForestCentroid.componentBatch (S.graph G i) (pick i)) :
    S.remaining (centroidDepth (Fintype.card A)) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  let w : (S.remaining (centroidDepth (Fintype.card A)) : Set A) := ⟨v, hv⟩
  let C := (S.graph G (centroidDepth (Fintype.card A))).connectedComponentMk w
  have hbound := S.centroid_component_bound G _ pick hcent havoid C
  let : Nonempty C := ⟨⟨C.nonempty_supp.choose, C.nonempty_supp.choose_spec⟩⟩
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hpow : 2 ^ centroidDepth (Fintype.card A) ≤
      2 ^ centroidDepth (Fintype.card A) * Nat.card C := Nat.le_mul_of_pos_right _ hpos
  exact (not_lt_of_ge (hpow.trans hbound)) (lt_two_pow_centroidDepth (Fintype.card A))

end DeletionSequence
end ForestSampling.ForestIteration
