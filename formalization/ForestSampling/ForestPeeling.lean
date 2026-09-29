import ForestSampling.ForestModel

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling.ForestPeeling

/-!
# Claim peeling on a finite forest

All degrees below are computed from the actual graph. The screen contract
requires exact low-degree rows and a cardinality cap on every other row.
-/

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
/-- A finite nonempty forest has degree sum strictly less than twice its
number of vertices. Extend it to a tree only to invoke the tree edge count. -/
theorem degree_sum_lt_twice_card (G : SimpleGraph A) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) [Nonempty A] :
    (∑ v, G.degree v) < 2 * Fintype.card A := by
  classical
  obtain ⟨T, hGT, _, hT⟩ :=
    (SimpleGraph.connected_top (V := A)).exists_isTree_le_of_le_of_isAcyclic
      (show G ≤ ⊤ from le_top) hG
  have hsum : (∑ v, G.degree v) ≤ ∑ v, T.degree v := by
    exact Finset.sum_le_sum (fun v _ ↦ G.degree_le_of_le hGT)
  have hcard := hT.card_edgeFinset
  have hdegrees := T.sum_degrees_eq_twice_card_edges
  omega

omit [DecidableEq A] in
/-- The nonstrict form also includes the empty forest. -/
theorem degree_sum_le_twice_card (G : SimpleGraph A) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) :
    (∑ v, G.degree v) ≤ 2 * Fintype.card A := by
  cases isEmpty_or_nonempty A
  · simp
  · exact (degree_sum_lt_twice_card G hG).le

variable (G : SimpleGraph A) [DecidableRel G.Adj]

/-- Degree inside a specified remaining vertex set. -/
def withinDegree (S : Finset A) (v : A) : ℕ := (G.neighborFinset v ∩ S).card

/-- The set-based degree is exactly the degree of the induced graph. -/
theorem degree_induce_eq_withinDegree (S : Finset A) (v : (S : Set A)) :
    (G.induce (S : Set A)).degree v = withinDegree G S v.1 := by
  have h := congrArg Finset.card (G.map_neighborFinset_induce (s := (S : Set A)) v)
  convert h using 1
  · rw [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree]
    simp only [← SimpleGraph.card_neighborSet_eq_degree]
    exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
  · simp [withinDegree]

/-- Deleting vertices cannot increase the degree of a remaining vertex. -/
theorem withinDegree_le_degree (S : Finset A) (v : A) :
    withinDegree G S v ≤ G.degree v :=
  Finset.card_le_card Finset.inter_subset_left

/-- The degree sum on an actual induced forest is at most twice its size. -/
theorem withinDegree_sum_le (hG : G.IsAcyclic) (S : Finset A) :
    (∑ v ∈ S, withinDegree G S v) ≤ 2 * S.card := by
  have h := degree_sum_le_twice_card (G.induce (S : Set A)) (hG.induce _)
  simp only [degree_induce_eq_withinDegree] at h
  rw [← Finset.sum_coe_sort]
  convert h using 1 <;> simp

/-- The strict degree sum bound on a nonempty induced forest. -/
theorem withinDegree_sum_lt (hG : G.IsAcyclic) (S : Finset A) (hS : S.Nonempty) :
    (∑ v ∈ S, withinDegree G S v) < 2 * S.card := by
  let : Nonempty (S : Set A) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have h := degree_sum_lt_twice_card (G.induce (S : Set A)) (hG.induce _)
  simp only [degree_induce_eq_withinDegree] at h
  rw [← Finset.sum_coe_sort]
  convert h using 1 <;> simp

/-- Vertices whose current degree exceeds the screen cutoff. -/
def highVertices (D : ℕ) : Finset A := Finset.univ.filter fun v ↦ D < G.degree v

omit [DecidableEq A] in
@[simp]
theorem mem_highVertices (D : ℕ) (v : A) : v ∈ highVertices G D ↔ D < G.degree v := by
  simp [highVertices]

/-- Vertices still exceeding the cutoff after deletion outside `S`. -/
def residualHigh (S : Finset A) (D : ℕ) : Finset A :=
  S.filter fun v ↦ D < withinDegree G S v

/-- A residual high-degree vertex was already high-degree before deletion. -/
theorem residualHigh_subset (S : Finset A) (D : ℕ) :
    residualHigh G S D ⊆ highVertices G D ∩ S := by
  intro v hv
  obtain ⟨hvS, hvD⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_inter.mpr ⟨(mem_highVertices G D v).mpr
    (hvD.trans_le (withinDegree_le_degree G S v)), hvS⟩

/-- The precise successful-screen information used by the peeling proof. -/
structure ScreenContract (D : ℕ) (rows : A → Finset A) : Prop where
  bounded : ∀ u, (rows u).card ≤ D
  exact_low : ∀ u, G.degree u ≤ D → rows u = G.neighborFinset u

variable {G}

omit [DecidableEq A] in
/-- Every successful returned row has size at most its true degree. -/
theorem ScreenContract.row_card_le_degree {D : ℕ} {rows : A → Finset A}
    (h : ScreenContract G D rows) (u : A) : (rows u).card ≤ G.degree u := by
  by_cases hu : G.degree u ≤ D
  · simp [h.exact_low u hu]
  · exact (h.bounded u).trans (Nat.le_of_lt (Nat.lt_of_not_ge hu))

/-- All vertices whose screen rows claim the given target. -/
def claimers (rows : A → Finset A) (v : A) : Finset A :=
  Finset.univ.filter fun u ↦ v ∈ rows u

/-- Observable incoming claim count. -/
def claimCount (rows : A → Finset A) (v : A) : ℕ := (claimers rows v).card

/-- The strict threshold `claims > D/2`, expressed without rounding. -/
def peelSet (D : ℕ) (rows : A → Finset A) : Finset A :=
  Finset.univ.filter fun v ↦ D < 2 * claimCount rows v

@[simp]
theorem mem_peelSet (D : ℕ) (rows : A → Finset A) (v : A) :
    v ∈ peelSet D rows ↔ D < 2 * claimCount rows v := by
  simp [peelSet]

/-- Low-degree neighbors all claim the vertex, regardless of what the
high-degree rows report. -/
theorem low_neighbors_subset_claimers {D : ℕ} {rows : A → Finset A}
    (h : ScreenContract G D rows) (v : A) :
    G.neighborFinset v \ highVertices G D ⊆ claimers rows v := by
  intro u hu
  obtain ⟨huN, huH⟩ := Finset.mem_sdiff.mp hu
  have huD : G.degree u ≤ D := Nat.le_of_not_gt (by simpa using huH)
  have hv : v ∈ rows u := by
    rw [h.exact_low u huD]
    exact (G.mem_neighborFinset u v).mpr (((G.mem_neighborFinset v u).mp huN).symm)
  simpa [claimers] using hv

/-- Any unpeeled high-degree vertex has more than `D/2` neighbors in the
current high-degree induced forest. -/
theorem survivor_high_degree {D : ℕ} {rows : A → Finset A}
    (h : ScreenContract G D rows) (v : A)
    (hvH : v ∈ highVertices G D) (hvP : v ∉ peelSet D rows) :
    D < 2 * withinDegree G (highVertices G D) v := by
  have hlow : (G.neighborFinset v \ highVertices G D).card ≤ claimCount rows v :=
    Finset.card_le_card (low_neighbors_subset_claimers h v)
  have hclaim : 2 * claimCount rows v ≤ D := by simpa using hvP
  have hdeg : D < G.degree v := (mem_highVertices G D v).mp hvH
  have hsplit := Finset.card_inter_add_card_sdiff (G.neighborFinset v) (highVertices G D)
  change _ + _ = G.degree v at hsplit
  unfold withinDegree
  omega

/-- Sum the per-survivor lower bounds inside the actual high-degree forest. -/
theorem survivor_count_mul_le_degree_sum {D : ℕ} {rows : A → Finset A}
    (h : ScreenContract G D rows) :
    D * (highVertices G D \ peelSet D rows).card ≤
      2 * ∑ v ∈ highVertices G D, withinDegree G (highVertices G D) v := by
  calc
    D * (highVertices G D \ peelSet D rows).card =
        ∑ v ∈ highVertices G D \ peelSet D rows, D := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ highVertices G D \ peelSet D rows,
        2 * withinDegree G (highVertices G D) v := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨hvH, hvP⟩ := Finset.mem_sdiff.mp hv
      exact (survivor_high_degree h v hvH hvP).le
    _ ≤ ∑ v ∈ highVertices G D, 2 * withinDegree G (highVertices G D) v :=
      Finset.sum_le_sum_of_subset Finset.sdiff_subset
    _ = 2 * ∑ v ∈ highVertices G D, withinDegree G (highVertices G D) v := by
      rw [Finset.mul_sum]

/-- Sharp strict contraction for a nonempty current high-degree set. -/
theorem survivor_count_contraction_lt (hG : G.IsAcyclic)
    {D : ℕ} {rows : A → Finset A} (h : ScreenContract G D rows)
    (hH : (highVertices G D).Nonempty) :
    D * (highVertices G D \ peelSet D rows).card <
      4 * (highVertices G D).card := by
  have hsum := survivor_count_mul_le_degree_sum h
  have hforest := withinDegree_sum_lt G hG (highVertices G D) hH
  omega

/-- The contraction inequality also includes an empty high-degree set. -/
theorem survivor_count_contraction (hG : G.IsAcyclic)
    {D : ℕ} {rows : A → Finset A} (h : ScreenContract G D rows) :
    D * (highVertices G D \ peelSet D rows).card ≤
      4 * (highVertices G D).card := by
  have hsum := survivor_count_mul_le_degree_sum h
  have hforest := withinDegree_sum_le G hG (highVertices G D)
  omega

/-- Every next-phase high-degree vertex is an unpeeled old high-degree vertex. -/
theorem next_high_subset_survivors (D : ℕ) (rows : A → Finset A) :
    residualHigh G (Finset.univ \ peelSet D rows) D ⊆
      highVertices G D \ peelSet D rows := by
  intro v hv
  obtain ⟨hvH, hvS⟩ := Finset.mem_inter.mp (residualHigh_subset G _ D hv)
  exact Finset.mem_sdiff.mpr ⟨hvH, (Finset.mem_sdiff.mp hvS).2⟩

/-- Actual next-phase degrees contract by `4/D` after deleting the peel set. -/
theorem next_high_contraction (hG : G.IsAcyclic)
    {D : ℕ} {rows : A → Finset A} (h : ScreenContract G D rows) :
    D * (residualHigh G (Finset.univ \ peelSet D rows) D).card ≤
      4 * (highVertices G D).card := by
  exact (Nat.mul_le_mul_left D (Finset.card_le_card (next_high_subset_survivors D rows))).trans
    (survivor_count_contraction hG h)

/-- The actual next-phase contraction is strict whenever an old high-degree
vertex exists. -/
theorem next_high_contraction_lt (hG : G.IsAcyclic)
    {D : ℕ} {rows : A → Finset A} (h : ScreenContract G D rows)
    (hH : (highVertices G D).Nonempty) :
    D * (residualHigh G (Finset.univ \ peelSet D rows) D).card <
      4 * (highVertices G D).card := by
  exact (Nat.mul_le_mul_left D (Finset.card_le_card (next_high_subset_survivors D rows))).trans_lt
    (survivor_count_contraction_lt hG h hH)

/-- An empty observable peel set certifies that all residual degrees are
within the cutoff. The manuscript's cutoff `D ≥ 9` is stronger than needed here. -/
theorem degree_le_of_peelSet_empty (hG : G.IsAcyclic)
    {D : ℕ} {rows : A → Finset A} (h : ScreenContract G D rows)
    (hD : 4 ≤ D) (hP : peelSet D rows = ∅) : ∀ v, G.degree v ≤ D := by
  intro v
  by_contra hv
  have hvH : v ∈ highVertices G D := (mem_highVertices G D v).mpr (Nat.lt_of_not_ge hv)
  have hcon := survivor_count_contraction_lt hG h ⟨v, hvH⟩
  simp only [hP, Finset.sdiff_empty] at hcon
  have hmul := Nat.mul_le_mul_right (highVertices G D).card hD
  omega

/-- At an empty peel set the successful screen is exact at every vertex. -/
theorem rows_exact_of_peelSet_empty (hG : G.IsAcyclic)
    {D : ℕ} {rows : A → Finset A} (h : ScreenContract G D rows)
    (hD : 4 ≤ D) (hP : peelSet D rows = ∅) :
    ∀ v, rows v = G.neighborFinset v :=
  fun v ↦ h.exact_low v (degree_le_of_peelSet_empty hG h hD hP v)

omit [DecidableEq A] in
/-- Count the initial high-degree vertices using their actual degrees. -/
theorem initial_high_count (hG : G.IsAcyclic) (D : ℕ) [Nonempty A] :
    (D + 1) * (highVertices G D).card < 2 * Fintype.card A := by
  have hsum : (D + 1) * (highVertices G D).card ≤ ∑ v, G.degree v := by
    calc
      (D + 1) * (highVertices G D).card = ∑ v ∈ highVertices G D, (D + 1) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ highVertices G D, G.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact (mem_highVertices G D v).mp hv
      _ ≤ ∑ v, G.degree v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  exact hsum.trans_lt (degree_sum_lt_twice_card G hG)

/-- Double-counting the directed claims counts precisely the row sizes. -/
theorem sum_claimCount (rows : A → Finset A) :
    (∑ v, claimCount rows v) = ∑ u, (rows u).card := by
  simp only [claimCount, claimers, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp

/-- Successful rows generate fewer than twice as many claims as vertices. -/
theorem sum_claimCount_lt (hG : G.IsAcyclic)
    {D : ℕ} {rows : A → Finset A} (h : ScreenContract G D rows) [Nonempty A] :
    (∑ v, claimCount rows v) < 2 * Fintype.card A := by
  rw [sum_claimCount]
  exact (Finset.sum_le_sum (fun v _ ↦ h.row_card_le_degree v)).trans_lt
    (degree_sum_lt_twice_card G hG)

/-- The number of singleton commits in one successful peel phase is strictly
less than `4 n / D`, with no static outdegree assumption. -/
theorem peelSet_card_bound (hG : G.IsAcyclic)
    {D : ℕ} {rows : A → Finset A} (h : ScreenContract G D rows) [Nonempty A] :
    D * (peelSet D rows).card < 4 * Fintype.card A := by
  have hsum : D * (peelSet D rows).card ≤ 2 * ∑ v, claimCount rows v := by
    calc
      D * (peelSet D rows).card = ∑ v ∈ peelSet D rows, D := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ peelSet D rows, 2 * claimCount rows v := by
        apply Finset.sum_le_sum
        intro v hv
        exact ((mem_peelSet D rows v).mp hv).le
      _ ≤ ∑ v, 2 * claimCount rows v :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = 2 * ∑ v, claimCount rows v := by rw [Finset.mul_sum]
  have hc := sum_claimCount_lt hG h
  omega

/-- Computing high degrees after deletion agrees exactly with computing them
on the induced graph and transporting vertices back to the original type. -/
theorem highVertices_induce_map (S : Finset A) (D : ℕ) :
    (highVertices (G.induce (S : Set A)) D).map (Function.Embedding.subtype (· ∈ S)) =
      residualHigh G S D := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    have huD := (mem_highVertices (G.induce (S : Set A)) D u).mp hu
    rw [degree_induce_eq_withinDegree] at huD
    exact Finset.mem_filter.mpr ⟨u.2, huD⟩
  · intro hv
    obtain ⟨hvS, hvD⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_map.mpr ⟨⟨v, hvS⟩, ?_, rfl⟩
    apply (mem_highVertices (G.induce (S : Set A)) D ⟨v, hvS⟩).mpr
    simpa only [degree_induce_eq_withinDegree] using hvD

/-- A cardinality bridge to the actual induced-graph vertex type. -/
theorem highVertices_induce_card (S : Finset A) (D : ℕ) :
    (highVertices (G.induce (S : Set A)) D).card = (residualHigh G S D).card := by
  rw [← highVertices_induce_map S D, Finset.card_map]

/-- Real-valued form of the sharp successful-path contraction. -/
theorem next_high_contraction_real (hG : G.IsAcyclic)
    {D : ℕ} {rows : A → Finset A} (h : ScreenContract G D rows) (hD : 0 < D) :
    ((residualHigh G (Finset.univ \ peelSet D rows) D).card : ℝ) ≤
      (4 / (D : ℝ)) * (highVertices G D).card := by
  have hnat := next_high_contraction hG h
  have hreal : (D : ℝ) * (residualHigh G (Finset.univ \ peelSet D rows) D).card ≤
      4 * (highVertices G D).card := by exact_mod_cast hnat
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  apply (mul_le_mul_iff_right₀ hDp).mp
  calc
    (D : ℝ) * (residualHigh G (Finset.univ \ peelSet D rows) D).card ≤
        4 * (highVertices G D).card := hreal
    _ = D * (4 / (D : ℝ) * (highVertices G D).card) := by field_simp

/-- The public `8/D` contraction is a direct relaxation of the proven sharp
bound, including the empty residual forest. -/
theorem next_high_contraction_public (hG : G.IsAcyclic)
    {D : ℕ} {rows : A → Finset A} (h : ScreenContract G D rows) (hD : 0 < D) :
    ((residualHigh G (Finset.univ \ peelSet D rows) D).card : ℝ) ≤
      (8 / (D : ℝ)) * (highVertices G D).card := by
  refine (next_high_contraction_real hG h hD).trans ?_
  gcongr
  norm_num

end ForestSampling.ForestPeeling
