import ForestSampling.PackedStructure
import ForestSampling.PackedFailure
import ForestSampling.PrefixSafeRepair

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.PackedLoopStructure

noncomputable section
attribute [local instance] Classical.propDecidable

open Program Program.PrefixRepair

variable {N repetitions : ℕ} {V Color : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]

/-- The row function actually returned by the standard screen under its
frozen oracle replies, including the real vote-score transcript. -/
def actualRows (O : FrozenOracle N V) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : Fin repetitions → Position N → Color) (q D : ℕ) (ε : ℝ)
    (j : ResidualVertex h) : Finset (ResidualVertex h) :=
  Screening.returnedRow O h B draft colors q D ε
    (PublicRowSelector.standardTopVotes
      (fun (scores : ResidualVertex h → ResidualVertex h → ℕ) j i ↦ scores j i))
    (fun j i ↦ (Finset.univ.filter (fun τ ↦ Screening.tableVote h B draft colors q ε
      (fun index ↦ O.readState (Screening.scheduledSubmission h B draft colors q index).state)
      τ i j)).card) j

omit [LinearOrder V] [Nonempty V] in
/-- Query collection preserves prefix safety precisely at the completed
actual-oracle reply table. -/
theorem safeBeforeStop_querySchedule {Index : Type*} [DecidableEq Index]
    (M : ForestModel N V) (O : FrozenOracle N V) {h : History N V}
    (queries : Index → Submission h) (todo : List Index) (replies : ReplyTable queries)
    (next : ReplyTable queries → Program N V h)
    (marked : ∀ table, PrefixRepair (next table) (next table)) :
    (querySchedule queries todo replies next marked).SafeBeforeStop M O ↔
      (marked (fillQueryReplies queries O todo replies)).SafeBeforeStop M O := by
  induction todo generalizing replies with
  | nil => rfl
  | cons i todo ih => exact ih _

omit [Nonempty V] in
/-- The concrete standard screen introduces no unsafe commit before its
continuation; its safety is exactly that of the actual returned rows. -/
theorem safeBeforeStop_markScreen (M : ForestModel N V) (O : FrozenOracle N V)
    (h : History N V) (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q D : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (marked : ∀ rows, PrefixRepair (next rows) (next rows))
    (hsafe : (marked (actualRows O h B draft colors q D ε)).SafeBeforeStop M O) :
    (PackedSampler.markScreen h B draft baseline repetitions q D ε colors next marked).SafeBeforeStop M O := by
  by_cases hempty : B.maxSize = 0
  · have hrows : actualRows O h B draft colors q D ε = fun _ ↦ ∅ := by
      funext j
      simp only [actualRows, Screening.returnedRow, if_pos hempty]
    rw [hrows] at hsafe
    simpa only [PackedSampler.markScreen, dif_pos hempty, safeBeforeStop_selfTransport,
      ] using hsafe
  · simp only [PackedSampler.markScreen, dif_neg hempty, safeBeforeStop_selfTransport,
      safeBeforeStop_querySchedule]
    rw [fillQueryReplies_eq (Screening.scheduledSubmission h B draft colors q) O
      Finset.univ.toList (fun i ↦ by simp)]
    have hrows : actualRows O h B draft colors q D ε = fun j ↦
        (PublicRowSelector.standardTopVotes
          (fun (scores : ResidualVertex h → ResidualVertex h → ℕ) j i ↦ scores j i)).choose j
          (Screening.tableCandidate h B draft colors q ε
            (fun index ↦ O.readState (Screening.scheduledSubmission h B draft colors q index).state) j)
          D (fun j i ↦ (Finset.univ.filter (fun τ ↦ Screening.tableVote h B draft colors q ε
            (fun index ↦ O.readState (Screening.scheduledSubmission h B draft colors q index).state)
            τ i j)).card) := by
      funext j
      simp only [actualRows, Screening.returnedRow, if_neg hempty, Screening.tableCandidate_oracle]
    rw [hrows] at hsafe
    exact hsafe

omit [LinearOrder V] [Nonempty V] in
/-- Frozen singleton peeling is safe before every continuation marker when
its current fuel covers the entire list. The continuation receives an exact
remaining-set identity and a bound on the fuel actually consumed. -/
theorem safeBeforeStop_markPeel (M : ForestModel N V) (O : FrozenOracle N V)
    (todo : List (Position N)) (extra : ℕ) (h : History N V)
    (after : (extra : ℕ) → (h : History N V) → Program N V h)
    (marked : ∀ extra h, PrefixRepair (after extra h) (after extra h))
    (hfuel : todo.length ≤ extra)
    (hafter : ∀ extra' h', extra ≤ extra' + todo.length →
      h'.uncommitted = h.uncommitted \ todo.toFinset →
      (marked extra' h').SafeBeforeStop M O) :
    (PackedSampler.markPeel todo extra h after marked).SafeBeforeStop M O := by
  induction todo generalizing extra h with
  | nil => exact hafter extra h (by simp) (by simp)
  | cons j todo ih =>
      by_cases hc : h.committed = Finset.univ
      · simp only [PackedSampler.markPeel, dif_pos hc, safeBeforeStop_selfTransport, SafeBeforeStop]
      · by_cases hj : j ∈ h.uncommitted
        · cases extra with
          | zero => simp at hfuel
          | succ extra =>
              simp only [PackedSampler.markPeel, dif_neg hc, dif_pos hj,
                safeBeforeStop_selfTransport, SafeBeforeStop]
              constructor
              · exact M.batchStructurallySafe_singleton h j _
              · intro z
                apply ih extra _ (by simpa using hfuel)
                intro extra' h' hf hs
                apply hafter extra' h' (by simp only [List.length_cons] at *; omega)
                rw [hs, History.appendBatch_uncommitted]
                ext v
                simp
                tauto
        · simp only [PackedSampler.markPeel, dif_neg hc, dif_neg hj, safeBeforeStop_selfTransport]
          apply ih extra h (by simp only [List.length_cons] at hfuel; omega)
          intro extra' h' hf hs
          apply hafter extra' h' (by simp only [List.length_cons]; omega)
          rw [hs]
          ext v
          simp only [Finset.mem_sdiff, List.toFinset_cons, Finset.mem_insert]
          constructor
          · rintro ⟨hv, ht⟩
            exact ⟨hv, fun he ↦ he.elim (fun heq ↦ hj (heq ▸ hv)) ht⟩
          · tauto

/-- Count the true high-degree vertices at an actual history. -/
def highCount (M : ForestModel N V) (h : History N V) (D : ℕ) : ℕ :=
  (ForestPeeling.highVertices (residualGraph M.graph h) D).card

/-- The frozen public peel list in exactly the order used by the sampler. -/
def peelList (h : History N V) (D : ℕ)
    (rows : ResidualVertex h → Finset (ResidualVertex h)) : List (Position N) :=
  ((ForestPeeling.peelSet D rows).map (Function.Embedding.subtype _)).sort (· ≤ ·)

omit [LinearOrder V] [Nonempty V] in
/-- Exact execution of a frozen list removes every selected public vertex,
so the true residual high-degree count contracts. -/
theorem highCount_after_peel (M : ForestModel N V) (h h' : History N V) (D : ℕ) (hD : 0 < D)
    (rows : ResidualVertex h → Finset (ResidualVertex h))
    (hrows : ForestPeeling.ScreenContract (residualGraph M.graph h) D rows)
    (hremaining : h'.uncommitted = h.uncommitted \ (peelList h D rows).toFinset) :
    (highCount M h' D : ℝ) ≤ (8 / (D : ℝ)) * highCount M h D := by
  let e : residualGraph M.graph h' ↪g residualGraph M.graph h :=
    M.graph.induceHomOfLE (fun _ hi ↦ by
      have hi' : _ ∈ h.uncommitted \ (peelList h D rows).toFinset := hremaining ▸ hi
      exact (Finset.mem_sdiff.mp hi').1)
  have havoid (v : ResidualVertex h') : e v ∉ ForestPeeling.peelSet D rows := by
    intro hv
    have hmem : v.1 ∈ (peelList h D rows).toFinset := by
      rw [peelList, Finset.sort_toFinset]
      exact Finset.mem_map.mpr ⟨e v, hv, rfl⟩
    have hnot : v.1 ∈ h.uncommitted \ (peelList h D rows).toFinset := by
      simpa only [hremaining] using v.2
    exact (Finset.mem_sdiff.mp hnot).2 hmem
  have hn := ForestIteration.high_card_after_peeling e (M.graph_acyclic.induce _) D rows hrows havoid
  have hr : (D : ℝ) * highCount M h' D ≤ 4 * highCount M h D := by exact_mod_cast hn
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  calc
    (highCount M h' D : ℝ) ≤ (4 * highCount M h D) / D := by
      apply (le_div_iff₀ hDp).mpr
      nlinarith
    _ ≤ (8 / (D : ℝ)) * highCount M h D := by
      rw [div_mul_eq_mul_div]
      gcongr
      norm_num

omit [LinearOrder V] [Nonempty V] in
/-- On a noncomplete history a successful frozen list uses fewer than the
paper's per-phase singleton-round allowance. -/
theorem peelList_length_lt (M : ForestModel N V) (h : History N V) (D : ℕ) (hD : 0 < D)
    (hc : h.committed ≠ Finset.univ)
    (rows : ResidualVertex h → Finset (ResidualVertex h))
    (hrows : ForestPeeling.ScreenContract (residualGraph M.graph h) D rows) :
    ((peelList h D rows).length : ℝ) < 4 * (N : ℝ) / D := by
  obtain ⟨v, hv⟩ := h.uncommitted_nonempty_of_not_complete hc
  let : Nonempty (ResidualVertex h) := ⟨⟨v, hv⟩⟩
  have hs := ForestPeeling.peelSet_card_bound (M.graph_acyclic.induce _) hrows
  have hcard : Fintype.card (ResidualVertex h) ≤ N := by
    simpa using Fintype.card_le_of_injective (fun x : ResidualVertex h ↦ x.1) Subtype.val_injective
  have hn := hs.trans_le (Nat.mul_le_mul_left 4 hcard)
  rw [peelList, Finset.length_sort, Finset.card_map]
  apply (lt_div_iff₀ (show (0 : ℝ) < D by exact_mod_cast hD)).mpr
  exact_mod_cast (by simpa [Nat.mul_comm] using hn)

omit [LinearOrder V] [Nonempty V] in
/-- The initial high-degree estimate follows from the real forest degree
sum, for any history at which the loop begins. -/
theorem initial_highCount_lt (M : ForestModel N V) (h : History N V) (D : ℕ) (hN : 0 < N) :
    (highCount M h D : ℝ) < 2 * (N : ℝ) / (D + 1) := by
  cases isEmpty_or_nonempty (ResidualVertex h)
  · have hz : highCount M h D = 0 := by simp [highCount, ForestPeeling.highVertices]
    rw [hz, Nat.cast_zero]
    positivity
  · have hs := ForestPeeling.initial_high_count (G := residualGraph M.graph h)
      (M.graph_acyclic.induce _) D
    have hc : Fintype.card (ResidualVertex h) ≤ N := by
      simpa using Fintype.card_le_of_injective (fun x : ResidualVertex h ↦ x.1) Subtype.val_injective
    have hn := hs.trans_le (Nat.mul_le_mul_left 2 hc)
    apply (lt_div_iff₀ (show (0 : ℝ) < D + 1 by positivity)).mpr
    have hr : ((D : ℝ) + 1) * highCount M h D < 2 * N := by exact_mod_cast hn
    nlinarith

omit [LinearOrder V] [Nonempty V] in
/-- Under the exact geometric invariant, reaching the completed-phase cap
makes every actual degree small enough for the last screen to be exact. -/
theorem rows_exact_at_cap (M : ForestModel N V) (h : History N V) (D : ℕ)
    (hN : 0 < N) (hD : 9 ≤ D)
    (rows : ResidualVertex h → Finset (ResidualVertex h))
    (hrows : ForestPeeling.ScreenContract (residualGraph M.graph h) D rows)
    (hhigh : (highCount M h D : ℝ) <
      (8 / (D : ℝ)) ^ ForestIteration.phaseCap N D * (2 * (N : ℝ) / (D + 1))) :
    ∀ j, rows j = (residualGraph M.graph h).neighborFinset j := by
  have hlt := hhigh.trans_le (ForestIteration.phaseCap_geometric N D hN hD)
  have hzero : highCount M h D = 0 := by
    have hn : highCount M h D < 1 := by exact_mod_cast hlt
    omega
  intro j
  apply hrows.exact_low
  by_contra hnot
  have hm := (ForestPeeling.mem_highVertices (residualGraph M.graph h) D j).mpr (Nat.lt_of_not_ge hnot)
  have he : ForestPeeling.highVertices (residualGraph M.graph h) D = ∅ := Finset.card_eq_zero.mp hzero
  simp [he] at hm

omit [Nonempty V] in
/-- The actual marked packed loop is safe up to its first failed screen.
The induction maintains actual high-degree counts and the remaining real
round allowance; it needs no assumption about future successful completions. -/
theorem markLoop_safeBeforeStop (M : ForestModel N V) (O : FrozenOracle N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q D : ℕ) (ε : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D)
    (hscreen : ∀ (h : History N V) (colors : Fin repetitions → Position N → Color),
      Screening.ScreenSuccess M h colors D →
      ForestPeeling.ScreenContract (residualGraph M.graph h) D (actualRows O h B draft colors q D ε))
    (phases : ℕ) (blocks : PackedSampler.ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions)
    (extra : ℕ) (h : History N V)
    (hphase : phases ≤ ForestIteration.phaseCap N D)
    (hfuel : 4 * (N : ℝ) * phases / D + ForestIteration.centroidDepth N ≤ extra)
    (hhigh : (highCount M h D : ℝ) <
      (8 / (D : ℝ)) ^ (ForestIteration.phaseCap N D - phases) * (2 * (N : ℝ) / (D + 1))) :
    (PackedSampler.markLoop M B draft baseline repetitions q D ε phases blocks extra h).SafeBeforeStop M O := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hratio : 0 < 8 / (D : ℝ) := by positivity
  induction phases generalizing extra h with
  | zero =>
      by_cases hc : h.committed = Finset.univ
      · simp only [PackedSampler.markLoop, dif_pos hc, safeBeforeStop_selfTransport, SafeBeforeStop]
      · by_cases hgood : Screening.ScreenSuccess M h (blocks 0) D
        · simp only [PackedSampler.markLoop, dif_neg hc, dif_pos hgood, safeBeforeStop_selfTransport]
          apply safeBeforeStop_markScreen
          rw [safeBeforeStop_unmarked]
          apply PackedStructure.terminal_structurallySafe_of_depth M O _ extra h
          · apply PackedStructure.residual_rowGraph_eq M.graph h _
            exact rows_exact_at_cap M h D hN hD _ (hscreen h (blocks 0) hgood) (by simpa using hhigh)
          · exact_mod_cast (by simpa using hfuel : (ForestIteration.centroidDepth N : ℝ) ≤ extra)
        · simp only [PackedSampler.markLoop, dif_neg hc, dif_neg hgood, SafeBeforeStop]
  | succ phases ih =>
      by_cases hc : h.committed = Finset.univ
      · simp only [PackedSampler.markLoop, dif_pos hc, safeBeforeStop_selfTransport, SafeBeforeStop]
      · by_cases hgood : Screening.ScreenSuccess M h (blocks 0) D
        · simp only [PackedSampler.markLoop, dif_neg hc, dif_pos hgood, safeBeforeStop_selfTransport]
          apply safeBeforeStop_markScreen
          let rows := actualRows O h B draft (blocks 0) q D ε
          have hrows : ForestPeeling.ScreenContract (residualGraph M.graph h) D rows := hscreen h _ hgood
          have hdepth : ForestIteration.centroidDepth N ≤ extra := by
            have hn : 0 ≤ 4 * (N : ℝ) * (phases + 1 : ℕ) / D := by positivity
            exact_mod_cast (by linarith : (ForestIteration.centroidDepth N : ℝ) ≤ extra)
          by_cases hp : ForestPeeling.peelSet D rows = ∅
          · dsimp only [rows] at hp
            simp only [dif_pos hp, safeBeforeStop_selfTransport, safeBeforeStop_unmarked]
            exact PackedStructure.terminal_structurallySafe_of_depth M O _ extra h
              (PackedStructure.residual_rowGraph_eq_of_empty_peel M h D (by omega) rows hrows hp) hdepth
          · dsimp only [rows] at hp
            simp only [dif_neg hp, safeBeforeStop_selfTransport]
            have hlength := peelList_length_lt M h D (by omega) hc rows hrows
            have hlistfuel : (peelList h D rows).length ≤ extra := by
              have hper : 4 * (N : ℝ) / D ≤ 4 * (N : ℝ) * (phases + 1 : ℕ) / D := by
                apply div_le_div_of_nonneg_right _ hDp.le
                have hp : (1 : ℝ) ≤ (phases + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 phases
                simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 4 * N by positivity)
              have ht : ((peelList h D rows).length : ℝ) < extra := by
                have hd : (0 : ℝ) ≤ ForestIteration.centroidDepth N := by positivity
                linarith
              exact_mod_cast ht.le
            apply safeBeforeStop_markPeel M O (peelList h D rows) extra h _ _ hlistfuel
            intro extra' h' hcost hremaining
            apply ih (fun call ↦ blocks call.succ) extra' h' (by omega)
            · have hcostR : (extra : ℝ) ≤ extra' + (peelList h D rows).length := by exact_mod_cast hcost
              have heq : 4 * (N : ℝ) * (phases + 1 : ℕ) / D =
                  4 * (N : ℝ) * phases / D + 4 * (N : ℝ) / D := by push_cast; ring
              rw [heq] at hfuel
              linarith
            · have hnext := highCount_after_peel M h h' D (by omega) rows hrows hremaining
              have hpow : ForestIteration.phaseCap N D - phases =
                  (ForestIteration.phaseCap N D - (phases + 1)) + 1 := by omega
              calc
                (highCount M h' D : ℝ) ≤ (8 / (D : ℝ)) * highCount M h D := hnext
                _ < (8 / (D : ℝ)) * ((8 / (D : ℝ)) ^
                    (ForestIteration.phaseCap N D - (phases + 1)) * (2 * (N : ℝ) / (D + 1))) :=
                  mul_lt_mul_of_pos_left hhigh hratio
                _ = (8 / (D : ℝ)) ^ (ForestIteration.phaseCap N D - phases) *
                    (2 * (N : ℝ) / (D + 1)) := by rw [hpow, pow_succ]; ring
        · simp only [PackedSampler.markLoop, dif_neg hc, dif_neg hgood, SafeBeforeStop]

omit [Nonempty V] in
/-- The exact public initial phase and hard-round caps satisfy the invariant
used by the concrete marked-loop induction. -/
theorem initial_markLoop_safeBeforeStop (M : ForestModel N V) (O : FrozenOracle N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q D : ℕ) (ε : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D)
    (hscreen : ∀ (h : History N V) (colors : Fin repetitions → Position N → Color),
      Screening.ScreenSuccess M h colors D →
      ForestPeeling.ScreenContract (residualGraph M.graph h) D (actualRows O h B draft colors q D ε))
    (blocks : PackedSampler.ColorBlocks (N := N) (Color := Color)
      (ForestIteration.phaseCap N D + 1) repetitions) (h : History N V) :
    (PackedSampler.markLoop M B draft baseline repetitions q D ε (ForestIteration.phaseCap N D)
      blocks (ForestIteration.hardRoundCap N D - 1) h).SafeBeforeStop M O := by
  apply markLoop_safeBeforeStop M O B draft baseline repetitions q D ε hN hD hscreen
    _ blocks _ h le_rfl
  · have hc := Nat.le_ceil (4 * (N : ℝ) * ForestIteration.phaseCap N D / D)
    unfold ForestIteration.hardRoundCap
    rw [show ⌈4 * (N : ℝ) * ForestIteration.phaseCap N D / D⌉₊ +
        ForestIteration.centroidDepth N + 2 - 1 =
      ⌈4 * (N : ℝ) * ForestIteration.phaseCap N D / D⌉₊ +
        ForestIteration.centroidDepth N + 1 by omega]
    push_cast
    linarith
  · simpa using initial_highCount_lt M h D hN

omit [Fintype Color] in
/-- The actual standard row function satisfies the screen contract from
exactly the manuscript's model, oracle, feasibility, and margin assumptions. -/
theorem actualRows_screenContract (M : ForestModel N V) (O : FrozenOracle N V)
    (h : History N V) (draft : Position N → V)
    (colors : Fin repetitions → Position N → Color) (q D : ℕ)
    (C s t ε ν signal : ℝ)
    (hfloor : (Fintype.card V : ℝ)⁻¹ < t - ε)
    (hε : 0 ≤ ε) (hν : 0 ≤ ν) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * t ^ s) ≤ ν) (hmargin : 4 * ε + ν < signal)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ ε)
    (hsuccess : Screening.ScreenSuccess M h colors D) :
    ForestPeeling.ScreenContract (residualGraph M.graph h) D
      (actualRows O h (Screening.Banks.ofOracle O t ε hfloor) draft colors q D ε) :=
  PackedStructure.screenContract_of_returnedRow M O h draft colors q D C s t ε ν signal
    hfloor hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows hsuccess _ _

/-- With the public caps and the stated model/oracle assumptions, every
seed of the actual sampler is structurally safe before its first failed
screen. No abstract safety, recurrence, or successful-row hypothesis remains. -/
theorem samplerMarker_safeBeforeStop (P : PackedSampler.Parameters N V)
    (M : ForestModel N V) (O : FrozenOracle N V) (C s ν signal : ℝ)
    (hN : 0 < N) (hD : 9 ≤ P.cutoff)
    (hphases : P.phases = ForestIteration.phaseCap N P.cutoff)
    (hextra : P.extraRounds = ForestIteration.hardRoundCap N P.cutoff - 1)
    (hε : 0 ≤ P.rowError) (hν : 0 ≤ ν) (ht0 : 0 ≤ P.threshold) (ht1 : P.threshold ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * P.threshold ^ s) ≤ ν) (hmargin : 4 * P.rowError + ν < signal)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ P.rowError)
    (blocks : PackedSampler.ColorBlocks (N := N) (Color := Color) (P.phases + 1) P.repetitions) :
    (PackedSampler.samplerMarker P M O blocks).SafeBeforeStop M O := by
  rcases P with ⟨q, hq, D, phases, extra, repetitions, t, ε, hfloor⟩
  dsimp only at hD hphases hextra hε ht0 ht1 hfeasible hmargin hrows blocks ⊢
  subst phases
  subst extra
  unfold PackedSampler.samplerMarker
  apply initial_markLoop_safeBeforeStop M O _ _ _ repetitions q D ε hN hD
  intro h colors hsuccess
  rw [PackedSampler.initialBanks_oracle]
  exact actualRows_screenContract M O h _ colors q D C s t ε ν signal
    hfloor hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows hsuccess

end
end ForestSampling.PackedLoopStructure
