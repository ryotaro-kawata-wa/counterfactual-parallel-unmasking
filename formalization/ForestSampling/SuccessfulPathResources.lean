import ForestSampling.PackedLoopStructure
import ForestSampling.PackedPathDepth
import ForestSampling.OracleBudgets

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace ForestSampling
namespace Program.PrefixRepair
variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A round allowance required only until a failed-screen marker.
The induced path theorem applies to complete paths with no failed screen. -/
def GoodWithinRounds (O : FrozenOracle N V) :
    {h : History N V} → {left right : Program N V h} → PrefixRepair left right → ℕ → Prop
  | _, _, _, .stop _ _, _ => True
  | _, _, _, .done _, _ => True
  | _, _, _, .query state _ _ _ next, R => GoodWithinRounds O (next (O.readState state)) R
  | _, _, _, .commit _ _ _ _ _ next, R => 0 < R ∧ ∀ z, GoodWithinRounds O (next z) (R-1)

theorem GoodWithinRounds.mono (O : FrozenOracle N V) {h : History N V}
    {left right : Program N V h} (marker : PrefixRepair left right) {R S : ℕ}
    (hb : marker.GoodWithinRounds O R) (hrs : R ≤ S) : marker.GoodWithinRounds O S := by
  induction marker generalizing R S with
  | stop left right => trivial
  | done complete => trivial
  | query state respects left right next ih => exact ih _ hb hrs
  | commit batch nonempty fresh left right next ih =>
      exact ⟨by exact lt_of_lt_of_le hb.1 hrs, fun z ↦ ih z (hb.2 z) (by omega)⟩

theorem GoodWithinRounds.retainedRoundCount_le (O : FrozenOracle N V) {h : History N V}
    {left right : Program N V h} (marker : PrefixRepair left right) (R : ℕ)
    (hb : marker.GoodWithinRounds O R) (path : Program.RetainedPath O left)
    (hgood : ¬ marker.HitsRepair O path) : Program.retainedRoundCount O left path ≤ R := by
  induction marker generalizing R with
  | stop left right => exact (hgood trivial).elim
  | done complete => exact Nat.zero_le _
  | query state respects left right next ih => exact ih _ R hb path hgood
  | commit batch nonempty fresh left right next ih =>
      have hh := ih path.1 (R-1) (hb.2 path.1) path.2 hgood
      have hp : 0 < R := hb.1
      change 1 + Program.retainedRoundCount O (left path.1) path.2 ≤ R
      omega

@[simp] theorem goodWithinRounds_selfTransport (O : FrozenOracle N V) {h : History N V}
    {p q : Program N V h} (heq : p = q) (marked : PrefixRepair q q) (R : ℕ) :
    (selfTransport heq marked).GoodWithinRounds O R = marked.GoodWithinRounds O R := by
  cases heq
  rfl

theorem goodWithinRounds_unmarked (O : FrozenOracle N V) {h : History N V}
    (p : Program N V h) (Q R : ℕ) (hb : p.WithinOracleBudgets O Q R) :
    (unmarked p).GoodWithinRounds O R := by
  induction p generalizing Q R with
  | done complete => trivial
  | query state respects next ih => exact ih _ (Q-1) R hb.2
  | commit batch nonempty fresh next ih => exact ⟨hb.1, fun z ↦ ih z Q (R-1) (hb.2 z)⟩

/-- Query collection itself consumes no commit rounds. -/
theorem goodWithinRounds_querySchedule {Index : Type*} [DecidableEq Index]
    (O : FrozenOracle N V) {h : History N V}
    (queries : Index → Submission h) (todo : List Index) (replies : Program.ReplyTable queries)
    (next : Program.ReplyTable queries → Program N V h)
    (marked : ∀ table, PrefixRepair (next table) (next table)) (R : ℕ) :
    (querySchedule queries todo replies next marked).GoodWithinRounds O R ↔
      (marked (Program.fillQueryReplies queries O todo replies)).GoodWithinRounds O R := by
  induction todo generalizing replies with
  | nil => rfl
  | cons i todo ih => exact ih _

end Program.PrefixRepair
namespace SuccessfulPathResources
variable {N : ℕ} {V Color : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]
open Program Program.PrefixRepair PackedLoopStructure

/-- A correct terminal graph completes within its actual halving depth,
independently of how much larger the reserved hard fuel is. -/
theorem terminal_withinDepth (M : ForestModel N V) (O : FrozenOracle N V)
    (G : SimpleGraph (Position N)) (depth extra : ℕ) (h : History N V)
    (heq : residualGraph G h = residualGraph M.graph h)
    (hfuel : depth ≤ extra)
    (hbound : ∀ C : (residualGraph G h).ConnectedComponent, Nat.card C < 2^depth) :
    (CappedController.terminal extra h G).WithinOracleBudgets O 0 depth := by
  induction depth generalizing extra h with
  | zero =>
      have hc := PackedStructure.complete_of_components_lt_one G h (by simpa using hbound)
      simp [CappedController.terminal, hc, WithinOracleBudgets]
  | succ depth ih =>
      cases extra with
      | zero => omega
      | succ extra =>
          rw [CappedController.terminal]
          split
          · trivial
          · rename_i hc
            refine ⟨by omega, ?_⟩
            intro z
            apply ih extra _ (PackedStructure.residual_eq_append G M.graph h heq _ _ z) (by omega)
            intro C
            have hh := PackedStructure.terminalBatch_halves G h (heq ▸ M.graph_acyclic.induce _) _ z C
            have hp := hbound (C.map (PackedStructure.appendEmbedding G h _ _ z).toHom)
            have hlt := hh.trans_lt hp
            rw [pow_succ] at hlt
            omega

/-- The global public logarithmic depth bounds the concrete terminal rounds. -/
theorem terminal_withinCentroidDepth (M : ForestModel N V) (O : FrozenOracle N V)
    (G : SimpleGraph (Position N)) (extra : ℕ) (h : History N V)
    (heq : residualGraph G h = residualGraph M.graph h)
    (hfuel : ForestIteration.centroidDepth N ≤ extra) :
    (CappedController.terminal extra h G).WithinOracleBudgets O 0 (ForestIteration.centroidDepth N) := by
  apply terminal_withinDepth M O G _ extra h heq hfuel
  intro C
  have hc : Nat.card C ≤ N := by
    have hi := Nat.card_le_card_of_injective (fun x : C ↦ x.1.1)
      (fun x y hxy ↦ Subtype.ext (Subtype.ext hxy))
    simpa using hi
  exact hc.trans_lt (ForestIteration.lt_two_pow_centroidDepth N)

/-- Screening queries preserve the successful-path round allowance. -/
theorem goodWithinRounds_markScreen (O : FrozenOracle N V)
    (h : History N V) (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q D : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (marked : ∀ rows, PrefixRepair (next rows) (next rows))
    (R : ℕ) (hsafe : (marked (actualRows O h B draft colors q D ε)).GoodWithinRounds O R) :
    (PackedSampler.markScreen h B draft baseline repetitions q D ε colors next marked).GoodWithinRounds O R := by
  by_cases hempty : B.maxSize = 0
  · have hrows : actualRows O h B draft colors q D ε = fun _ ↦ ∅ := by
      funext j
      simp only [actualRows, Screening.returnedRow, if_pos hempty]
    rw [hrows] at hsafe
    simpa only [PackedSampler.markScreen, dif_pos hempty, goodWithinRounds_selfTransport,
      ] using hsafe
  · simp only [PackedSampler.markScreen, dif_neg hempty, goodWithinRounds_selfTransport,
      goodWithinRounds_querySchedule]
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

/-- Frozen peeling uses at most one round per listed vertex before its
continuation. The proof retains the actual fuel and remaining-set relation. -/
theorem goodWithinRounds_markPeel (O : FrozenOracle N V)
    (todo : List (Position N)) (extra : ℕ) (h : History N V)
    (after : (extra : ℕ) → (h : History N V) → Program N V h)
    (marked : ∀ extra h, PrefixRepair (after extra h) (after extra h))
    (R : ℕ) (hfuel : todo.length ≤ extra)
    (hafter : ∀ extra' h', extra ≤ extra' + todo.length →
      h'.uncommitted = h.uncommitted \ todo.toFinset →
      (marked extra' h').GoodWithinRounds O R) :
    (PackedSampler.markPeel todo extra h after marked).GoodWithinRounds O (todo.length+R) := by
  induction todo generalizing extra h with
  | nil => simpa only [PackedSampler.markPeel, CappedController.peelPass, List.length_nil, Nat.zero_add] using hafter extra h (by simp) (by simp)
  | cons j todo ih =>
      by_cases hc : h.committed = Finset.univ
      · simp only [PackedSampler.markPeel, dif_pos hc, goodWithinRounds_selfTransport, GoodWithinRounds]
      · by_cases hj : j ∈ h.uncommitted
        · cases extra with
          | zero => simp at hfuel
          | succ extra =>
              simp only [PackedSampler.markPeel, dif_neg hc, dif_pos hj,
                goodWithinRounds_selfTransport, GoodWithinRounds]
              refine ⟨by simp, ?_⟩
              intro z
              rw [show (j :: todo).length + R - 1 = todo.length + R by simp]
              apply ih extra _ (by simpa using hfuel)
              intro extra' h' hf hs
              apply hafter extra' h' (by simp only [List.length_cons] at *; omega)
              rw [hs, History.appendBatch_uncommitted]
              ext v
              simp
              tauto
        · simp only [PackedSampler.markPeel, dif_neg hc, dif_neg hj, goodWithinRounds_selfTransport]
          apply GoodWithinRounds.mono O _ (R := todo.length+R) _ (by simp)
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

/-- A uniform integer upper bound strictly below the real per-phase bound. -/
noncomputable def peelAllowance (N D : ℕ) : ℕ := ⌈4*(N : ℝ)/D⌉₊-1

theorem peelAllowance_lt (N D : ℕ) (hN : 0 < N) (hD : 0 < D) :
    (peelAllowance N D : ℝ) < 4*(N : ℝ)/D := by
  have hx : 0 < 4*(N : ℝ)/D := by positivity
  have hc : 0 < ⌈4*(N : ℝ)/D⌉₊ := Nat.ceil_pos.mpr hx
  have hb := Nat.ceil_lt_add_one hx.le
  unfold peelAllowance
  rw [Nat.cast_sub (by omega)]
  push_cast
  linarith

theorem peelList_length_le_allowance (M : ForestModel N V) (h : History N V) (D : ℕ)
    (hD : 0 < D) (hc : h.committed ≠ Finset.univ)
    (rows : ResidualVertex h → Finset (ResidualVertex h))
    (hrows : ForestPeeling.ScreenContract (residualGraph M.graph h) D rows) :
    (peelList h D rows).length ≤ peelAllowance N D := by
  have hh := peelList_length_lt M h D hD hc rows hrows
  have hb : (peelList h D rows).length < ⌈4*(N : ℝ)/D⌉₊ := Nat.lt_ceil.mpr hh
  unfold peelAllowance
  omega

/-- Every actual successful prefix preserves a per-phase integer allowance
strictly below 4N/D, plus the actual centroid-depth allowance. -/
theorem markLoop_goodWithinRounds (M : ForestModel N V) (O : FrozenOracle N V)
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
    (PackedSampler.markLoop M B draft baseline repetitions q D ε phases blocks extra h).GoodWithinRounds O
      (peelAllowance N D * phases + ForestIteration.centroidDepth N) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hratio : 0 < 8 / (D : ℝ) := by positivity
  induction phases generalizing extra h with
  | zero =>
      by_cases hc : h.committed = Finset.univ
      · simp only [PackedSampler.markLoop, dif_pos hc, goodWithinRounds_selfTransport, GoodWithinRounds]
      · by_cases hgood : Screening.ScreenSuccess M h (blocks 0) D
        · simp only [PackedSampler.markLoop, dif_neg hc, dif_pos hgood, goodWithinRounds_selfTransport]
          apply goodWithinRounds_markScreen
          simp only [Nat.mul_zero, Nat.zero_add]
          apply goodWithinRounds_unmarked O _ 0 _
          apply terminal_withinCentroidDepth M O _ extra h
          · apply PackedStructure.residual_rowGraph_eq M.graph h _
            exact rows_exact_at_cap M h D hN hD _ (hscreen h (blocks 0) hgood) (by simpa using hhigh)
          · exact_mod_cast (by simpa using hfuel : (ForestIteration.centroidDepth N : ℝ) ≤ extra)
        · simp only [PackedSampler.markLoop, dif_neg hc, dif_neg hgood, GoodWithinRounds]
  | succ phases ih =>
      by_cases hc : h.committed = Finset.univ
      · simp only [PackedSampler.markLoop, dif_pos hc, goodWithinRounds_selfTransport, GoodWithinRounds]
      · by_cases hgood : Screening.ScreenSuccess M h (blocks 0) D
        · simp only [PackedSampler.markLoop, dif_neg hc, dif_pos hgood, goodWithinRounds_selfTransport]
          apply goodWithinRounds_markScreen
          let rows := actualRows O h B draft (blocks 0) q D ε
          have hrows : ForestPeeling.ScreenContract (residualGraph M.graph h) D rows := hscreen h _ hgood
          have hdepth : ForestIteration.centroidDepth N ≤ extra := by
            have hn : 0 ≤ 4 * (N : ℝ) * (phases + 1 : ℕ) / D := by positivity
            exact_mod_cast (by linarith : (ForestIteration.centroidDepth N : ℝ) ≤ extra)
          by_cases hp : ForestPeeling.peelSet D rows = ∅
          · dsimp only [rows] at hp
            simp only [dif_pos hp, goodWithinRounds_selfTransport]
            apply GoodWithinRounds.mono O _ (R := ForestIteration.centroidDepth N) _ (Nat.le_add_left _ _)
            apply goodWithinRounds_unmarked O _ 0 _
            exact terminal_withinCentroidDepth M O _ extra h
              (PackedStructure.residual_rowGraph_eq_of_empty_peel M h D (by omega) rows hrows hp) hdepth
          · dsimp only [rows] at hp
            simp only [dif_neg hp, goodWithinRounds_selfTransport]
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
            have hcap := peelList_length_le_allowance M h D (by omega) hc rows hrows
            apply GoodWithinRounds.mono O _
              (R := (peelList h D rows).length + (peelAllowance N D * phases + ForestIteration.centroidDepth N)) _
              (by rw [Nat.mul_succ]; omega)
            apply goodWithinRounds_markPeel O (peelList h D rows) extra h _ _ _ hlistfuel
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
        · simp only [PackedSampler.markLoop, dif_neg hc, dif_neg hgood, GoodWithinRounds]

/-- The public fuel meets the successful-path round invariant. -/
theorem initial_markLoop_goodWithinRounds (M : ForestModel N V) (O : FrozenOracle N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q D : ℕ) (ε : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D)
    (hscreen : ∀ (h : History N V) (colors : Fin repetitions → Position N → Color),
      Screening.ScreenSuccess M h colors D →
      ForestPeeling.ScreenContract (residualGraph M.graph h) D (actualRows O h B draft colors q D ε))
    (blocks : PackedSampler.ColorBlocks (N := N) (Color := Color)
      (ForestIteration.phaseCap N D + 1) repetitions) (h : History N V) :
    (PackedSampler.markLoop M B draft baseline repetitions q D ε (ForestIteration.phaseCap N D)
      blocks (ForestIteration.hardRoundCap N D - 1) h).GoodWithinRounds O
      (peelAllowance N D * ForestIteration.phaseCap N D + ForestIteration.centroidDepth N) := by
  apply markLoop_goodWithinRounds M O B draft baseline repetitions q D ε hN hD hscreen
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

/-- The full finite hypotheses give an actual marker-aware round budget. -/
theorem samplerMarker_goodWithinRounds (P : PackedSampler.Parameters N V)
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
    (PackedSampler.samplerMarker P M O blocks).GoodWithinRounds O
      (peelAllowance N P.cutoff * ForestIteration.phaseCap N P.cutoff + ForestIteration.centroidDepth N) := by
  rcases P with ⟨q, hq, D, phases, extra, repetitions, t, ε, hfloor⟩
  dsimp only at hD hphases hextra hε ht0 ht1 hfeasible hmargin hrows blocks ⊢
  subst phases
  subst extra
  unfold PackedSampler.samplerMarker
  apply initial_markLoop_goodWithinRounds M O _ _ _ repetitions q D ε hN hD
  intro h colors hsuccess
  rw [PackedSampler.initialBanks_oracle]
  exact actualRows_screenContract M O h _ colors q D C s t ε ν signal
    hfloor hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows hsuccess

/-- The sharper successful-path inequality is about the actual retained
round count of the concrete sampler, not an abstract peel-sequence proxy. -/
theorem sampler_successful_rounds_lt (P : PackedSampler.Parameters N V)
    (M : ForestModel N V) (O : FrozenOracle N V) (C s ν signal : ℝ)
    (hN : 0 < N) (hD : 9 ≤ P.cutoff) (hDN : P.cutoff ≤ N-1)
    (hphases : P.phases = ForestIteration.phaseCap N P.cutoff)
    (hextra : P.extraRounds = ForestIteration.hardRoundCap N P.cutoff - 1)
    (hε : 0 ≤ P.rowError) (hν : 0 ≤ ν) (ht0 : 0 ≤ P.threshold) (ht1 : P.threshold ≤ 1)
    (hRT : M.TailResponseRegular C s) (hUEN : M.EdgeNondegenerate signal)
    (hfeasible : min 1 (C * P.threshold ^ s) ≤ ν) (hmargin : 4 * P.rowError + ν < signal)
    (hrows : ∀ (y : MaskedState N V) (j : MaskedPosition y),
      FinDist.tv (y.exactRow M.target M.target_positive j) (O.row y j) ≤ P.rowError)
    (blocks : PackedSampler.ColorBlocks (N := N) (Color := Color) (P.phases+1) P.repetitions)
    (path : Program.RetainedPath O
      ((PackedSampler.sampler P).program blocks (O.readState (MaskedState.allMask N V))))
    (hgood : ¬ (PackedSampler.samplerMarker P M O blocks).HitsRepair O path) :
    (Program.retainedRoundCount O
      ((PackedSampler.sampler P).program blocks (O.readState (MaskedState.allMask N V))) path : ℝ) <
      4*(N : ℝ)*ForestIteration.phaseCap N P.cutoff/P.cutoff + ForestIteration.centroidDepth N := by
  have hb := samplerMarker_goodWithinRounds P M O C s ν signal hN hD hphases hextra
    hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows blocks
  have hc := GoodWithinRounds.retainedRoundCount_le O _ _ hb path hgood
  have hJ : 0 < ForestIteration.phaseCap N P.cutoff :=
    ForestIteration.phaseCap_pos N P.cutoff hD (by omega)
  have hp := mul_lt_mul_of_pos_right (peelAllowance_lt N P.cutoff hN (by omega))
    (show (0 : ℝ) < ForestIteration.phaseCap N P.cutoff by exact_mod_cast hJ)
  have hcr : (Program.retainedRoundCount O
      ((PackedSampler.sampler P).program blocks (O.readState (MaskedState.allMask N V))) path : ℝ) ≤
      (peelAllowance N P.cutoff : ℝ) * ForestIteration.phaseCap N P.cutoff + ForestIteration.centroidDepth N := by
    exact_mod_cast hc
  calc
    _ ≤ _ := hcr
    _ < (4*(N : ℝ)/P.cutoff)*ForestIteration.phaseCap N P.cutoff + ForestIteration.centroidDepth N :=
      by linarith
    _ = _ := by ring

end SuccessfulPathResources
end ForestSampling
