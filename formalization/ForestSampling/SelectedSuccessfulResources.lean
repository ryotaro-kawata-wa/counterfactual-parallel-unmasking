import ForestSampling.SelectedPackedStructure
import ForestSampling.PackedLoopStructure
import ForestSampling.SuccessfulPathResources

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.SelectedPackedSampler
namespace SuccessfulResources
open ForestSampling.SuccessfulPathResources

noncomputable section
attribute [local instance] Classical.propDecidable

open Program Program.PrefixRepair
open PackedLoopStructure (highCount peelList highCount_after_peel peelList_length_lt
  initial_highCount_lt rows_exact_at_cap)

variable {N repetitions : ℕ} {V Color State : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]


theorem selectedScreen_goodWithinRounds (policy : Policy N V Color State repetitions)
    (memory : State) (O : FrozenOracle N V)
    (h : History N V) (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q D : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : State → (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (marked : ∀ memory rows, PrefixRepair (next memory rows) (next memory rows))
    (R : ℕ) (hsafe : (marked (actualMemory policy memory O h B draft colors q)
      (actualRows policy memory O h B draft colors q D ε)).GoodWithinRounds O R) :
    (markScreen policy memory h B draft baseline q D ε colors next marked).GoodWithinRounds O R := by
  by_cases hempty : B.maxSize = 0
  · have hrows : actualRows policy memory O h B draft colors q D ε = fun _ ↦ ∅ := by
      funext j
      simp only [actualRows, Screening.returnedRow, if_pos hempty]
    rw [hrows] at hsafe
    change (marked (policy.remember h memory colors
      (if B.maxSize = 0 then [] else observations h B draft colors q
        (fun index ↦ O.readState (Screening.scheduledSubmission h B draft colors q index).state)))
      (fun _ ↦ ∅)).GoodWithinRounds O R at hsafe
    rw [if_pos hempty] at hsafe
    simpa only [markScreen, dif_pos hempty, goodWithinRounds_selfTransport] using hsafe
  · have hrows : actualRows policy memory O h B draft colors q D ε = fun j ↦
        (policy.selector h memory colors).choose j
          (Screening.tableCandidate h B draft colors q ε
            (fun index ↦ O.readState (Screening.scheduledSubmission h B draft colors q index).state) j)
          D (observations h B draft colors q
            (fun index ↦ O.readState (Screening.scheduledSubmission h B draft colors q index).state)) := by
      funext j
      simp only [actualRows, Screening.returnedRow, if_neg hempty,
        Screening.tableCandidate_oracle, actualTranscript]
    rw [hrows] at hsafe
    unfold actualMemory actualTranscript at hsafe
    rw [if_neg hempty] at hsafe
    simp only [markScreen, dif_neg hempty, goodWithinRounds_selfTransport, goodWithinRounds_querySchedule]
    rw [fillQueryReplies_eq (Screening.scheduledSubmission h B draft colors q) O
      Finset.univ.toList (fun i ↦ by simp)]
    exact hsafe

theorem selectedLoop_goodWithinRounds (policy : Policy N V Color State repetitions) (M : ForestModel N V) (O : FrozenOracle N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q D : ℕ) (ε : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D)
    (hscreen : ∀ (h : History N V) (memory : State) (colors : Fin repetitions → Position N → Color),
      Screening.ScreenSuccess M h colors D →
      ForestPeeling.ScreenContract (residualGraph M.graph h) D (actualRows policy memory O h B draft colors q D ε))
    (phases : ℕ) (blocks : PackedSampler.ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions)
    (memory : State) (extra : ℕ) (h : History N V)
    (hphase : phases ≤ ForestIteration.phaseCap N D)
    (hfuel : 4 * (N : ℝ) * phases / D + ForestIteration.centroidDepth N ≤ extra)
    (hhigh : (highCount M h D : ℝ) <
      (8 / (D : ℝ)) ^ (ForestIteration.phaseCap N D - phases) * (2 * (N : ℝ) / (D + 1))) :
    (markLoop policy M B draft baseline q D ε phases blocks memory extra h).GoodWithinRounds O (peelAllowance N D * phases + ForestIteration.centroidDepth N) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hratio : 0 < 8 / (D : ℝ) := by positivity
  induction phases generalizing memory extra h with
  | zero =>
      by_cases hc : h.committed = Finset.univ
      · simp only [markLoop, dif_pos hc, goodWithinRounds_selfTransport, GoodWithinRounds]
      · by_cases hgood : Screening.ScreenSuccess M h (blocks 0) D
        · simp only [markLoop, dif_neg hc, dif_pos hgood, goodWithinRounds_selfTransport]
          apply selectedScreen_goodWithinRounds
          simp only [Nat.mul_zero, Nat.zero_add]
          apply goodWithinRounds_unmarked O _ 0 _
          apply terminal_withinCentroidDepth M O _ extra h
          · apply PackedStructure.residual_rowGraph_eq M.graph h _
            exact rows_exact_at_cap M h D hN hD _ (hscreen h memory (blocks 0) hgood) (by simpa using hhigh)
          · exact_mod_cast (by simpa using hfuel : (ForestIteration.centroidDepth N : ℝ) ≤ extra)
        · simp only [markLoop, dif_neg hc, dif_neg hgood, GoodWithinRounds]
  | succ phases ih =>
      by_cases hc : h.committed = Finset.univ
      · simp only [markLoop, dif_pos hc, goodWithinRounds_selfTransport, GoodWithinRounds]
      · by_cases hgood : Screening.ScreenSuccess M h (blocks 0) D
        · simp only [markLoop, dif_neg hc, dif_pos hgood, goodWithinRounds_selfTransport]
          apply selectedScreen_goodWithinRounds
          let rows := actualRows policy memory O h B draft (blocks 0) q D ε
          have hrows : ForestPeeling.ScreenContract (residualGraph M.graph h) D rows := hscreen h memory _ hgood
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
            apply ih (fun call ↦ blocks call.succ) _ extra' h' (by omega)
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
        · simp only [markLoop, dif_neg hc, dif_neg hgood, GoodWithinRounds]


theorem initial_selectedLoop_goodWithinRounds (policy : Policy N V Color State repetitions) (M : ForestModel N V) (O : FrozenOracle N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q D : ℕ) (ε : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D)
    (hscreen : ∀ (h : History N V) (memory : State) (colors : Fin repetitions → Position N → Color),
      Screening.ScreenSuccess M h colors D →
      ForestPeeling.ScreenContract (residualGraph M.graph h) D (actualRows policy memory O h B draft colors q D ε))
    (blocks : PackedSampler.ColorBlocks (N := N) (Color := Color)
      (ForestIteration.phaseCap N D + 1) repetitions) (memory : State) (h : History N V) :
    (markLoop policy M B draft baseline q D ε (ForestIteration.phaseCap N D)
      blocks memory (ForestIteration.hardRoundCap N D - 1) h).GoodWithinRounds O (peelAllowance N D * ForestIteration.phaseCap N D + ForestIteration.centroidDepth N) := by
  apply selectedLoop_goodWithinRounds policy M O B draft baseline q D ε hN hD hscreen
    _ blocks memory _ h le_rfl
  · have hc := Nat.le_ceil (4 * (N : ℝ) * ForestIteration.phaseCap N D / D)
    unfold ForestIteration.hardRoundCap
    rw [show ⌈4 * (N : ℝ) * ForestIteration.phaseCap N D / D⌉₊ +
        ForestIteration.centroidDepth N + 2 - 1 =
      ⌈4 * (N : ℝ) * ForestIteration.phaseCap N D / D⌉₊ +
        ForestIteration.centroidDepth N + 1 by omega]
    push_cast
    linarith
  · simpa using initial_highCount_lt M h D hN


theorem selectedSamplerMarker_goodWithinRounds (P : PackedSampler.Parameters N V)
    (policy : Policy N V Color State P.repetitions)
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State)
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
    (samplerMarker P policy initialMemory M O blocks).GoodWithinRounds O (peelAllowance N P.cutoff * ForestIteration.phaseCap N P.cutoff + ForestIteration.centroidDepth N) := by
  rcases P with ⟨q, hq, D, phases, extra, repetitions, t, ε, hfloor⟩
  dsimp only at hD hphases hextra hε ht0 ht1 hfeasible hmargin hrows blocks ⊢
  subst phases
  subst extra
  unfold samplerMarker
  apply initial_selectedLoop_goodWithinRounds policy M O _ _ _ q D ε hN hD
  intro h memory colors hsuccess
  rw [PackedSampler.initialBanks_oracle]
  exact actualRows_screenContract policy memory M O h _ colors q D C s t ε ν signal
    hfloor hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows hsuccess

theorem selectedSampler_successful_rounds_lt (P : PackedSampler.Parameters N V)
    (policy : Policy N V Color State P.repetitions)
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State)
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
      ((sampler P policy initialMemory).program blocks (O.readState (MaskedState.allMask N V))))
    (hgood : ¬ (samplerMarker P policy initialMemory M O blocks).HitsRepair O path) :
    (Program.retainedRoundCount O
      ((sampler P policy initialMemory).program blocks (O.readState (MaskedState.allMask N V))) path : ℝ) <
      4*(N : ℝ)*ForestIteration.phaseCap N P.cutoff/P.cutoff + ForestIteration.centroidDepth N := by
  have hb := selectedSamplerMarker_goodWithinRounds P policy initialMemory M O C s ν signal hN hD hphases hextra
    hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows blocks
  have hc := GoodWithinRounds.retainedRoundCount_le O _ _ hb path hgood
  have hJ : 0 < ForestIteration.phaseCap N P.cutoff :=
    ForestIteration.phaseCap_pos N P.cutoff hD (by omega)
  have hp := mul_lt_mul_of_pos_right (peelAllowance_lt N P.cutoff hN (by omega))
    (show (0 : ℝ) < ForestIteration.phaseCap N P.cutoff by exact_mod_cast hJ)
  have hcr : (Program.retainedRoundCount O
      ((sampler P policy initialMemory).program blocks (O.readState (MaskedState.allMask N V))) path : ℝ) ≤
      (peelAllowance N P.cutoff : ℝ) * ForestIteration.phaseCap N P.cutoff + ForestIteration.centroidDepth N := by
    exact_mod_cast hc
  calc
    _ ≤ _ := hcr
    _ < (4*(N : ℝ)/P.cutoff)*ForestIteration.phaseCap N P.cutoff + ForestIteration.centroidDepth N :=
      by linarith
    _ = _ := by ring

end
end SuccessfulResources
end ForestSampling.SelectedPackedSampler
