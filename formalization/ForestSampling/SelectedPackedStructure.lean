import ForestSampling.SelectedPackedFailure
import ForestSampling.PackedLoopStructure

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.SelectedPackedSampler

noncomputable section
attribute [local instance] Classical.propDecidable

open Program Program.PrefixRepair
open PackedLoopStructure (highCount peelList highCount_after_peel peelList_length_lt
  initial_highCount_lt rows_exact_at_cap safeBeforeStop_markPeel safeBeforeStop_querySchedule)

variable {N repetitions : ℕ} {V Color State : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]

/-- The complete transcript actually supplied to the chosen selector. -/
def actualTranscript (O : FrozenOracle N V) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : Fin repetitions → Position N → Color) (q : ℕ) : List (Observation N V) :=
  if B.maxSize = 0 then [] else observations h B draft colors q
    (fun index ↦ O.readState (Screening.scheduledSubmission h B draft colors q index).state)

/-- The next public memory of this policy's actual screen. -/
def actualMemory (policy : Policy N V Color State repetitions) (memory : State)
    (O : FrozenOracle N V) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : Fin repetitions → Position N → Color) (q : ℕ) : State :=
  policy.remember h memory colors (actualTranscript O h B draft colors q)

/-- The rows actually returned by this chosen policy on its own public past. -/
def actualRows (policy : Policy N V Color State repetitions) (memory : State)
    (O : FrozenOracle N V) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (colors : Fin repetitions → Position N → Color) (q D : ℕ) (ε : ℝ)
    (j : ResidualVertex h) : Finset (ResidualVertex h) :=
  Screening.returnedRow O h B draft colors q D ε (policy.selector h memory colors)
    (actualTranscript O h B draft colors q) j

/-- A chosen screen performs only queries and pure public updates before
its continuation. Safety is checked at its actual rows and actual memory. -/
theorem safeBeforeStop_markScreen (policy : Policy N V Color State repetitions)
    (memory : State) (M : ForestModel N V) (O : FrozenOracle N V)
    (h : History N V) (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q D : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : State → (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (marked : ∀ memory rows, PrefixRepair (next memory rows) (next memory rows))
    (hsafe : (marked (actualMemory policy memory O h B draft colors q)
      (actualRows policy memory O h B draft colors q D ε)).SafeBeforeStop M O) :
    (markScreen policy memory h B draft baseline q D ε colors next marked).SafeBeforeStop M O := by
  by_cases hempty : B.maxSize = 0
  · have hrows : actualRows policy memory O h B draft colors q D ε = fun _ ↦ ∅ := by
      funext j
      simp only [actualRows, Screening.returnedRow, if_pos hempty]
    rw [hrows] at hsafe
    change (marked (policy.remember h memory colors
      (if B.maxSize = 0 then [] else observations h B draft colors q
        (fun index ↦ O.readState (Screening.scheduledSubmission h B draft colors q index).state)))
      (fun _ ↦ ∅)).SafeBeforeStop M O at hsafe
    rw [if_pos hempty] at hsafe
    simpa only [markScreen, dif_pos hempty, safeBeforeStop_selfTransport] using hsafe
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
    simp only [markScreen, dif_neg hempty, safeBeforeStop_selfTransport, safeBeforeStop_querySchedule]
    rw [fillQueryReplies_eq (Screening.scheduledSubmission h B draft colors q) O
      Finset.univ.toList (fun i ↦ by simp)]
    exact hsafe

theorem markLoop_safeBeforeStop (policy : Policy N V Color State repetitions) (M : ForestModel N V) (O : FrozenOracle N V)
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
    (markLoop policy M B draft baseline q D ε phases blocks memory extra h).SafeBeforeStop M O := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hratio : 0 < 8 / (D : ℝ) := by positivity
  induction phases generalizing memory extra h with
  | zero =>
      by_cases hc : h.committed = Finset.univ
      · simp only [markLoop, dif_pos hc, safeBeforeStop_selfTransport, SafeBeforeStop]
      · by_cases hgood : Screening.ScreenSuccess M h (blocks 0) D
        · simp only [markLoop, dif_neg hc, dif_pos hgood, safeBeforeStop_selfTransport]
          apply safeBeforeStop_markScreen
          rw [safeBeforeStop_unmarked]
          apply PackedStructure.terminal_structurallySafe_of_depth M O _ extra h
          · apply PackedStructure.residual_rowGraph_eq M.graph h _
            exact rows_exact_at_cap M h D hN hD _ (hscreen h memory (blocks 0) hgood) (by simpa using hhigh)
          · exact_mod_cast (by simpa using hfuel : (ForestIteration.centroidDepth N : ℝ) ≤ extra)
        · simp only [markLoop, dif_neg hc, dif_neg hgood, SafeBeforeStop]
  | succ phases ih =>
      by_cases hc : h.committed = Finset.univ
      · simp only [markLoop, dif_pos hc, safeBeforeStop_selfTransport, SafeBeforeStop]
      · by_cases hgood : Screening.ScreenSuccess M h (blocks 0) D
        · simp only [markLoop, dif_neg hc, dif_pos hgood, safeBeforeStop_selfTransport]
          apply safeBeforeStop_markScreen
          let rows := actualRows policy memory O h B draft (blocks 0) q D ε
          have hrows : ForestPeeling.ScreenContract (residualGraph M.graph h) D rows := hscreen h memory _ hgood
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
        · simp only [markLoop, dif_neg hc, dif_neg hgood, SafeBeforeStop]

/-- The exact public initial phase and hard-round caps satisfy the invariant
used by the concrete marked-loop induction. -/
theorem initial_markLoop_safeBeforeStop (policy : Policy N V Color State repetitions) (M : ForestModel N V) (O : FrozenOracle N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q D : ℕ) (ε : ℝ)
    (hN : 0 < N) (hD : 9 ≤ D)
    (hscreen : ∀ (h : History N V) (memory : State) (colors : Fin repetitions → Position N → Color),
      Screening.ScreenSuccess M h colors D →
      ForestPeeling.ScreenContract (residualGraph M.graph h) D (actualRows policy memory O h B draft colors q D ε))
    (blocks : PackedSampler.ColorBlocks (N := N) (Color := Color)
      (ForestIteration.phaseCap N D + 1) repetitions) (memory : State) (h : History N V) :
    (markLoop policy M B draft baseline q D ε (ForestIteration.phaseCap N D)
      blocks memory (ForestIteration.hardRoundCap N D - 1) h).SafeBeforeStop M O := by
  apply markLoop_safeBeforeStop policy M O B draft baseline q D ε hN hD hscreen
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

/-- The actual chosen-policy row function satisfies the screen contract from
exactly the manuscript's model, oracle, feasibility, and margin assumptions. -/
theorem actualRows_screenContract (policy : Policy N V Color State repetitions) (memory : State) (M : ForestModel N V) (O : FrozenOracle N V)
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
      (actualRows policy memory O h (Screening.Banks.ofOracle O t ε hfloor) draft colors q D ε) :=
  PackedStructure.screenContract_of_returnedRow M O h draft colors q D C s t ε ν signal
    hfloor hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows hsuccess _ _

/-- With the public caps and the stated model/oracle assumptions, every
seed of the actual sampler is structurally safe before its first failed
screen. No abstract safety, recurrence, or successful-row hypothesis remains. -/
theorem samplerMarker_safeBeforeStop (P : PackedSampler.Parameters N V)
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
    (samplerMarker P policy initialMemory M O blocks).SafeBeforeStop M O := by
  rcases P with ⟨q, hq, D, phases, extra, repetitions, t, ε, hfloor⟩
  dsimp only at hD hphases hextra hε ht0 ht1 hfeasible hmargin hrows blocks ⊢
  subst phases
  subst extra
  unfold samplerMarker
  apply initial_markLoop_safeBeforeStop policy M O _ _ _ q D ε hN hD
  intro h memory colors hsuccess
  rw [PackedSampler.initialBanks_oracle]
  exact actualRows_screenContract policy memory M O h _ colors q D C s t ε ν signal
    hfloor hε hν ht0 ht1 hRT hUEN hfeasible hmargin hrows hsuccess

end
end ForestSampling.SelectedPackedSampler
