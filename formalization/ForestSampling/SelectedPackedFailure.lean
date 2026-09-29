import ForestSampling.SelectedPackedSampler
import ForestSampling.PackedFailure

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ForestSampling.SelectedPackedSampler

variable {N repetitions : ℕ} {V Color State Seed : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]

open Program Program.PrefixRepair
open PackedSampler (ColorBlocks Parameters seedLaw initialBanks initialDraft initialMarginal)

/-- Lift markers through the actual selected screen, preserving its public
memory update and its own chosen rows. No comparison of selectors is made. -/
noncomputable def markScreen (policy : Policy N V Color State repetitions)
    (memory : State) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : State → (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (marked : ∀ memory rows, PrefixRepair (next memory rows) (next memory rows)) :
    PrefixRepair (runScreen policy memory h B draft baseline q cutoff ε colors next)
      (runScreen policy memory h B draft baseline q cutoff ε colors next) := by
  classical
  let output := fun (table : Program.ReplyTable (Screening.scheduledSubmission h B draft colors q)) ↦
    (policy.remember h memory colors (observations h B draft colors q table),
      fun j ↦ (policy.selector h memory colors).choose j
        (Screening.tableCandidate h B draft colors q ε table j) cutoff
        (observations h B draft colors q table))
  exact if hempty : B.maxSize = 0 then
    selfTransport (q := next (policy.remember h memory colors []) (fun _ ↦ ∅))
      (by simp only [runScreen, if_pos hempty]) (marked _ _)
  else selfTransport (q := runQuerySchedule (Screening.scheduledSubmission h B draft colors q)
      Finset.univ.toList (fun _ j ↦ baseline j) (fun table ↦ next (output table).1 (output table).2))
    (by simp only [runScreen, if_neg hempty, Screening.runPackedQueries, output])
    (querySchedule (Screening.scheduledSubmission h B draft colors q)
      Finset.univ.toList _ _ (fun table ↦ marked (output table).1 (output table).2))

private theorem weighted_const [Fintype Seed] (μ : FinDist Seed) (c : ℝ) :
    ∑ w, μ w * c = c := by rw [← Finset.sum_mul, μ.sum_mass, one_mul]

/-- Future color averaging commutes with this screen because the policy
can read the fixed current block and past memory but not the future seed. -/
theorem mean_markScreen_le [Fintype Seed] (policy : Policy N V Color State repetitions)
    (μ : FinDist Seed) (memory : State)
    (O : FrozenOracle N V) (K : BatchKernel N V) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : Seed → State → (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (marked : ∀ w memory rows, PrefixRepair (next w memory rows) (next w memory rows))
    (bound : ℝ) (hbound : ∀ memory rows,
      (∑ w, μ w * (marked w memory rows).failureMassWith O K) ≤ bound) :
    (∑ w, μ w * (markScreen policy memory h B draft baseline q cutoff ε colors
      (next w) (marked w)).failureMassWith O K) ≤ bound := by
  classical
  by_cases hempty : B.maxSize = 0
  · simpa only [markScreen, dif_pos hempty, failureMassWith_selfTransport] using
      hbound (policy.remember h memory colors []) (fun _ ↦ ∅)
  · simp only [markScreen, dif_neg hempty, failureMassWith_selfTransport,
      failureMassWith_querySchedule]
    exact hbound _ _

noncomputable def markLoop (policy : Policy N V Color State repetitions) (M : ForestModel N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (ε : ℝ) :
    (phases : ℕ) →
    (blocks : ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions) →
    (memory : State) → (extra : ℕ) → (h : History N V) →
    PrefixRepair (loop policy B draft baseline q cutoff ε phases blocks memory extra h)
      (loop policy B draft baseline q cutoff ε phases blocks memory extra h)
  | 0, blocks, memory, extra, h => by
      classical
      exact if hc : h.committed = Finset.univ then
        selfTransport (q := .done hc) (by rw [loop, dif_pos hc]) (.done hc)
      else if _hgood : Screening.ScreenSuccess M h (blocks 0) cutoff then
        selfTransport (by rw [loop, dif_neg hc]; rfl)
          (markScreen policy memory h B draft baseline q cutoff ε (blocks 0)
            (fun memory' rows ↦ CappedController.terminal extra h (CappedController.rowGraph h rows))
            (fun memory' rows ↦ unmarked (CappedController.terminal extra h (CappedController.rowGraph h rows))))
      else .stop _ _
  | phases' + 1, blocks, memory, extra, h => by
      classical
      exact if hc : h.committed = Finset.univ then
        selfTransport (q := .done hc) (by rw [loop, dif_pos hc]) (.done hc)
      else if _hgood : Screening.ScreenSuccess M h (blocks 0) cutoff then
        selfTransport (by rw [loop, dif_neg hc]; rfl)
          (markScreen policy memory h B draft baseline q cutoff ε (blocks 0)
            (fun memory' rows ↦
              let peel := ForestPeeling.peelSet cutoff rows
              if peel = ∅ then CappedController.terminal extra h (CappedController.rowGraph h rows)
              else CappedController.peelPass
                ((peel.map (Function.Embedding.subtype _)).sort (· ≤ ·)) extra h
                (fun extra' h' ↦ loop policy B draft baseline q cutoff ε phases'
                  (fun call ↦ blocks call.succ) memory' extra' h'))
            (fun memory' rows ↦ if hempty : ForestPeeling.peelSet cutoff rows = ∅ then
              selfTransport (q := CappedController.terminal extra h (CappedController.rowGraph h rows))
                (by simp only [if_pos hempty]) (unmarked _)
            else selfTransport (by simp only [if_neg hempty])
              (PackedSampler.markPeel
                (((ForestPeeling.peelSet cutoff rows).map (Function.Embedding.subtype _)).sort (· ≤ ·))
                extra h
                (fun extra' h' ↦ loop policy B draft baseline q cutoff ε phases'
                  (fun call ↦ blocks call.succ) memory' extra' h')
                (fun extra' h' ↦ markLoop policy M B draft baseline q cutoff ε phases'
                  (fun call ↦ blocks call.succ) memory' extra' h'))))
      else .stop _ _

/-- Adaptive union bound for the concrete capped loop. The premise is only
the proved one-screen bound at each fixed history. Independence of reached
histories from future seed blocks is proved by the program recursion,
query-table semantics, and finite interchange of commit/seed sums. -/
theorem mean_markLoop_le (policy : Policy N V Color State repetitions) (M : ForestModel N V)
    (O : FrozenOracle N V) (K : BatchKernel N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (ε : ℝ)
    (blockLaw : FinDist (Fin repetitions → Position N → Color))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hscreen : ∀ h : History N V,
      blockLaw.eventMass (fun colors ↦ ¬ Screening.ScreenSuccess M h colors cutoff) ≤ δ)
    (phases : ℕ)
    (memory : State) (extra : ℕ) (h : History N V) :
    (∑ blocks, FinDist.piProduct (fun _ : Fin (phases + 1) ↦ blockLaw) blocks *
      (markLoop policy M B draft baseline q cutoff ε phases blocks memory extra h).failureMassWith O K) ≤
      (phases + 1 : ℕ) * δ := by
  classical
  induction phases generalizing memory extra h with
  | zero =>
      by_cases hc : h.committed = Finset.univ
      · simpa only [markLoop, dif_pos hc, failureMassWith_selfTransport,
          failureMassWith, mul_zero, Finset.sum_const_zero, Nat.cast_add, Nat.cast_zero,
          Nat.cast_one, zero_add, one_mul] using hδ
      · rw [FinDist.piProduct_expect_cons]
        calc
          _ ≤ ∑ colors, blockLaw colors *
              (if ¬ Screening.ScreenSuccess M h colors cutoff then (1 : ℝ) else 0) := by
            apply Finset.sum_le_sum
            intro colors _
            apply mul_le_mul_of_nonneg_left _ (blockLaw.nonneg colors)
            by_cases hgood : Screening.ScreenSuccess M h colors cutoff
            · simp only [markLoop, dif_neg hc, Fin.cons_zero,
                failureMassWith_selfTransport, hgood, not_true_eq_false, if_false, ↓reduceDIte]
              apply mean_markScreen_le
              intro memory' rows
              simp only [failureMassWith_unmarked, mul_zero, Finset.sum_const_zero, le_refl]
            · simp only [markLoop, dif_neg hc, Fin.cons_zero,
                failureMassWith, hgood, not_false_eq_true, if_true, ↓reduceDIte]
              exact le_of_eq (weighted_const _ 1)
          _ = blockLaw.eventMass (fun colors ↦ ¬ Screening.ScreenSuccess M h colors cutoff) := by
            unfold FinDist.eventMass
            apply Finset.sum_congr rfl
            intro colors _
            split <;> simp
          _ ≤ _ := by simpa using hscreen h
  | succ phases ih =>
      have hrest : 0 ≤ (phases + 1 : ℕ) * δ :=
        mul_nonneg (Nat.cast_nonneg _) hδ
      by_cases hc : h.committed = Finset.univ
      · simpa only [markLoop, dif_pos hc, failureMassWith_selfTransport,
          failureMassWith, mul_zero, Finset.sum_const_zero] using
            (mul_nonneg (Nat.cast_nonneg (phases + 1 + 1)) hδ)
      · rw [FinDist.piProduct_expect_cons]
        calc
          _ ≤ ∑ colors, blockLaw colors *
              ((if ¬ Screening.ScreenSuccess M h colors cutoff then (1 : ℝ) else 0) +
                (phases + 1 : ℕ) * δ) := by
            apply Finset.sum_le_sum
            intro colors _
            apply mul_le_mul_of_nonneg_left _ (blockLaw.nonneg colors)
            by_cases hgood : Screening.ScreenSuccess M h colors cutoff
            · simp only [markLoop, dif_neg hc, Fin.cons_zero,
                failureMassWith_selfTransport, hgood, not_true_eq_false, if_false, zero_add,
                ↓reduceDIte]
              apply mean_markScreen_le
              intro memory' rows
              by_cases hempty : ForestPeeling.peelSet cutoff rows = ∅
              · simpa only [dif_pos hempty, failureMassWith_selfTransport,
                  failureMassWith_unmarked, mul_zero, Finset.sum_const_zero] using hrest
              · simp only [dif_neg hempty, failureMassWith_selfTransport]
                apply PackedSampler.mean_markPeel_le _ O K _ extra h _ _ _ hrest
                intro extra' h'
                exact ih memory' extra' h'
            · simp only [markLoop, dif_neg hc, Fin.cons_zero,
                failureMassWith, hgood, not_false_eq_true, if_true, ↓reduceDIte]
              rw [weighted_const]
              linarith
          _ = blockLaw.eventMass (fun colors ↦ ¬ Screening.ScreenSuccess M h colors cutoff) +
                (phases + 1 : ℕ) * δ := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, weighted_const]
            congr 1
            unfold FinDist.eventMass
            apply Finset.sum_congr rfl
            intro colors _
            split <;> simp
          _ ≤ (phases + 1 + 1 : ℕ) * δ := by
            have hfail := hscreen h
            push_cast
            nlinarith

/-- The actual independent uniform blocks meet the allocated adaptive
failure budget, for either oracle-product or true-joint batch draws. -/
theorem mean_markLoop_le_budget [Nonempty Color] (policy : Policy N V Color State repetitions) (M : ForestModel N V)
    (O : FrozenOracle N V) (K : BatchKernel N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (q cutoff : ℕ) (ε : ℝ)
    (phases : ℕ) (memory : State) (extra : ℕ) (h : History N V) (η : ℝ) (hN : 0 < N) (hη : 0 < η)
    (hcolors : 8 * (cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (repetitions : ℝ)) :
    (∑ blocks, FinDist.piProduct (fun _ : Fin (phases + 1) ↦
        FinDist.piProduct (fun _ : Fin repetitions ↦
          FinDist.uniformColors (α := Position N) (Color := Color))) blocks *
      (markLoop policy M B draft baseline q cutoff ε phases blocks memory extra h).failureMassWith O K) ≤ η := by
  have hmean := mean_markLoop_le policy M O K B draft baseline q cutoff ε
    (FinDist.piProduct (fun _ : Fin repetitions ↦
      FinDist.uniformColors (α := Position N) (Color := Color)))
    (η / (phases + 1 : ℕ)) (div_nonneg hη.le (Nat.cast_nonneg _))
    (fun h' ↦ Screening.screenFailure_le_budget M h' cutoff repetitions (phases + 1) η
      hN (by omega) hη hcolors hT) phases memory extra h
  have hc : (phases + 1 : ℝ) ≠ 0 := by positivity
  convert hmean using 1
  push_cast
  field_simp


/-- The first failed-screen marker for the actual sampler at its actual
all-mask oracle reply. This is solely an execution event used in analysis. -/
noncomputable def samplerMarker (P : Parameters N V)
    (policy : Policy N V Color State P.repetitions)
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State) (M : ForestModel N V)
    (O : FrozenOracle N V)
    (blocks : ColorBlocks (N := N) (Color := Color) (P.phases + 1) P.repetitions) :
    PrefixRepair
      ((sampler P policy initialMemory).program blocks (O.readState (MaskedState.allMask N V)))
      ((sampler P policy initialMemory).program blocks (O.readState (MaskedState.allMask N V))) :=
  markLoop policy M
    (initialBanks (O.readState (MaskedState.allMask N V)) P.threshold P.rowError P.thresholdFloor)
    (initialDraft (O.readState (MaskedState.allMask N V)))
    (initialMarginal (O.readState (MaskedState.allMask N V)))
    P.chunkSize P.cutoff P.rowError P.phases blocks
      (initialMemory (O.readState (MaskedState.allMask N V))) P.extraRounds (History.empty N V)

/-- Finite seed-average probability of reaching a failed screen in the
actual sampler. The batch kernel is fixed before seed averaging, and may
be the implemented oracle product or the exact joint target reference. -/
theorem sampler_mean_failure_le [Nonempty Color] (P : Parameters N V)
    (policy : Policy N V Color State P.repetitions)
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State)
    (M : ForestModel N V) (O : FrozenOracle N V) (K : BatchKernel N V)
    (η : ℝ) (hN : 0 < N) (hη : 0 < η)
    (hcolors : 8 * (P.cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((P.phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (P.repetitions : ℝ)) :
    (∑ blocks, seedLaw (Color := Color) P blocks *
      (samplerMarker P policy initialMemory M O blocks).failureMassWith O K) ≤ η :=
  mean_markLoop_le_budget policy M O K _ _ _ P.chunkSize P.cutoff P.rowError
    P.phases (initialMemory (O.readState (MaskedState.allMask N V))) P.extraRounds (History.empty N V) η hN hη hcolors hT

/-- The preceding recursive failure mass is exactly the probability of
the first failed-screen event on actual retained execution paths. -/
theorem sampler_reached_screen_failure_le [Nonempty Color] (P : Parameters N V)
    (policy : Policy N V Color State P.repetitions)
    (initialMemory : PackedSampler.InitialReply (N := N) (V := V) → State)
    (M : ForestModel N V) (O : FrozenOracle N V) (K : BatchKernel N V)
    (η : ℝ) (hN : 0 < N) (hη : 0 < η)
    (hcolors : 8 * (P.cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((P.phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (P.repetitions : ℝ)) :
    (∑ blocks, seedLaw (Color := Color) P blocks *
      (Program.retainedLaw O K
        ((sampler P policy initialMemory).program blocks (O.readState (MaskedState.allMask N V)))).eventMass
        ((samplerMarker P policy initialMemory M O blocks).HitsRepair O)) ≤ η := by
  simp_rw [← failureMassWith_eq_event]
  exact sampler_mean_failure_le P policy initialMemory M O K η hN hη hcolors hT


end ForestSampling.SelectedPackedSampler
