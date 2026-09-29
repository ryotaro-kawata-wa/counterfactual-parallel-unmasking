import ForestSampling.PackedSampler
import ForestSampling.ProgramFailure
import ForestSampling.FiniteSeed

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ForestSampling
namespace PackedSampler

variable {N : ℕ} {V Color Seed : Type*}
variable [Fintype V] [DecidableEq V] [LinearOrder V] [Nonempty V]
variable [Fintype Color] [DecidableEq Color]

open Program Program.PrefixRepair

/-- Lift continuation failure markers through the actual packed screen.
The screen's deterministic queries introduce no additional marker. -/
noncomputable def markScreen (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q cutoff : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (marked : ∀ rows, PrefixRepair (next rows) (next rows)) :
    PrefixRepair (runStandardScreen h B draft baseline repetitions q cutoff ε colors next)
      (runStandardScreen h B draft baseline repetitions q cutoff ε colors next) := by
  classical
  let select := fun (table : Program.ReplyTable (Screening.scheduledSubmission h B draft colors q)) j ↦
    (PublicRowSelector.standardTopVotes
      (fun (scores : ResidualVertex h → ResidualVertex h → ℕ) j i ↦ scores j i)).choose j
      (Screening.tableCandidate h B draft colors q ε table j) cutoff
      (fun j i ↦ (Finset.univ.filter (fun τ ↦ Screening.tableVote h B draft colors q ε table τ i j)).card)
  exact if hempty : B.maxSize = 0 then
    selfTransport (q := next (fun _ ↦ ∅))
      (by simp only [runStandardScreen, Screening.runScreen, if_pos hempty]) (marked _)
  else selfTransport (q := runQuerySchedule (Screening.scheduledSubmission h B draft colors q)
      Finset.univ.toList (fun _ j ↦ baseline j) (fun table ↦ next (select table)))
    (by simp only [runStandardScreen, Screening.runScreen, if_neg hempty,
      Screening.runPackedQueries, select])
    (querySchedule (Screening.scheduledSubmission h B draft colors q)
      Finset.univ.toList _ _ (fun table ↦ marked (select table)))

omit [Nonempty V] in
private theorem weighted_const [Fintype Seed] (μ : FinDist Seed) (c : ℝ) :
    ∑ w, μ w * c = c := by rw [← Finset.sum_mul, μ.sum_mass, one_mul]

omit [Nonempty V] in
/-- Fixing the current color block fixes every screen query and reply.
Consequently an average bound for each returned-row continuation survives
the actual screen even when those continuations depend on a future seed. -/
theorem mean_markScreen_le [Fintype Seed] (μ : FinDist Seed)
    (O : FrozenOracle N V) (K : BatchKernel N V) (h : History N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q cutoff : ℕ) (ε : ℝ)
    (colors : Fin repetitions → Position N → Color)
    (next : Seed → (ResidualVertex h → Finset (ResidualVertex h)) → Program N V h)
    (marked : ∀ w rows, PrefixRepair (next w rows) (next w rows))
    (bound : ℝ) (hbound : ∀ rows,
      (∑ w, μ w * (marked w rows).failureMassWith O K) ≤ bound) :
    (∑ w, μ w * (markScreen h B draft baseline repetitions q cutoff ε colors
      (next w) (marked w)).failureMassWith O K) ≤ bound := by
  classical
  by_cases hempty : B.maxSize = 0
  · simpa only [markScreen, dif_pos hempty, failureMassWith_selfTransport] using hbound (fun _ ↦ ∅)
  · simp only [markScreen, dif_neg hempty, failureMassWith_selfTransport,
      failureMassWith_querySchedule]
    exact hbound _

/-- Frozen singleton peeling may consume commit randomness, but it cannot
inspect a future color seed until it reaches its continuation. -/
noncomputable def markPeel :
    (todo : List (Position N)) → (extra : ℕ) → (h : History N V) →
    (after : (extra : ℕ) → (h : History N V) → Program N V h) →
    (∀ extra h, PrefixRepair (after extra h) (after extra h)) →
    PrefixRepair (CappedController.peelPass todo extra h after)
      (CappedController.peelPass todo extra h after)
  | [], extra, h, _after, marked => marked extra h
  | j :: todo, extra, h, after, marked => by
      classical
      exact if hc : h.committed = Finset.univ then
        selfTransport (by rw [CappedController.peelPass, dif_pos hc]) (.done hc)
      else if hj : j ∈ h.uncommitted then
        match extra with
        | 0 => selfTransport (by rw [CappedController.peelPass, dif_neg hc, dif_pos hj])
            (unmarked (Program.commitAll h))
        | extra' + 1 =>
            selfTransport (by rw [CappedController.peelPass, dif_neg hc, dif_pos hj])
              (.commit _ _ _ _ _ (fun z ↦ markPeel todo extra' _ after marked))
      else selfTransport (by rw [CappedController.peelPass, dif_neg hc, dif_neg hj])
        (markPeel todo extra h after marked)

omit [LinearOrder V] [Nonempty V] in
/-- Interchanging finite seed and commit sums proves independence from all
future blocks along the actual frozen peel pass, including its hard guard. -/
theorem mean_markPeel_le [Fintype Seed] (μ : FinDist Seed)
    (O : FrozenOracle N V) (K : BatchKernel N V)
    (todo : List (Position N)) (extra : ℕ) (h : History N V)
    (after : Seed → (extra : ℕ) → (h : History N V) → Program N V h)
    (marked : ∀ w extra h, PrefixRepair (after w extra h) (after w extra h))
    (bound : ℝ) (hbound0 : 0 ≤ bound)
    (hbound : ∀ extra h,
      (∑ w, μ w * (marked w extra h).failureMassWith O K) ≤ bound) :
    (∑ w, μ w * (markPeel todo extra h (after w) (marked w)).failureMassWith O K) ≤ bound := by
  induction todo generalizing extra h with
  | nil => exact hbound extra h
  | cons j todo ih =>
      by_cases hc : h.committed = Finset.univ
      · simpa only [markPeel, dif_pos hc, failureMassWith_selfTransport, failureMassWith, mul_zero, Finset.sum_const_zero] using hbound0
      · by_cases hj : j ∈ h.uncommitted
        · cases extra with
          | zero => simpa only [markPeel, dif_neg hc, dif_pos hj, failureMassWith_selfTransport, failureMassWith_unmarked, mul_zero, Finset.sum_const_zero] using hbound0
          | succ extra =>
              simp only [markPeel, dif_neg hc, dif_pos hj, failureMassWith_selfTransport, failureMassWith]
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              calc
                _ = ∑ z, K.law h {j} (by simpa using ‹j ∈ h.uncommitted›) z *
                    ∑ w, μ w * (markPeel todo extra
                      (h.appendBatch {j} (by simpa using hj) z)
                      (after w) (marked w)).failureMassWith O K := by
                  apply Finset.sum_congr rfl
                  intro z _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro w _
                  ring
                _ ≤ ∑ z, K.law h {j} (by simpa using ‹j ∈ h.uncommitted›) z * bound :=
                  Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_left (ih extra _)
                    ((K.law h {j} _).nonneg z)
                _ = bound := weighted_const _ _
        · simpa only [markPeel, dif_neg hc, dif_neg hj, failureMassWith_selfTransport] using ih extra h

/- The next annotation uses the true graph only for analysis. It does not
change the concrete sampler, its queries, its batches, or any sampled law. -/

/-- Mark exactly the first reached screen whose color-separation majority
fails. Every other operation is the corresponding actual packed-loop
operation; a completed or terminal execution introduces no marker. -/
noncomputable def markLoop (M : ForestModel N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q cutoff : ℕ) (ε : ℝ) :
    (phases : ℕ) →
    (blocks : ColorBlocks (N := N) (Color := Color) (phases + 1) repetitions) →
    (extra : ℕ) → (h : History N V) →
    PrefixRepair (loop B draft baseline repetitions q cutoff ε phases blocks extra h)
      (loop B draft baseline repetitions q cutoff ε phases blocks extra h)
  | 0, blocks, extra, h => by
      classical
      exact if hc : h.committed = Finset.univ then
        selfTransport (q := .done hc) (by rw [loop, dif_pos hc]) (.done hc)
      else if _hgood : Screening.ScreenSuccess M h (blocks 0) cutoff then
        selfTransport (by rw [loop, dif_neg hc]; rfl)
          (markScreen h B draft baseline repetitions q cutoff ε (blocks 0)
            (fun rows ↦ CappedController.terminal extra h (CappedController.rowGraph h rows))
            (fun rows ↦ unmarked (CappedController.terminal extra h (CappedController.rowGraph h rows))))
      else .stop _ _
  | phases' + 1, blocks, extra, h => by
      classical
      exact if hc : h.committed = Finset.univ then
        selfTransport (q := .done hc) (by rw [loop, dif_pos hc]) (.done hc)
      else if _hgood : Screening.ScreenSuccess M h (blocks 0) cutoff then
        selfTransport (by rw [loop, dif_neg hc]; rfl)
          (markScreen h B draft baseline repetitions q cutoff ε (blocks 0)
            (fun rows ↦
              let peel := ForestPeeling.peelSet cutoff rows
              if peel = ∅ then CappedController.terminal extra h (CappedController.rowGraph h rows)
              else CappedController.peelPass
                ((peel.map (Function.Embedding.subtype _)).sort (· ≤ ·)) extra h
                (fun extra' h' ↦ loop B draft baseline repetitions q cutoff ε phases'
                  (fun call ↦ blocks call.succ) extra' h'))
            (fun rows ↦ if hempty : ForestPeeling.peelSet cutoff rows = ∅ then
              selfTransport (q := CappedController.terminal extra h (CappedController.rowGraph h rows))
                (by simp only [if_pos hempty]) (unmarked _)
            else selfTransport (by simp only [if_neg hempty])
              (markPeel
                (((ForestPeeling.peelSet cutoff rows).map (Function.Embedding.subtype _)).sort (· ≤ ·))
                extra h
                (fun extra' h' ↦ loop B draft baseline repetitions q cutoff ε phases'
                  (fun call ↦ blocks call.succ) extra' h')
                (fun extra' h' ↦ markLoop M B draft baseline repetitions q cutoff ε phases'
                  (fun call ↦ blocks call.succ) extra' h'))))
      else .stop _ _

/-- Adaptive union bound for the concrete capped loop. The premise is only
the proved one-screen bound at each fixed history. Independence of reached
histories from future seed blocks is proved by the program recursion,
query-table semantics, and finite interchange of commit/seed sums. -/
theorem mean_markLoop_le (M : ForestModel N V)
    (O : FrozenOracle N V) (K : BatchKernel N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q cutoff : ℕ) (ε : ℝ)
    (blockLaw : FinDist (Fin repetitions → Position N → Color))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hscreen : ∀ h : History N V,
      blockLaw.eventMass (fun colors ↦ ¬ Screening.ScreenSuccess M h colors cutoff) ≤ δ)
    (phases : ℕ)
    (extra : ℕ) (h : History N V) :
    (∑ blocks, FinDist.piProduct (fun _ : Fin (phases + 1) ↦ blockLaw) blocks *
      (markLoop M B draft baseline repetitions q cutoff ε phases blocks extra h).failureMassWith O K) ≤
      (phases + 1 : ℕ) * δ := by
  classical
  induction phases generalizing extra h with
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
              intro rows
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
              intro rows
              by_cases hempty : ForestPeeling.peelSet cutoff rows = ∅
              · simpa only [dif_pos hempty, failureMassWith_selfTransport,
                  failureMassWith_unmarked, mul_zero, Finset.sum_const_zero] using hrest
              · simp only [dif_neg hempty, failureMassWith_selfTransport]
                apply mean_markPeel_le _ O K _ extra h _ _ _ hrest
                intro extra' h'
                exact ih extra' h'
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
theorem mean_markLoop_le_budget [Nonempty Color] (M : ForestModel N V)
    (O : FrozenOracle N V) (K : BatchKernel N V)
    (B : Screening.Banks (N := N) (V := V)) (draft : Position N → V)
    (baseline : Position N → FinDist V) (repetitions q cutoff : ℕ) (ε : ℝ)
    (phases extra : ℕ) (h : History N V) (η : ℝ) (hN : 0 < N) (hη : 0 < η)
    (hcolors : 8 * (cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (repetitions : ℝ)) :
    (∑ blocks, FinDist.piProduct (fun _ : Fin (phases + 1) ↦
        FinDist.piProduct (fun _ : Fin repetitions ↦
          FinDist.uniformColors (α := Position N) (Color := Color))) blocks *
      (markLoop M B draft baseline repetitions q cutoff ε phases blocks extra h).failureMassWith O K) ≤ η := by
  have hmean := mean_markLoop_le M O K B draft baseline repetitions q cutoff ε
    (FinDist.piProduct (fun _ : Fin repetitions ↦
      FinDist.uniformColors (α := Position N) (Color := Color)))
    (η / (phases + 1 : ℕ)) (div_nonneg hη.le (Nat.cast_nonneg _))
    (fun h' ↦ Screening.screenFailure_le_budget M h' cutoff repetitions (phases + 1) η
      hN (by omega) hη hcolors hT) phases extra h
  have hc : (phases + 1 : ℝ) ≠ 0 := by positivity
  convert hmean using 1
  push_cast
  field_simp

/-- The first failed-screen marker for the actual sampler at its actual
all-mask oracle reply. This is solely an execution event used in analysis. -/
noncomputable def samplerMarker (P : Parameters N V) (M : ForestModel N V)
    (O : FrozenOracle N V)
    (blocks : ColorBlocks (N := N) (Color := Color) (P.phases + 1) P.repetitions) :
    PrefixRepair
      ((sampler (Color := Color) P).program blocks (O.readState (MaskedState.allMask N V)))
      ((sampler (Color := Color) P).program blocks (O.readState (MaskedState.allMask N V))) :=
  markLoop M
    (initialBanks (O.readState (MaskedState.allMask N V)) P.threshold P.rowError P.thresholdFloor)
    (initialDraft (O.readState (MaskedState.allMask N V)))
    (initialMarginal (O.readState (MaskedState.allMask N V)))
    P.repetitions P.chunkSize P.cutoff P.rowError P.phases blocks P.extraRounds (History.empty N V)

/-- Finite seed-average probability of reaching a failed screen in the
actual sampler. The batch kernel is fixed before seed averaging, and may
be the implemented oracle product or the exact joint target reference. -/
theorem sampler_mean_failure_le [Nonempty Color] (P : Parameters N V)
    (M : ForestModel N V) (O : FrozenOracle N V) (K : BatchKernel N V)
    (η : ℝ) (hN : 0 < N) (hη : 0 < η)
    (hcolors : 8 * (P.cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((P.phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (P.repetitions : ℝ)) :
    (∑ blocks, seedLaw (Color := Color) P blocks *
      (samplerMarker P M O blocks).failureMassWith O K) ≤ η :=
  mean_markLoop_le_budget M O K _ _ _ P.repetitions P.chunkSize P.cutoff P.rowError
    P.phases P.extraRounds (History.empty N V) η hN hη hcolors hT

/-- The preceding recursive failure mass is exactly the probability of
the first failed-screen event on actual retained execution paths. -/
theorem sampler_reached_screen_failure_le [Nonempty Color] (P : Parameters N V)
    (M : ForestModel N V) (O : FrozenOracle N V) (K : BatchKernel N V)
    (η : ℝ) (hN : 0 < N) (hη : 0 < η)
    (hcolors : 8 * (P.cutoff + 1) ≤ Fintype.card Color)
    (hT : 8 * Real.log ((P.phases + 1 : ℕ) * (N : ℝ)^2 / η) ≤ (P.repetitions : ℝ)) :
    (∑ blocks, seedLaw (Color := Color) P blocks *
      (Program.retainedLaw O K
        ((sampler (Color := Color) P).program blocks (O.readState (MaskedState.allMask N V)))).eventMass
        ((samplerMarker P M O blocks).HitsRepair O)) ≤ η := by
  simp_rw [← failureMassWith_eq_event]
  exact sampler_mean_failure_le P M O K η hN hη hcolors hT

end PackedSampler
end ForestSampling
