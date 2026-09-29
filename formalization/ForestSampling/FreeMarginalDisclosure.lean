import ForestSampling.SurvivorDisclosure
import ForestSampling.FreeMarginalBudgets
import ForestSampling.DisclosureTransport

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace HardMatching.SurvivorRecord
variable {N K B : ℕ}

/-- A current-history marginal read has no displayed token at any surviving
source, because the analytic retired region already contains the history. -/
theorem queryHits_commitState_eq_empty (r : SurvivorRecord N K)
    (I : HardMatching.InstanceIndex N K) (h : History N (HardVocabulary K B))
    (hh : h.committed ⊆ r.retired) : r.queryHits I (MaskedState.commitState h) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hi, hhit⟩ := Finset.mem_filter.mp hi
  have hn : i ∉ h.committed := fun hc ↦ (Finset.mem_sdiff.mp hi).2 (hh hc)
  simpa [MaskedState.commitState, hn] using hhit

/-- Free marginal feedback retires no additional matching endpoints. -/
theorem queryUpdate_retired_commitState (r : SurvivorRecord N K)
    (I : HardMatching.InstanceIndex N K) (hI : r.Compatible I)
    (h : History N (HardVocabulary K B)) (hh : h.committed ⊆ r.retired) :
    (r.queryUpdate I hI (MaskedState.commitState h)).retired = r.retired := by
  simp [queryUpdate, updateRetirement, fromRegion, retirementClosure,
    queryHits_commitState_eq_empty r I h hh]

/-- Candidate sets of surviving vertices are unchanged by a free marginal
read; values stored at already retired vertices do not enter this estimate. -/
theorem queryCandidates_commitState (r : SurvivorRecord N K)
    (h : History N (HardVocabulary K B)) (hh : h.committed ⊆ r.retired)
    (i : Position N) (hi : i ∉ r.retired) :
    r.queryCandidates (MaskedState.commitState h) i = r.candidates i := by
  classical
  have hn : i ∉ h.committed := fun hc ↦ hi (hh hc)
  simp [queryCandidates, MaskedState.commitState, hn]

/-- Exact fiber disintegration shows that arbitrary free marginal feedback
preserves the query-disclosure potential. -/
theorem uniformDisclosureEval_freeQuery_le [Nonempty (HardVocabulary K B)]
    (P : HardLocalParameters K B) {h : History N (HardVocabulary K B)}
    (state : MaskedState N (HardVocabulary K B)) (respects : state.RespectsHistory h)
    (next : (MaskedPosition state → FinDist (HardVocabulary K B)) →
      Program N (HardVocabulary K B) h)
    (r : SurvivorRecord N K)
    [Nonempty {I : HardMatching.InstanceIndex N K // r.Compatible I}]
    (hh : h.committed ⊆ r.retired) (hstate : state = MaskedState.commitState h) (m q : ℕ)
    (hnext : ∀ I : {I : HardMatching.InstanceIndex N K // r.Compatible I},
      letI : Nonempty {J : HardMatching.InstanceIndex N K //
        (r.queryUpdate I.1 I.2 state).Compatible J} :=
        ⟨⟨I.1, r.compatible_queryUpdate I.1 I.2 state⟩⟩
      uniformDisclosureEval P
        (next ((HardMatching.selectedOracle P I.1.1 I.1.2).readState state))
        (r.queryUpdate I.1 I.2 state) ≤
        2 * ((N - (r.queryUpdate I.1 I.2 state).retired.card : ℕ) : ℝ) *
          q / m) :
    uniformDisclosureEval P (.query state respects next) r ≤
      2 * ((N - r.retired.card : ℕ) : ℝ) * q / m := by
  classical
  let A := {I : HardMatching.InstanceIndex N K // r.Compatible I}
  let g : A → SurvivorRecord N K := fun I ↦ r.queryUpdate I.1 I.2 state
  let f : A → ℝ := fun I ↦ disclosureEval P I.1 (.query state respects next) r I.2
  let w : A → ℝ := fun I ↦
    (((g I).retired.card - r.retired.card : ℕ) : ℝ) +
      2 * ((N - (g I).retired.card : ℕ) : ℝ) * q / m
  have hw : ∀ I J, g I = g J → w I = w J := by
    intro I J hrec
    simp only [w, hrec]
  have hbound : ∀ I : A, letI : Nonempty {J : A // g J = g I} := ⟨⟨I, rfl⟩⟩
      (FinDist.uniform {J : A // g J = g I}).expectation (fun J ↦ f J.1) ≤ w I := by
    intro I
    let r' := r.queryUpdate I.1 I.2 state
    let : Nonempty {J : A // g J = g I} := ⟨⟨I, rfl⟩⟩
    let : Nonempty {J : HardMatching.InstanceIndex N K // r'.Compatible J} :=
      ⟨⟨I.1, r.compatible_queryUpdate I.1 I.2 state⟩⟩
    let e := r.queryRetirementFiberEquiv I.1 I.2 state
    let f' : {J : HardMatching.InstanceIndex N K // r'.Compatible J} → ℝ := fun J ↦
      (((r'.retired.card - r.retired.card : ℕ) : ℝ)) +
        disclosureEval P J.1
          (next ((HardMatching.selectedOracle P I.1.1 I.1.2).readState state)) r' J.2
    have hfun : (fun J : {J : A // g J = g I} ↦ f J.1) = f' ∘ e := by
      funext J
      have hrec : r.queryUpdate J.1.1 J.1.2 state = r' := J.2
      have hreply := r.queryUpdate_readState_eq P I.1 I.2 state J.1.1 (e J).2
      simp only [f, disclosureEval, f', Function.comp_apply]
      rw [← hreply]
      exact congrArg₂ (fun a b : ℝ ↦ a + b)
        (congrArg (fun s : SurvivorRecord N K ↦ ((s.retired.card - r.retired.card : ℕ) : ℝ)) hrec)
        (disclosureEval_congr_record P J.1.1 _ hrec _ _)
    rw [hfun, FinDist.uniform_expectation_equiv]
    change (FinDist.uniform {J : HardMatching.InstanceIndex N K // r'.Compatible J}).expectation
      (fun J ↦ ((r'.retired.card - r.retired.card : ℕ) : ℝ) +
        disclosureEval P J.1
          (next ((HardMatching.selectedOracle P I.1.1 I.1.2).readState state)) r' J.2) ≤ _
    rw [FinDist.expectation_const_add]
    exact add_le_add (le_refl _) (hnext I)
  have havg := FinDist.uniform_expectation_le_by_witness_fibers g f w hw hbound
  have hwconst : ∀ I : A, w I = 2 * ((N - r.retired.card : ℕ) : ℝ) * q / m := by
    intro I
    dsimp only [w, g]
    rw [hstate, queryUpdate_retired_commitState r I.1 I.2 h hh]
    simp
  have he : w = fun _ ↦ 2 * ((N - r.retired.card : ℕ) : ℝ) * q / m := funext hwconst
  rw [he, FinDist.expectation_const] at havg
  exact havg


/-- The complete adaptive disclosure bound remains valid when every
current-history marginal read is free. Only genuine candidate tests consume Q. -/
theorem uniformDisclosureEval_freeMarginal_le [Nonempty (HardVocabulary K B)]
    (P : HardLocalParameters K B) {h : History N (HardVocabulary K B)}
    (p : Program N (HardVocabulary K B) h) (r : SurvivorRecord N K)
    [Nonempty {I : HardMatching.InstanceIndex N K // r.Compatible I}]
    (hh : h.committed ⊆ r.retired) (m q R : ℕ) (hqm : q < m)
    (hcard : ∀ i : r.Survivor, m ≤ (r.candidates i.1).card)
    (hbudget : ∀ I (hI : r.Compatible I),
      p.WithinFreeMarginalBudgets (HardMatching.selectedOracle P I.1 I.2) q R) :
    uniformDisclosureEval P p r ≤ 2 * ((N - r.retired.card : ℕ) : ℝ) * q / m := by
  classical
  induction p generalizing r m q R with
  | done complete =>
      simp only [uniformDisclosureEval, disclosureEval, FinDist.expectation_const]
      positivity
  | @query h state respects next ih =>
      by_cases hstate : state = MaskedState.commitState h
      · apply uniformDisclosureEval_freeQuery_le P state respects next r hh hstate m q
        intro J
        let r' := r.queryUpdate J.1 J.2 state
        let : Nonempty {L : HardMatching.InstanceIndex N K // r'.Compatible L} :=
          ⟨⟨J.1, r.compatible_queryUpdate J.1 J.2 state⟩⟩
        have hsub : r.retired ⊆ r'.retired :=
          subset_retirementClosure_left J.1.1 r.retired (r.queryHits J.1 state)
        apply ih ((HardMatching.selectedOracle P J.1.1 J.1.2).readState state) r'
          (hh.trans hsub) m q R hqm
        · intro i
          have hi : i.1 ∉ r.retired := fun hn ↦ i.2 (hsub hn)
          have hc := hcard ⟨i.1, hi⟩
          change m ≤ (r.queryCandidates state i.1).card
          rw [hstate, queryCandidates_commitState r h hh i.1 hi]
          exact hc
        · intro L hL
          have hLold := r.compatible_queryUpdate_mono J.1 J.2 state L hL
          have hr := r.queryUpdate_readState_eq P J.1 J.2 state L hL
          rw [hr]
          have hb := hbudget L hLold
          simpa only [Program.WithinFreeMarginalBudgets, if_pos hstate] using hb
      ·
        obtain ⟨I, hI⟩ := Classical.choice (inferInstance :
          Nonempty {I : HardMatching.InstanceIndex N K // r.Compatible I})
        have hb := hbudget I hI
        simp only [Program.WithinFreeMarginalBudgets, if_neg hstate] at hb
        have hq0 : 0 < q := hb.1
        apply uniformDisclosureEval_query_le P state respects next r m q hq0 hqm hcard
        intro J
        let r' := r.queryUpdate J.1 J.2 state
        let : Nonempty {L : HardMatching.InstanceIndex N K // r'.Compatible L} :=
          ⟨⟨J.1, r.compatible_queryUpdate J.1 J.2 state⟩⟩
        have hsub : r.retired ⊆ r'.retired :=
          subset_retirementClosure_left J.1.1 r.retired (r.queryHits J.1 state)
        apply ih ((HardMatching.selectedOracle P J.1.1 J.1.2).readState state) r'
          (hh.trans hsub) (m - 1) (q - 1) R (by omega)
        · intro i
          have hi : i.1 ∉ r.retired := fun hh' ↦ i.2 (hsub hh')
          have hc := hcard ⟨i.1, hi⟩
          change m ≤ (r.candidates i.1).card at hc
          have hdel := r.card_queryCandidates_add_one_ge state i.1
          change m - 1 ≤ (r.queryCandidates state i.1).card
          omega
        · intro L hL
          have hLold := r.compatible_queryUpdate_mono J.1 J.2 state L hL
          have hr := r.queryUpdate_readState_eq P J.1 J.2 state L hL
          rw [hr]
          have hb := hbudget L hLold
          simp only [Program.WithinFreeMarginalBudgets, if_neg hstate] at hb
          exact hb.2
  | @commit h batch nonempty fresh next ih =>
      apply uniformDisclosureEval_commit_le P batch nonempty fresh next r hh m q
      intro I
      let r' := r.commitUpdate I.1 I.2 batch
      let : Nonempty {J : HardMatching.InstanceIndex N K // r'.Compatible J} :=
        ⟨⟨I.1, r.compatible_commitUpdate I.1 I.2 batch⟩⟩
      intro z
      have hsub : r.retired ⊆ r'.retired :=
        subset_retirementClosure_left I.1.1 r.retired batch
      have hh' : (h.appendBatch batch fresh z).committed ⊆ r'.retired := by
        rw [History.appendBatch_committed]
        exact Finset.union_subset (hh.trans hsub)
          (subset_retirementClosure_touched I.1.1 r.retired batch)
      apply ih z r' hh' m q (R - 1) hqm
      · intro i
        exact hcard ⟨i.1, fun hi ↦ i.2 (hsub hi)⟩
      · intro J hJ
        exact (hbudget J (r.compatible_commitUpdate_mono I.1 I.2 batch J hJ)).2 z

end HardMatching.SurvivorRecord

namespace NonlinearMatchingParameters
open HardMatching.SurvivorRecord
variable {N : ℕ}
noncomputable section

/-- The actual adaptive query-disclosure expectation has the exact Q/K
constant. Budgets cover the actual frozen oracle of every hard instance and
all possible commit values, including under the analytic midpoint process. -/
theorem midpointLedger_freeMarginal_queryVertices_expectation_le (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (Q R : ℕ) (hQ : Q < P.bankSize)
    (hbudgets : ∀ I, A.WithinFreeMarginalBudgets (P.hardFamily I).oracle Q R) :
    (P.midpointJoint A w).expectation
      (fun outcome ↦ ((P.midpointLedger A w outcome).queryVertices : ℝ)) ≤
      2 * (N : ℝ) * Q / P.bankSize := by
  let := P.vocabularyNonempty
  let := P.initialFiberNonempty
  rw [P.midpointLedger_queryVertices_eq_initial_disclosure A w]
  have hbound := uniformDisclosureEval_freeMarginal_le P.toHardLocal (P.commonInitialProgram A w)
    (initial N P.bankSize) (by simp [History.empty]) P.bankSize Q R hQ
    (by intro i; simp [initial])
    (by
      intro I _
      rw [← P.hard_initialProgram_eq_common A w I]
      exact hbudgets I w)
  simpa only [initial, Finset.card_empty, Nat.sub_zero] using hbound

/-- With at most K/8 extra queries, the expected number of query-retired
edges is at most N/8 under the actual instance--midpoint law. This is the
remaining numerical input to the concrete adaptive collision-tail theorem. -/
theorem midpointLedger_freeMarginal_disclosure_le_eighth (P : NonlinearMatchingParameters N)
    {Seed : Type*} (A : Sampler N (HardVocabulary P.bankSize P.backgroundSize) Seed)
    (w : Seed) (Q R : ℕ) (hQ : Q ≤ P.bankSize / 8)
    (hbudgets : ∀ I, A.WithinFreeMarginalBudgets (P.hardFamily I).oracle Q R) :
    (∑ outcome, P.midpointJoint A w outcome *
      ((P.midpointLedger A w outcome).queryVertices : ℝ) / 2) ≤ (N : ℝ) / 8 := by
  have hK : 0 < P.bankSize := P.bank_nonempty
  have hQlt : Q < P.bankSize := by omega
  have hbound := P.midpointLedger_freeMarginal_queryVertices_expectation_le A w Q R hQlt hbudgets
  have hratio : (Q : ℝ) / P.bankSize ≤ 1 / 8 := by
    have hKr : (0 : ℝ) < P.bankSize := by exact_mod_cast hK
    apply (div_le_iff₀ hKr).mpr
    have hnat : 8 * Q ≤ P.bankSize := by omega
    have hreal : (8 : ℝ) * Q ≤ P.bankSize := by exact_mod_cast hnat
    linarith
  have hscale := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ 2 * N by positivity)
  rw [← Finset.sum_div]
  change (P.midpointJoint A w).expectation
    (fun outcome ↦ ((P.midpointLedger A w outcome).queryVertices : ℝ)) / 2 ≤ _
  have hupper : 2 * (N : ℝ) * Q / P.bankSize ≤ (N : ℝ) / 4 := by
    calc
      _ = 2 * (N : ℝ) * ((Q : ℝ) / P.bankSize) := by ring
      _ ≤ 2 * (N : ℝ) * (1 / 8) := hscale
      _ = _ := by ring
  linarith

end
end NonlinearMatchingParameters
end ForestSampling
