import ForestSampling.MidpointSurvivor
import ForestSampling.FiniteFibers
import ForestSampling.OracleBudgets

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

/-- Expected cardinalities of finite random subsets equal the sum of their
actual inclusion probabilities. -/
theorem expectation_card_filter {α ι : Type*} [Fintype α] [DecidableEq ι]
    (p : FinDist α) (s : Finset ι) (E : α → ι → Prop) [∀ a, DecidablePred (E a)] :
    p.expectation (fun a ↦ ((s.filter (E a)).card : ℝ)) =
      ∑ i ∈ s, p.eventMass (fun a ↦ E a i) := by
  classical
  have hcard (a : α) : ((s.filter (E a)).card : ℝ) =
      ∑ i ∈ s, if E a i then (1 : ℝ) else 0 := by simp
  simp_rw [hcard]
  unfold expectation eventMass
  simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  exact Finset.sum_comm

/-- Adding a constant reward to every outcome adds that constant to its
finite expectation. -/
theorem expectation_const_add {α : Type*} [Fintype α] (p : FinDist α)
    (c : ℝ) (f : α → ℝ) :
    p.expectation (fun a ↦ c + f a) = c + p.expectation f := by
  unfold expectation
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, p.sum_mass, one_mul]

/-- Finite expectation respects an affine scalar expression. -/
theorem expectation_affine {α : Type*} [Fintype α] (p : FinDist α)
    (c d : ℝ) (f : α → ℝ) :
    p.expectation (fun a ↦ c + d * f a) = c + d * p.expectation f := by
  rw [expectation_const_add, expectation_const_mul]

end FinDist

namespace HardMatching.SurvivorRecord
variable {N K B : ℕ}

/-- Uniform survivor triggers bound the expected number of actual query
hits. The candidate minimum is tracked explicitly through later recursion. -/
theorem uniform_expected_queryHits_le (r : SurvivorRecord N K)
    [Nonempty {I : HardMatching.InstanceIndex N K // r.Compatible I}]
    (state : MaskedState N (HardVocabulary K B)) (m : ℕ) (hm : 0 < m)
    (hcard : ∀ i : r.Survivor, m ≤ (r.candidates i.1).card) :
    (FinDist.uniform {I : HardMatching.InstanceIndex N K // r.Compatible I}).expectation
      (fun I ↦ ((r.queryHits I.1 state).card : ℝ)) ≤
      ((N - r.retired.card : ℕ) : ℝ) / m := by
  classical
  unfold queryHits
  rw [FinDist.expectation_card_filter]
  calc
    _ ≤ ∑ i ∈ (Finset.univ \ r.retired), ((m : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ∉ r.retired := (Finset.mem_sdiff.mp hi).2
      apply (r.uniform_fiber_hit_probability_le state ⟨i, hi'⟩).trans
      have hpos : (0 : ℝ) < m := by exact_mod_cast hm
      have hle : (m : ℝ) ≤ (r.candidates i).card := by exact_mod_cast hcard ⟨i, hi'⟩
      simpa only [one_div] using one_div_le_one_div_of_le hpos hle
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul,
        Finset.card_sdiff_of_subset (Finset.subset_univ r.retired), Finset.card_univ,
        Fintype.card_fin]
      rfl

/-- Query retirement exposes at least every hit source and at most its two
edge endpoints. The bounds count actual newly retired vertices. -/
theorem queryUpdate_card_bounds (r : SurvivorRecord N K)
    (I : HardMatching.InstanceIndex N K) (hI : r.Compatible I)
    (state : MaskedState N (HardVocabulary K B)) :
    let d := (r.queryUpdate I hI state).retired.card - r.retired.card
    (r.queryHits I state).card ≤ d ∧ d ≤ 2 * (r.queryHits I state).card := by
  classical
  let H := r.queryHits I state
  let R := (r.queryUpdate I hI state).retired
  have hs : r.retired ⊆ R := subset_retirementClosure_left I.1 r.retired H
  have hH : H ⊆ R \ r.retired := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨subset_retirementClosure_touched I.1 r.retired H hi,
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).1).2⟩
  have hdiff : H \ r.retired = H := by
    apply Finset.sdiff_eq_self_iff_disjoint.mpr
    exact Finset.disjoint_left.mpr (fun i hi hr ↦
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).1).2 hr)
  have hc := I.1.retirement_card_ledger r.retired H hI.regionClosed
  rw [hdiff] at hc
  have hsmall := Finset.card_le_card hH
  rw [Finset.card_sdiff_of_subset hs] at hsmall
  change R.card + 2 * I.1.internalEdgeCount H = r.retired.card + 2 * H.card at hc
  exact ⟨hsmall, by change R.card - r.retired.card ≤ 2 * H.card; omega⟩


/-- The one-query potential inequality combines the actual hit bound with
whole-edge retirement. The potential uses the number of still-active vertices,
which preserves the exact Q/K constant across adaptive queries. -/
theorem uniform_query_potential_le (r : SurvivorRecord N K)
    [Nonempty {I : HardMatching.InstanceIndex N K // r.Compatible I}]
    (state : MaskedState N (HardVocabulary K B)) (m q : ℕ)
    (hq0 : 0 < q) (hqm : q < m)
    (hcard : ∀ i : r.Survivor, m ≤ (r.candidates i.1).card) :
    (FinDist.uniform {I : HardMatching.InstanceIndex N K // r.Compatible I}).expectation
      (fun I ↦
        (((r.queryUpdate I.1 I.2 state).retired.card - r.retired.card : ℕ) : ℝ) +
        2 * ((N - (r.queryUpdate I.1 I.2 state).retired.card : ℕ) : ℝ) *
          (q - 1 : ℕ) / (m - 1 : ℕ)) ≤
      2 * ((N - r.retired.card : ℕ) : ℝ) * q / m := by
  classical
  let n : ℝ := (N - r.retired.card : ℕ)
  let c : ℝ := (q - 1 : ℕ) / (m - 1 : ℕ)
  have hm0 : 0 < m := by omega
  have hm1 : 0 < m - 1 := by omega
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hm1r : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hm1
  have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hm1r.le
  have hc1 : c ≤ 1 := (div_le_one hm1r).mpr (by exact_mod_cast (show q - 1 ≤ m - 1 by omega))
  have hbound (I : {I : HardMatching.InstanceIndex N K // r.Compatible I}) :
      (((r.queryUpdate I.1 I.2 state).retired.card - r.retired.card : ℕ) : ℝ) +
        2 * ((N - (r.queryUpdate I.1 I.2 state).retired.card : ℕ) : ℝ) *
          (q - 1 : ℕ) / (m - 1 : ℕ) ≤
      2 * n * c + 2 * (1 - c) * ((r.queryHits I.1 state).card : ℝ) := by
    let d := (r.queryUpdate I.1 I.2 state).retired.card - r.retired.card
    let n' := N - (r.queryUpdate I.1 I.2 state).retired.card
    have hb := r.queryUpdate_card_bounds I.1 I.2 state
    have hsmall : (r.retired.card : ℕ) ≤ (r.queryUpdate I.1 I.2 state).retired.card :=
      Finset.card_le_card (subset_retirementClosure_left I.1.1 r.retired (r.queryHits I.1 state))
    have htotal : (r.queryUpdate I.1 I.2 state).retired.card ≤ N := by
      simpa using Finset.card_le_univ (r.queryUpdate I.1 I.2 state).retired
    have heq : n' + d = N - r.retired.card := by omega
    have heqr : (n' : ℝ) + d = n := by dsimp only [n]; exact_mod_cast heq
    have hlow : ((r.queryHits I.1 state).card : ℝ) ≤ d := by exact_mod_cast hb.1
    have hhigh : (d : ℝ) ≤ 2 * ((r.queryHits I.1 state).card : ℝ) := by exact_mod_cast hb.2
    change (d : ℝ) + 2 * (n' : ℝ) * (q - 1 : ℕ) / (m - 1 : ℕ) ≤ _
    have hmul : 2 * (n' : ℝ) * (q - 1 : ℕ) / (m - 1 : ℕ) = 2 * n' * c := by
      dsimp [c]; ring
    rw [hmul]
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hlow)]
  calc
    _ ≤ (FinDist.uniform {I : HardMatching.InstanceIndex N K // r.Compatible I}).expectation
        (fun I ↦ 2 * n * c + 2 * (1 - c) * ((r.queryHits I.1 state).card : ℝ)) :=
      FinDist.expectation_mono _ hbound
    _ = 2 * n * c + 2 * (1 - c) *
        (FinDist.uniform {I : HardMatching.InstanceIndex N K // r.Compatible I}).expectation
          (fun I ↦ ((r.queryHits I.1 state).card : ℝ)) := FinDist.expectation_affine _ _ _ _
    _ ≤ 2 * n * c + 2 * (1 - c) * (n / m) := by
      have havg := mul_le_mul_of_nonneg_left
        (r.uniform_expected_queryHits_le state m hm0 hcard)
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (sub_nonneg.mpr hc1))
      dsimp only [n]
      linarith
    _ = _ := by
      have hmr1 : (0 : ℝ) < (m : ℝ) - 1 := by
        have hgt : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
        linarith
      dsimp [c, n]
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub (by omega : 1 ≤ m)]
      push_cast
      field_simp [ne_of_gt hmr, ne_of_gt hmr1]
      <;> ring

/-- The expected number of vertices ultimately disclosed by extra queries
in the actual midpoint program on a fixed hidden instance. -/
noncomputable def disclosureEval [Nonempty (HardVocabulary K B)]
    (P : HardLocalParameters K B) (I : HardMatching.InstanceIndex N K) :
    {h : History N (HardVocabulary K B)} → (p : Program N (HardVocabulary K B) h) →
    (r : SurvivorRecord N K) → r.Compatible I → ℝ
  | _, .done _, _, _ => 0
  | _, .query state _ next, r, hI =>
      (((r.queryUpdate I hI state).retired.card - r.retired.card : ℕ) : ℝ) +
      disclosureEval P I (next ((HardMatching.selectedOracle P I.1 I.2).readState state))
        (r.queryUpdate I hI state) (r.compatible_queryUpdate I hI state)
  | h, .commit batch _ fresh next, r, hI =>
      ((instanceMidpointKernel P I).law h batch fresh).expectation (fun z ↦
        disclosureEval P I (next z) (r.commitUpdate I hI batch)
          (r.compatible_commitUpdate I hI batch))

/-- Equal records give equal recursive disclosure evaluations; the
compatibility certificates are propositions and carry no computational data. -/
theorem disclosureEval_congr_record [Nonempty (HardVocabulary K B)]
    (P : HardLocalParameters K B) (I : HardMatching.InstanceIndex N K)
    {h : History N (HardVocabulary K B)} (p : Program N (HardVocabulary K B) h)
    {r s : SurvivorRecord N K} (hrs : r = s) (hr : r.Compatible I) (hs : s.Compatible I) :
    disclosureEval P I p r hr = disclosureEval P I p s hs := by
  cases hrs
  rfl

/-- This recursion is exactly the query-vertex counter in the already
constructed actual retained-path retirement ledger. -/
theorem disclosureEval_eq_retained_expectation [Nonempty (HardVocabulary K B)]
    (P : HardLocalParameters K B) (I : HardMatching.InstanceIndex N K)
    {h : History N (HardVocabulary K B)} (p : Program N (HardVocabulary K B) h)
    (r : SurvivorRecord N K) (hI : r.Compatible I) :
    disclosureEval P I p r hI =
      (Program.retainedLaw (HardMatching.selectedOracle P I.1 I.2) (instanceMidpointKernel P I) p).expectation
        (fun path ↦ ((Program.retirementLedger I (HardMatching.selectedOracle P I.1 I.2)
          p r hI path).queryVertices : ℝ)) := by
  induction p generalizing r with
  | done complete => simp [disclosureEval, Program.retirementLedger, FinDist.expectation]
  | query state respects next ih =>
      simp only [disclosureEval]
      rw [ih]
      symm
      simp only [Program.retirementLedger, Nat.cast_add]
      exact FinDist.expectation_const_add
        (Program.retainedLaw (HardMatching.selectedOracle P I.1 I.2) (instanceMidpointKernel P I)
          (next ((HardMatching.selectedOracle P I.1 I.2).readState state))) _ _
  | @commit h batch nonempty fresh next ih =>
      simp only [disclosureEval]
      simp_rw [ih]
      symm
      exact FinDist.expectation_sigmaJoint _ _ _

/-- Average the actual query disclosure recursion over the complete current
compatible-instance fiber. -/
noncomputable def uniformDisclosureEval [Nonempty (HardVocabulary K B)]
    (P : HardLocalParameters K B) {h : History N (HardVocabulary K B)}
    (p : Program N (HardVocabulary K B) h) (r : SurvivorRecord N K)
    [Nonempty {I : HardMatching.InstanceIndex N K // r.Compatible I}] : ℝ :=
  (FinDist.uniform {I : HardMatching.InstanceIndex N K // r.Compatible I}).expectation
    (fun I ↦ disclosureEval P I.1 p r I.2)

/-- Query-fiber disintegration converts the recursively proved future
potential into the current one-query potential. -/
theorem uniformDisclosureEval_query_le [Nonempty (HardVocabulary K B)]
    (P : HardLocalParameters K B) {h : History N (HardVocabulary K B)}
    (state : MaskedState N (HardVocabulary K B)) (respects : state.RespectsHistory h)
    (next : (MaskedPosition state → FinDist (HardVocabulary K B)) →
      Program N (HardVocabulary K B) h)
    (r : SurvivorRecord N K)
    [Nonempty {I : HardMatching.InstanceIndex N K // r.Compatible I}]
    (m q : ℕ) (hq0 : 0 < q) (hqm : q < m)
    (hcard : ∀ i : r.Survivor, m ≤ (r.candidates i.1).card)
    (hnext : ∀ I : {I : HardMatching.InstanceIndex N K // r.Compatible I},
      letI : Nonempty {J : HardMatching.InstanceIndex N K //
        (r.queryUpdate I.1 I.2 state).Compatible J} :=
        ⟨⟨I.1, r.compatible_queryUpdate I.1 I.2 state⟩⟩
      uniformDisclosureEval P
        (next ((HardMatching.selectedOracle P I.1.1 I.1.2).readState state))
        (r.queryUpdate I.1 I.2 state) ≤
        2 * ((N - (r.queryUpdate I.1 I.2 state).retired.card : ℕ) : ℝ) *
          (q - 1 : ℕ) / (m - 1 : ℕ)) :
    uniformDisclosureEval P (.query state respects next) r ≤
      2 * ((N - r.retired.card : ℕ) : ℝ) * q / m := by
  classical
  let A := {I : HardMatching.InstanceIndex N K // r.Compatible I}
  let g : A → SurvivorRecord N K := fun I ↦ r.queryUpdate I.1 I.2 state
  let f : A → ℝ := fun I ↦ disclosureEval P I.1 (.query state respects next) r I.2
  let w : A → ℝ := fun I ↦
    (((g I).retired.card - r.retired.card : ℕ) : ℝ) +
      2 * ((N - (g I).retired.card : ℕ) : ℝ) * (q - 1 : ℕ) / (m - 1 : ℕ)
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
  exact havg.trans (r.uniform_query_potential_le state m q hq0 hqm hcard)

/-- Commit-fiber disintegration preserves the query potential. It averages
the actual common midpoint batch law after the real retirement disclosure. -/
theorem uniformDisclosureEval_commit_le [Nonempty (HardVocabulary K B)]
    (P : HardLocalParameters K B) {h : History N (HardVocabulary K B)}
    (batch : Finset (Position N)) (nonempty : batch.Nonempty)
    (fresh : batch ⊆ h.uncommitted)
    (next : (z : batch → HardVocabulary K B) →
      Program N (HardVocabulary K B) (h.appendBatch batch fresh z))
    (r : SurvivorRecord N K)
    [Nonempty {I : HardMatching.InstanceIndex N K // r.Compatible I}]
    (hh : h.committed ⊆ r.retired) (m q : ℕ)
    (hnext : ∀ I : {I : HardMatching.InstanceIndex N K // r.Compatible I},
      letI : Nonempty {J : HardMatching.InstanceIndex N K //
        (r.commitUpdate I.1 I.2 batch).Compatible J} :=
        ⟨⟨I.1, r.compatible_commitUpdate I.1 I.2 batch⟩⟩
      ∀ z, uniformDisclosureEval P (next z) (r.commitUpdate I.1 I.2 batch) ≤
        2 * ((N - (r.commitUpdate I.1 I.2 batch).retired.card : ℕ) : ℝ) * q / m) :
    uniformDisclosureEval P (.commit batch nonempty fresh next) r ≤
      2 * ((N - r.retired.card : ℕ) : ℝ) * q / m := by
  classical
  let A := {I : HardMatching.InstanceIndex N K // r.Compatible I}
  let g : A → SurvivorRecord N K := fun I ↦ r.commitUpdate I.1 I.2 batch
  let f : A → ℝ := fun I ↦ disclosureEval P I.1 (.commit batch nonempty fresh next) r I.2
  let c : ℝ := 2 * ((N - r.retired.card : ℕ) : ℝ) * q / m
  have hbound : ∀ I : A, letI : Nonempty {J : A // g J = g I} := ⟨⟨I, rfl⟩⟩
      (FinDist.uniform {J : A // g J = g I}).expectation (fun J ↦ f J.1) ≤ c := by
    intro I
    let r' := r.commitUpdate I.1 I.2 batch
    let : Nonempty {J : A // g J = g I} := ⟨⟨I, rfl⟩⟩
    let : Nonempty {J : HardMatching.InstanceIndex N K // r'.Compatible J} :=
      ⟨⟨I.1, r.compatible_commitUpdate I.1 I.2 batch⟩⟩
    let e := r.commitRetirementFiberEquiv I.1 I.2 batch
    let law := (instanceMidpointKernel P I.1).law h batch fresh
    let future : {J : HardMatching.InstanceIndex N K // r'.Compatible J} →
        (batch → HardVocabulary K B) → ℝ := fun J z ↦ disclosureEval P J.1 (next z) r' J.2
    let f' : {J : HardMatching.InstanceIndex N K // r'.Compatible J} → ℝ :=
      fun J ↦ law.expectation (future J)
    have hfun : (fun J : {J : A // g J = g I} ↦ f J.1) = f' ∘ e := by
      funext J
      have hrec : r.commitUpdate J.1.1 J.1.2 batch = r' := J.2
      have hkernel := r.commitUpdate_midpointBatchLaw_eq P I.1 I.2 h hh batch fresh J.1.1 (e J).2
      simp only [f, disclosureEval, f', future, Function.comp_apply]
      change ((instanceMidpointKernel P J.1.1).law h batch fresh).expectation _ = _
      change (instanceMidpointKernel P I.1).law h batch fresh =
        (instanceMidpointKernel P J.1.1).law h batch fresh at hkernel
      rw [← hkernel]
      apply congrArg law.expectation
      funext z
      exact disclosureEval_congr_record P J.1.1 (next z) hrec _ _
    rw [hfun, FinDist.uniform_expectation_equiv]
    change (FinDist.uniform {J : HardMatching.InstanceIndex N K // r'.Compatible J}).expectation
      (fun J ↦ law.expectation (future J)) ≤ c
    rw [FinDist.expectation_comm]
    have hfuture : ∀ z,
        (FinDist.uniform {J : HardMatching.InstanceIndex N K // r'.Compatible J}).expectation
          (fun J ↦ future J z) ≤ c := by
      intro z
      apply (hnext I z).trans
      have hsub : r.retired.card ≤ r'.retired.card :=
        Finset.card_le_card (subset_retirementClosure_left I.1.1 r.retired batch)
      have hn : ((N - r'.retired.card : ℕ) : ℝ) ≤ ((N - r.retired.card : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le_sub_left hsub N
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (Nat.cast_nonneg q))
        (Nat.cast_nonneg m)
    have havg := law.expectation_mono hfuture
    rwa [FinDist.expectation_const] at havg
  have havg := FinDist.uniform_expectation_le_by_witness_fibers g f (fun _ ↦ c)
    (fun _ _ _ ↦ rfl) hbound
  simpa only [FinDist.expectation_const, f, A, c, uniformDisclosureEval] using havg

/-- The complete actual midpoint execution satisfies the exact query
potential bound. Budgets are checked only against each compatible instance's
real frozen oracle, and still cover every possible commit assignment. -/
theorem uniformDisclosureEval_le [Nonempty (HardVocabulary K B)]
    (P : HardLocalParameters K B) {h : History N (HardVocabulary K B)}
    (p : Program N (HardVocabulary K B) h) (r : SurvivorRecord N K)
    [Nonempty {I : HardMatching.InstanceIndex N K // r.Compatible I}]
    (hh : h.committed ⊆ r.retired) (m q R : ℕ) (hqm : q < m)
    (hcard : ∀ i : r.Survivor, m ≤ (r.candidates i.1).card)
    (hbudget : ∀ I (hI : r.Compatible I),
      p.WithinOracleBudgets (HardMatching.selectedOracle P I.1 I.2) q R) :
    uniformDisclosureEval P p r ≤ 2 * ((N - r.retired.card : ℕ) : ℝ) * q / m := by
  classical
  induction p generalizing r m q R with
  | done complete =>
      simp only [uniformDisclosureEval, disclosureEval, FinDist.expectation_const]
      positivity
  | query state respects next ih =>
      obtain ⟨I, hI⟩ := Classical.choice (inferInstance :
        Nonempty {I : HardMatching.InstanceIndex N K // r.Compatible I})
      have hq0 : 0 < q := (hbudget I hI).1
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
        exact (hbudget L hLold).2
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
end ForestSampling
