import ForestSampling.CompensatedLaplace
import ForestSampling.SurvivorLaplace

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace HardMatching
namespace SurvivorRecord

variable {N K B : ℕ} [Nonempty (HardVocabulary K B)]

/-- The midpoint compensation average under the actual compatible-instance
fiber at the current operation boundary. -/
noncomputable def uniformLaplaceEval (P : HardLocalParameters K B)
    {h : History N (HardVocabulary K B)} (p : Program N (HardVocabulary K B) h)
    (r : SurvivorRecord N K) [Nonempty {I : InstanceIndex N K // r.Compatible I}] : ℝ :=
  (FinDist.uniform {I : InstanceIndex N K // r.Compatible I}).expectation
    (fun I ↦ laplaceEval P I.1 p r I.2)

/-- The compensation factor is fixed once a commit retirement record is
known: that record exposes every edge touching the active batch. -/
theorem laplaceFactor_eq_of_commitUpdate (r : SurvivorRecord N K)
    (I J : InstanceIndex N K) (hI : r.Compatible I) (hJ : r.Compatible J)
    (batch : Finset (Position N))
    (hrecord : r.commitUpdate I hI batch = r.commitUpdate J hJ batch) :
    r.laplaceFactor I batch = r.laplaceFactor J batch := by
  have hJ' : (r.commitUpdate I hI batch).Compatible J := by
    rw [hrecord]
    exact r.compatible_commitUpdate J hJ batch
  have hagree := (r.compatible_commitUpdate I hI batch).agreeOnRegion hJ'
  have hmates : ∀ i ∈ batch \ r.retired, I.1.mate i = J.1.mate i := by
    intro i hi
    exact hagree.1 i (subset_retirementClosure_touched I.1 r.retired batch (Finset.mem_sdiff.mp hi).1)
  have hcount : I.1.internalEdgeCount (batch \ r.retired) =
      J.1.internalEdgeCount (batch \ r.retired) := by
    unfold PerfectMatching.internalEdgeCount
    congr 1
    ext i
    by_cases hi : i ∈ batch \ r.retired
    · simp [PerfectMatching.representatives, hmates i hi]
    · simp only [Finset.mem_filter]
      constructor <;> rintro ⟨_, hiS, _⟩ <;> exact False.elim (hi hiS)
  simp only [laplaceFactor, hcount]


/-- Equal analytic records give equal evaluations independently of the
proof witnessing compatibility with the fixed hidden instance. -/
theorem laplaceEval_congr_record (P : HardLocalParameters K B) (I : InstanceIndex N K)
    {h : History N (HardVocabulary K B)} (p : Program N (HardVocabulary K B) h)
    {r s : SurvivorRecord N K} (heq : r = s) (hr : r.Compatible I) (hs : s.Compatible I) :
    laplaceEval P I p r hr = laplaceEval P I p s hs := by
  cases heq
  rfl

/-- Query retirement preserves a uniform fiber average because each new
record determines the actual frozen reply and hence the next program branch. -/
theorem uniformLaplaceEval_query_le_one (P : HardLocalParameters K B)
    {h : History N (HardVocabulary K B)} (state : MaskedState N (HardVocabulary K B))
    (respects : state.RespectsHistory h)
    (next : (MaskedPosition state → FinDist (HardVocabulary K B)) →
      Program N (HardVocabulary K B) h)
    (r : SurvivorRecord N K) [Nonempty {I : InstanceIndex N K // r.Compatible I}]
    (hh : h.committed ⊆ r.retired)
    (hnext : ∀ reply (r' : SurvivorRecord N K)
      (hNE : Nonempty {I : InstanceIndex N K // r'.Compatible I}),
      let := hNE
      h.committed ⊆ r'.retired → uniformLaplaceEval P (next reply) r' ≤ 1) :
    uniformLaplaceEval P (.query state respects next) r ≤ 1 := by
  classical
  let A := {I : InstanceIndex N K // r.Compatible I}
  let g : A → SurvivorRecord N K := fun I ↦ r.queryUpdate I.1 I.2 state
  let f : A → ℝ := fun I ↦ laplaceEval P I.1 (.query state respects next) r I.2
  have hbound : ∀ I : A, letI : Nonempty {J : A // g J = g I} := ⟨⟨I, rfl⟩⟩
      (FinDist.uniform {J : A // g J = g I}).expectation (fun J ↦ f J.1) ≤ (1 : ℝ) := by
    intro I
    let r' := r.queryUpdate I.1 I.2 state
    let : Nonempty {J : A // g J = g I} := ⟨⟨I, rfl⟩⟩
    let hNE : Nonempty {J : InstanceIndex N K // r'.Compatible J} :=
      ⟨⟨I.1, r.compatible_queryUpdate I.1 I.2 state⟩⟩
    let := hNE
    let e := r.queryRetirementFiberEquiv I.1 I.2 state
    let f' : {J : InstanceIndex N K // r'.Compatible J} → ℝ := fun J ↦
      laplaceEval P J.1 (next ((selectedOracle P I.1.1 I.1.2).readState state)) r' J.2
    have hfun : (fun J : {J : A // g J = g I} ↦ f J.1) = f' ∘ e := by
      funext J
      have hrec : r.queryUpdate J.1.1 J.1.2 state = r' := J.2
      have hreply := r.queryUpdate_readState_eq P I.1 I.2 state J.1.1 (e J).2
      simp only [f, laplaceEval, f', Function.comp_apply]
      rw [← hreply]
      exact laplaceEval_congr_record P J.1.1 _ hrec _ _
    rw [hfun, FinDist.uniform_expectation_equiv]
    exact hnext _ r' hNE (hh.trans (subset_retirementClosure_left I.1.1 r.retired (r.queryHits I.1 state)))
  have hx := FinDist.uniform_expectation_le_by_witness_fibers g f (fun _ ↦ 1)
    (fun _ _ _ ↦ rfl) hbound
  simpa only [FinDist.expectation_const, f, A, uniformLaplaceEval] using hx

/-- Commit retirement exposes the local factor and normalized batch kernel.
The remaining compatible hidden data still have the full uniform fiber law. -/
theorem uniformLaplaceEval_commit_le_one (P : HardLocalParameters K B)
    {h : History N (HardVocabulary K B)} (batch : Finset (Position N))
    (nonempty : batch.Nonempty) (fresh : batch ⊆ h.uncommitted)
    (next : (z : batch → HardVocabulary K B) →
      Program N (HardVocabulary K B) (h.appendBatch batch fresh z))
    (r : SurvivorRecord N K) [Nonempty {I : InstanceIndex N K // r.Compatible I}]
    (hh : h.committed ⊆ r.retired)
    (hnext : ∀ z (r' : SurvivorRecord N K)
      (hNE : Nonempty {I : InstanceIndex N K // r'.Compatible I}),
      let := hNE
      (h.appendBatch batch fresh z).committed ⊆ r'.retired →
        uniformLaplaceEval P (next z) r' ≤ 1) :
    uniformLaplaceEval P (.commit batch nonempty fresh next) r ≤ 1 := by
  classical
  let A := {I : InstanceIndex N K // r.Compatible I}
  let g : A → SurvivorRecord N K := fun I ↦ r.commitUpdate I.1 I.2 batch
  let f : A → ℝ := fun I ↦ laplaceEval P I.1 (.commit batch nonempty fresh next) r I.2
  let w : A → ℝ := fun I ↦ r.laplaceFactor I.1 batch
  have hw : ∀ I J, g I = g J → w I = w J := by
    intro I J hrec
    exact r.laplaceFactor_eq_of_commitUpdate I.1 J.1 I.2 J.2 batch hrec
  have hbound : ∀ I : A, letI : Nonempty {J : A // g J = g I} := ⟨⟨I, rfl⟩⟩
      (FinDist.uniform {J : A // g J = g I}).expectation (fun J ↦ f J.1) ≤ w I := by
    intro I
    let r' := r.commitUpdate I.1 I.2 batch
    let : Nonempty {J : A // g J = g I} := ⟨⟨I, rfl⟩⟩
    let hNE : Nonempty {J : InstanceIndex N K // r'.Compatible J} :=
      ⟨⟨I.1, r.compatible_commitUpdate I.1 I.2 batch⟩⟩
    let := hNE
    let e := r.commitRetirementFiberEquiv I.1 I.2 batch
    let q := (instanceMidpointKernel P I.1).law h batch fresh
    let future : {J : InstanceIndex N K // r'.Compatible J} →
        (batch → HardVocabulary K B) → ℝ := fun J z ↦ laplaceEval P J.1 (next z) r' J.2
    let f' : {J : InstanceIndex N K // r'.Compatible J} → ℝ :=
      fun J ↦ w I * q.expectation (future J)
    have hfun : (fun J : {J : A // g J = g I} ↦ f J.1) = f' ∘ e := by
      funext J
      have hrec : r.commitUpdate J.1.1 J.1.2 batch = r' := J.2
      have hweight : r.laplaceFactor J.1.1 batch = w I := hw J.1 I J.2
      have hkernel := r.commitUpdate_midpointBatchLaw_eq P I.1 I.2 h hh batch fresh J.1.1 (e J).2
      simp only [f, laplaceEval, f', future, Function.comp_apply]
      change r.laplaceFactor J.1.1 batch *
        ((instanceMidpointKernel P J.1.1).law h batch fresh).expectation _ = _
      rw [hweight]
      change (instanceMidpointKernel P I.1).law h batch fresh =
        (instanceMidpointKernel P J.1.1).law h batch fresh at hkernel
      rw [← hkernel]
      apply congrArg (fun F ↦ w I * q.expectation F)
      funext z
      exact laplaceEval_congr_record P J.1.1 (next z) hrec _ _
    rw [hfun, FinDist.uniform_expectation_equiv]
    change (FinDist.uniform {J : InstanceIndex N K // r'.Compatible J}).expectation
      (fun J ↦ w I * q.expectation (future J)) ≤ w I
    rw [FinDist.expectation_const_mul, FinDist.expectation_comm]
    have hhist : ∀ z, (h.appendBatch batch fresh z).committed ⊆ r'.retired := by
      intro z
      rw [History.appendBatch_committed]
      exact Finset.union_subset
        (hh.trans (subset_retirementClosure_left I.1.1 r.retired batch))
        (subset_retirementClosure_touched I.1.1 r.retired batch)
    have heach : ∀ z,
        (FinDist.uniform {J : InstanceIndex N K // r'.Compatible J}).expectation
          (fun J ↦ future J z) ≤ 1 := by
      intro z
      exact hnext z r' hNE (hhist z)
    have havg := q.expectation_mono heach
    rw [FinDist.expectation_const] at havg
    exact (mul_le_mul_of_nonneg_left havg (Real.exp_nonneg _)).trans_eq (mul_one _)
  have hx := FinDist.uniform_expectation_le_by_witness_fibers g f w hw hbound
  apply hx.trans
  exact r.uniform_fiber_commit_compensated batch

/-- The full compensated collision moment is at most one for the actual
adaptive midpoint execution. This proves the structural induction from
concrete retirement fibers and their actual normalized kernels. -/
theorem uniformLaplaceEval_le_one (P : HardLocalParameters K B)
    {h : History N (HardVocabulary K B)} (p : Program N (HardVocabulary K B) h)
    (r : SurvivorRecord N K) [Nonempty {I : InstanceIndex N K // r.Compatible I}]
    (hh : h.committed ⊆ r.retired) : uniformLaplaceEval P p r ≤ 1 := by
  induction p generalizing r with
  | done complete =>
      simp [uniformLaplaceEval, laplaceEval, FinDist.expectation_const]
  | query state respects next ih =>
      apply uniformLaplaceEval_query_le_one P state respects next r hh
      intro reply r' hNE
      let := hNE
      dsimp only
      intro hh'
      exact ih reply r' hh'
  | commit batch nonempty fresh next ih =>
      apply uniformLaplaceEval_commit_le_one P batch nonempty fresh next r hh
      intro z r' hNE
      let := hNE
      dsimp only
      intro hh'
      exact ih z r' hh'


end SurvivorRecord
end HardMatching
end ForestSampling
