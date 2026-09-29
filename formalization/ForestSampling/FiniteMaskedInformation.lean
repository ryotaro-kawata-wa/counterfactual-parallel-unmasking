import ForestSampling.FiniteChannelInformation
import ForestSampling.PairConditionals

set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators

namespace ForestSampling.FinDist
noncomputable section

variable {ι α β γ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-- Independent observation masks, sampled conditionally on the complete
configuration using a fresh erasure coin at every coordinate. -/
def maskChannel (x : ι → α) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    FinDist (ι → Option α) := piProduct fun i ↦ (dirac (x i)).erase q hq0 hq1

/-- The actual independently masked law, including both token randomness
and all independent mask randomness. -/
def maskedLaw (p : FinDist (ι → α)) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    FinDist (ι → Option α) := p.bind (fun x ↦ maskChannel x q hq0 hq1)

/-- The probability of one mask pattern, with its retained values omitted. -/
def maskWeight (y : ι → Option α) (q : ℝ) : ℝ :=
  ∏ i, if (y i).isSome then q else 1-q

def MaskAgrees (y : ι → Option α) (x : ι → α) : Prop :=
  ∀ i a, y i = some a → x i = a

instance (y : ι → Option α) (x : ι → α) : Decidable (MaskAgrees y x) :=
  Classical.propDecidable _

theorem maskWeight_pos (y : ι → Option α) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < maskWeight y q := by
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact hq0
  · linarith

/-- Once the visible values agree, an observation's likelihood depends
only on its mask pattern. An incompatible value has zero likelihood. -/
theorem maskChannel_apply (x : ι → α) (y : ι → Option α)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    maskChannel x q hq0 hq1 y = if MaskAgrees y x then maskWeight y q else 0 := by
  classical
  by_cases h : MaskAgrees y x
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    cases hy : y i with
    | none => simp [hy, erase]
    | some a => simp [hy, erase, dirac_apply, h i a hy]
  · rw [if_neg h]
    unfold MaskAgrees at h
    push_neg at h
    obtain ⟨i,a,hya,hia⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hya, erase, dirac_apply, hia, Ne.symm hia]

theorem maskedLaw_apply (p : FinDist (ι → α)) (y : ι → Option α)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    p.maskedLaw q hq0 hq1 y = maskWeight y q * p.eventMass (MaskAgrees y) := by
  simp only [maskedLaw, bind_apply, maskChannel_apply, eventMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> ring

/-- Retain both an actual channel observation and an arbitrary readout of
the underlying sample, without replacing their joint law by marginals. -/
def observationJoint (p : FinDist α) (k : α → FinDist β) (readout : α → γ) :
    FinDist (β × γ) := p.bind (fun a ↦ (k a).map (fun b ↦ (b,readout a)))

theorem observationJoint_apply (p : FinDist α) (k : α → FinDist β)
    (readout : α → γ) (b : β) (c : γ) :
    observationJoint p k readout (b,c) =
      ∑ a, if readout a = c then p a * k a b else 0 := by
  simp only [observationJoint, bind_apply, map_apply, Prod.mk.injEq]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : readout a = c <;> simp [h]

@[simp] theorem observationJoint_leftMarginal (p : FinDist α) (k : α → FinDist β)
    (readout : α → γ) : (observationJoint p k readout).leftMarginal = p.bind k := by
  ext b
  rw [leftMarginal_apply]
  simp only [observationJoint_apply, bind_apply]
  rw [Finset.sum_comm]
  simp

/-- Running a further readout channel on the retained latent value is
identical to sampling its output alongside the original observation. -/
theorem observationJoint_rightChannel {δ : Type*} [Fintype δ] [DecidableEq δ]
    (p : FinDist α) (k : α → FinDist β) (readout : α → γ) (l : γ → FinDist δ) :
    rightChannel (observationJoint p k readout) l =
      p.bind (fun a ↦ (k a).prod (l (readout a))) := by
  ext bd
  obtain ⟨b,d⟩ := bd
  rw [rightChannel_apply, bind_apply]
  simp only [observationJoint_apply, Finset.sum_mul, ite_mul, zero_mul, prod_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [mul_assoc]

/-- Separate two coordinates from a finite product without losing the
outside subtype's actual index set. -/
theorem prod_split_pair (f : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    (∏ k, f k) = f i * f j * ∏ k : {k // k ≠ i ∧ k ≠ j}, f k := by
  classical
  rw [← Finset.prod_subtype ((Finset.univ.erase i).erase j)
    (fun k ↦ by simp [and_comm]) f]
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) f (a := j) (by simp [hij.symm])]
  ring

end
end ForestSampling.FinDist

namespace ForestSampling.MaskedInformation
noncomputable section

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A masked background extends to a full masked state with the two
endpoints deliberately unobserved. -/
def outsideState (i j : Position N) (y : CompleteBoundary N (Option V) i j) : MaskedState N V :=
  CompleteBoundary.extension i j none none y

theorem outsideState_agrees_iff (i j : Position N)
    (y : CompleteBoundary N (Option V) i j) (x : Configuration N V) :
    (outsideState i j y).Agrees x ↔ FinDist.MaskAgrees y (fun k ↦ x k) := by
  constructor
  · intro h k a hka
    apply h k a
    simpa [outsideState, CompleteBoundary.extension, k.2.1, k.2.2] using hka
  · intro h k a hka
    by_cases hki : k=i
    · simp [outsideState, CompleteBoundary.extension, hki] at hka
    · by_cases hkj : k=j
      · simp [outsideState, CompleteBoundary.extension, hkj] at hka
      · apply h ⟨k,hki,hkj⟩ a
        simpa [outsideState, CompleteBoundary.extension, hki, hkj] using hka

/-- The observed background marginal contains all source randomness and
independent mask coins outside the two designated coordinates. -/
def backgroundLaw (p : FinDist (Configuration N V)) (i j : Position N)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : FinDist (CompleteBoundary N (Option V) i j) :=
  p.bind (fun x ↦ FinDist.maskChannel (fun k : {k // k ≠ i ∧ k ≠ j} ↦ x k) q hq0 hq1)

def backgroundPairLaw (p : FinDist (Configuration N V)) (i j : Position N)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    FinDist (CompleteBoundary N (Option V) i j × (V × V)) :=
  FinDist.observationJoint p
    (fun x ↦ FinDist.maskChannel (fun k : {k // k ≠ i ∧ k ≠ j} ↦ x k) q hq0 hq1)
    (fun x ↦ (x i,x j))

theorem backgroundLaw_apply (p : FinDist (Configuration N V)) (i j : Position N)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (y : CompleteBoundary N (Option V) i j) :
    backgroundLaw p i j q hq0 hq1 y =
      FinDist.maskWeight y q * p.eventMass (outsideState i j y).Agrees := by
  simp only [backgroundLaw, FinDist.bind_apply, FinDist.maskChannel_apply,
    FinDist.eventMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [outsideState_agrees_iff]
  split_ifs <;> ring

theorem backgroundPairLaw_apply (p : FinDist (Configuration N V)) (i j : Position N)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (y : CompleteBoundary N (Option V) i j) (ab : V × V) :
    backgroundPairLaw p i j q hq0 hq1 (y,ab) =
      FinDist.maskWeight y q * p.eventMass
        (fun x ↦ (outsideState i j y).Agrees x ∧ (x i,x j)=ab) := by
  simp only [backgroundPairLaw, FinDist.observationJoint_apply, FinDist.maskChannel_apply,
    FinDist.eventMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [outsideState_agrees_iff]
  split_ifs <;> simp_all <;> ring

/-- The actual masked observation splits into its outside history followed
by the ordered pair of endpoint observations. -/
def pairObservationEquiv {i j : Position N} (hij : i ≠ j) :
    MaskedState N V ≃ (CompleteBoundary N (Option V) i j × (Option V × Option V)) :=
  (CompleteBoundary.pairSplitEquiv (V := Option V) hij).trans (Equiv.prodComm _ _)

def maskedPairLaw (p : FinDist (Configuration N V)) {i j : Position N} (hij : i ≠ j)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :=
  (p.maskedLaw q hq0 hq1).map (pairObservationEquiv (V := V) hij)

theorem maskChannel_pairObservation (x : Configuration N V) {i j : Position N} (hij : i ≠ j)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (FinDist.maskChannel x q hq0 hq1).map (pairObservationEquiv (V := V) hij) =
      (FinDist.maskChannel (fun k : {k // k ≠ i ∧ k ≠ j} ↦ x k) q hq0 hq1).prod
        (((FinDist.dirac (x i)).erase q hq0 hq1).prod ((FinDist.dirac (x j)).erase q hq0 hq1)) := by
  ext yab
  obtain ⟨y,ab⟩ := yab
  rw [FinDist.map_equiv_apply]
  change (∏ k, ((FinDist.dirac (x k)).erase q hq0 hq1)
    (CompleteBoundary.extension i j ab.1 ab.2 y k)) =
    (∏ k : {k // k ≠ i ∧ k ≠ j}, ((FinDist.dirac (x k)).erase q hq0 hq1) (y k)) *
      (((FinDist.dirac (x i)).erase q hq0 hq1) ab.1 *
       ((FinDist.dirac (x j)).erase q hq0 hq1) ab.2)
  rw [FinDist.prod_split_pair _ hij]
  simp only [CompleteBoundary.extension, dite_true, hij.symm, dite_false]
  have ho : (∏ k : {k // k ≠ i ∧ k ≠ j},
      ((FinDist.dirac (x k)).erase q hq0 hq1)
        (CompleteBoundary.extension i j ab.1 ab.2 y k)) =
      ∏ k : {k // k ≠ i ∧ k ≠ j}, ((FinDist.dirac (x k)).erase q hq0 hq1) (y k) := by
    apply Finset.prod_congr rfl
    intro k _
    simp [CompleteBoundary.extension, k.2.1, k.2.2]
  simp only [CompleteBoundary.extension] at ho
  rw [ho]
  ring

theorem maskedPairLaw_eq_rightChannel (p : FinDist (Configuration N V))
    {i j : Position N} (hij : i ≠ j) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    maskedPairLaw p hij q hq0 hq1 = FinDist.rightChannel
      (backgroundPairLaw p i j q hq0 hq1)
      (fun ab ↦ ((FinDist.dirac ab.1).erase q hq0 hq1).prod
        ((FinDist.dirac ab.2).erase q hq0 hq1)) := by
  rw [maskedPairLaw, FinDist.maskedLaw, FinDist.map_bind_channel]
  simp_rw [maskChannel_pairObservation _ hij]
  exact (FinDist.observationJoint_rightChannel p
    (fun x ↦ FinDist.maskChannel (fun k : {k // k ≠ i ∧ k ≠ j} ↦ x k) q hq0 hq1)
    (fun x ↦ (x i,x j)) (fun ab : V × V ↦ ((FinDist.dirac ab.1).erase q hq0 hq1).prod
      ((FinDist.dirac ab.2).erase q hq0 hq1))).symm

variable [Nonempty V]

theorem backgroundLaw_positive (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (i j : Position N) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (backgroundLaw p i j q hq0.le hq1.le).StrictlyPositive := by
  intro y
  rw [backgroundLaw_apply]
  exact mul_pos (FinDist.maskWeight_pos y q hq0 hq1) ((outsideState i j y).probability_pos p hp)

/-- Bayes cancellation identifies the actual conditional endpoint pair
given a masked background with the manuscript's exact history pair. -/
theorem backgroundPairLaw_eq_pairJoint (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (i j : Position N) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    backgroundPairLaw p i j q hq0 hq1 = FinDist.pairJoint
      (backgroundLaw p i j q hq0 hq1) (fun y ↦ (outsideState i j y).exactPair p hp i j) := by
  ext yab
  obtain ⟨y,ab⟩ := yab
  have hr : (outsideState i j y).exactPair p hp i j ab =
      p.eventMass (fun x ↦ (outsideState i j y).Agrees x ∧ (x i,x j)=ab) /
        p.eventMass (outsideState i j y).Agrees :=
    FinDist.conditionalMap_apply_ratio p (outsideState i j y).Agrees
      ((outsideState i j y).probability_pos p hp) (fun x ↦ (x i,x j)) ab
  rw [backgroundPairLaw_apply, FinDist.pairJoint_apply, backgroundLaw_apply, hr]
  have hn : p.eventMass (outsideState i j y).Agrees ≠ 0 :=
    ((outsideState i j y).probability_pos p hp).ne'
  field_simp [hn]

theorem backgroundPairLaw_positive (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    {i j : Position N} (hij : i ≠ j) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (backgroundPairLaw p i j q hq0.le hq1.le).StrictlyPositive := by
  rw [backgroundPairLaw_eq_pairJoint p hp]
  apply FinDist.pairJoint_positive _ _ (backgroundLaw_positive p hp i j q hq0 hq1)
  intro y
  apply MaskedState.exactPair_positive p hp _ hij
  · simp [outsideState, CompleteBoundary.extension]
  · simp [outsideState, CompleteBoundary.extension, hij.symm]

/-- The full vector's actual masked-pair marginal is exactly fresh endpoint
erasure applied to the actual background-conditioned pair joint law. -/
theorem maskedPairLaw_eq_eraseRightPair (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    {i j : Position N} (hij : i ≠ j) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    maskedPairLaw p hij q hq0.le hq1.le =
      (backgroundPairLaw p i j q hq0.le hq1.le).eraseRightPair
        (backgroundPairLaw_positive p hp hij q hq0 hq1) q hq0.le hq1.le := by
  rw [maskedPairLaw_eq_rightChannel, FinDist.eraseRightPair_eq_rightChannel]

theorem maskedPairLaw_positive (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    {i j : Position N} (hij : i ≠ j) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (maskedPairLaw p hij q hq0.le hq1.le).StrictlyPositive := by
  rw [maskedPairLaw_eq_eraseRightPair p hp hij q hq0 hq1]
  exact FinDist.eraseRightPair_positive _ _ q hq0 hq1

theorem backgroundPairLaw_conditionalRight (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    {i j : Position N} (hij : i ≠ j) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (y : CompleteBoundary N (Option V) i j) :
    (backgroundPairLaw p i j q hq0.le hq1.le).conditionalRight
      (backgroundPairLaw_positive p hp hij q hq0 hq1) y =
      (outsideState i j y).exactPair p hp i j := by
  have he : ∀ y, ((outsideState i j y).exactPair p hp i j).StrictlyPositive := by
    intro y
    apply MaskedState.exactPair_positive p hp _ hij
    · simp [outsideState, CompleteBoundary.extension]
    · simp [outsideState, CompleteBoundary.extension, hij.symm]
  simpa only [backgroundPairLaw_eq_pairJoint p hp] using
    FinDist.pairJoint_conditionalRight (backgroundLaw p i j q hq0.le hq1.le)
      (fun y ↦ (outsideState i j y).exactPair p hp i j)
      (backgroundLaw_positive p hp i j q hq0 hq1) he y

/-- The manuscript's masked-pair identity is a theorem about the full
independent erasure law: endpoint survival contributes `q²`, while the
remaining average is over the actual masked-background distribution. -/
theorem maskedPair_conditionalMutualInformation (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    {i j : Position N} (hij : i ≠ j) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (maskedPairLaw p hij q hq0.le hq1.le).conditionalMutualInformation
      (maskedPairLaw_positive p hp hij q hq0 hq1) =
      q^2 * ∑ y, backgroundLaw p i j q hq0.le hq1.le y *
        ((outsideState i j y).exactPair p hp i j).mutualInformation := by
  have hc {r s : FinDist (CompleteBoundary N (Option V) i j × (Option V × Option V))}
      (hr : r.StrictlyPositive) (hs : s.StrictlyPositive) (h : r=s) :
      r.conditionalMutualInformation hr = s.conditionalMutualInformation hs := by
    subst s
    rfl
  rw [hc (maskedPairLaw_positive p hp hij q hq0 hq1)
    (FinDist.eraseRightPair_positive _ _ q hq0 hq1)
    (maskedPairLaw_eq_eraseRightPair p hp hij q hq0 hq1),
    FinDist.conditionalMutualInformation_eraseRightPair _ _ q hq0 hq1]
  congr 1
  unfold FinDist.conditionalMutualInformation
  simp only [backgroundPairLaw_conditionalRight p hp hij q hq0 hq1]
  change (∑ y, (FinDist.observationJoint p _ _).leftMarginal y * _) = _
  rw [FinDist.observationJoint_leftMarginal]
  rfl

end
end ForestSampling.MaskedInformation
