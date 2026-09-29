import ForestSampling.FiniteErasureInformation

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.FinDist
noncomputable section

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-- The ordinary joint law of a finite input and an actual conditional
output channel. This is the product-shaped version of `sigmaJoint`. -/
def pairJoint (p : FinDist α) (k : α → FinDist β) : FinDist (α × β) :=
  (sigmaJoint p k).map (Equiv.sigmaEquivProd α β)

@[simp] theorem pairJoint_apply (p : FinDist α) (k : α → FinDist β) (a : α) (b : β) :
    pairJoint p k (a,b) = p a * k a b := by
  rw [pairJoint, map_equiv_apply]
  rfl

@[simp] theorem pairJoint_leftMarginal (p : FinDist α) (k : α → FinDist β) :
    (pairJoint p k).leftMarginal = p := by
  ext a
  simp only [leftMarginal_apply, pairJoint_apply, ← Finset.mul_sum, (k a).sum_mass, mul_one]

theorem pairJoint_positive (p : FinDist α) (k : α → FinDist β)
    (hp : p.StrictlyPositive) (hk : ∀ a, (k a).StrictlyPositive) :
    (pairJoint p k).StrictlyPositive := fun ab ↦ by
  rw [show ab = (ab.1,ab.2) from rfl, pairJoint_apply]
  exact mul_pos (hp _) (hk _ _)

@[simp] theorem pairJoint_conditionalRight [Nonempty β]
    (p : FinDist α) (k : α → FinDist β) (hp : p.StrictlyPositive)
    (hk : ∀ a, (k a).StrictlyPositive) (a : α) :
    (pairJoint p k).conditionalRight (pairJoint_positive p k hp hk) a = k a := by
  ext b
  rw [conditionalRight_apply, pairJoint_apply, pairJoint_leftMarginal]
  exact mul_div_cancel_left₀ _ (hp a).ne'

/-- A pushforward may be performed either before or after forming a finite
mixture. All summation identities here concern the actual probability law. -/
theorem map_bind_channel (p : FinDist α) (k : α → FinDist β) (f : β → γ) :
    (p.bind k).map f = p.bind (fun a ↦ (k a).map f) := by
  ext c
  simp only [map_apply, bind_apply]
  have hh (b : β) : (if f b = c then ∑ a, p a * k a b else 0) =
      ∑ a, if f b = c then p a * k a b else 0 := by
    split_ifs <;> simp
  simp_rw [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

/-- Apply a channel to the right coordinate while retaining the left
coordinate as part of the joint observation. -/
def rightChannel (p : FinDist (α × β)) (k : β → FinDist γ) : FinDist (α × γ) :=
  p.bind (fun ab ↦ (k ab.2).map (fun c ↦ (ab.1,c)))

theorem rightChannel_apply (p : FinDist (α × β)) (k : β → FinDist γ)
    (a : α) (c : γ) : rightChannel p k (a,c) = ∑ b, p (a,b)*k b c := by
  simp only [rightChannel, bind_apply, map_apply, Fintype.sum_prod_type, Prod.mk.injEq]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  simp only [ite_and, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem rightChannel_eq_pairJoint [Nonempty β]
    (p : FinDist (α × β)) (hp : p.StrictlyPositive) (k : β → FinDist γ) :
    rightChannel p k = pairJoint p.leftMarginal
      (fun a ↦ (p.conditionalRight hp a).bind k) := by
  ext ac
  obtain ⟨a,c⟩ := ac
  rw [rightChannel_apply, pairJoint_apply, bind_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [conditionalRight_apply]
  field_simp [(p.leftMarginal_positive hp a).ne']
  exact (mul_div_cancel_right₀ _ (p.leftMarginal_positive hp a).ne').symm

/-- Independent erasure of the right pair in a joint law preserves the
background observation and uses fresh coins for the two endpoints. -/
def eraseRightPair [Nonempty α] [Nonempty β]
    (p : FinDist (γ × (α × β))) (hp : p.StrictlyPositive)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : FinDist (γ × (Option α × Option β)) :=
  pairJoint p.leftMarginal (fun c ↦ (p.conditionalRight hp c).erasePair q hq0 hq1)

/-- The posterior form of endpoint erasure agrees with actually running
the two fresh channels on the original joint observation. -/
theorem eraseRightPair_eq_rightChannel [Nonempty α] [Nonempty β]
    (p : FinDist (γ × (α × β))) (hp : p.StrictlyPositive)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    p.eraseRightPair hp q hq0 hq1 = rightChannel p
      (fun ab ↦ ((dirac ab.1).erase q hq0 hq1).prod ((dirac ab.2).erase q hq0 hq1)) := by
  rw [rightChannel_eq_pairJoint p hp]
  simp only [bind_dirac_erase_pair, eraseRightPair]

theorem eraseRightPair_positive [Nonempty α] [Nonempty β]
    (p : FinDist (γ × (α × β))) (hp : p.StrictlyPositive)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (p.eraseRightPair hp q hq0.le hq1.le).StrictlyPositive :=
  pairJoint_positive _ _ (p.leftMarginal_positive hp)
    (fun c ↦ erasePair_positive _ (p.conditionalRight_positive hp c) q hq0 hq1)

/-- Conditioning on any retained background observation commutes exactly
with fresh independent erasure of the endpoint pair. -/
theorem eraseRightPair_conditionalRight [Nonempty α] [Nonempty β]
    (p : FinDist (γ × (α × β))) (hp : p.StrictlyPositive)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (c : γ) :
    (p.eraseRightPair hp q hq0.le hq1.le).conditionalRight
      (p.eraseRightPair_positive hp q hq0 hq1) c =
      (p.conditionalRight hp c).erasePair q hq0.le hq1.le :=
  pairJoint_conditionalRight _ _ (p.leftMarginal_positive hp)
    (fun c ↦ erasePair_positive _ (p.conditionalRight_positive hp c) q hq0 hq1) c

/-- The two-endpoint masking factor remains exactly `q²` after averaging
over every actual background value in conditional mutual information. -/
theorem conditionalMutualInformation_eraseRightPair [Nonempty α] [Nonempty β]
    (p : FinDist (γ × (α × β))) (hp : p.StrictlyPositive)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (p.eraseRightPair hp q hq0.le hq1.le).conditionalMutualInformation
      (p.eraseRightPair_positive hp q hq0 hq1) =
      q^2 * p.conditionalMutualInformation hp := by
  unfold conditionalMutualInformation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [eraseRightPair_conditionalRight p hp q hq0 hq1 c, mutualInformation_erasePair _
    (p.conditionalRight_positive hp c) q hq0 hq1]
  change (pairJoint p.leftMarginal _).leftMarginal c * _ = _
  rw [pairJoint_leftMarginal]
  ring

end
end ForestSampling.FinDist
