import ForestSampling.FiniteProbability

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

/-- TV obeys the triangle inequality with the paper's factor-one-half
normalization. -/
theorem tv_triangle (p q r : FinDist α) : tv p r ≤ tv p q + tv q r := by
  unfold tv
  have hsum : (∑ x, |p x - r x|) ≤ (∑ x, |p x - q x|) + ∑ x, |q x - r x| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    have heq : p x - r x = (p x - q x) + (q x - r x) := by ring
    rw [heq]
    exact abs_add_le _ _
  linarith

/-- Kernels with a shared input law have output TV at most their mean local
TV. This is the basic common-prefix comparison step for repaired programs. -/
theorem tv_bind_same_le (p : FinDist α) (k l : α → FinDist β) :
    tv (p.bind k) (p.bind l) ≤ ∑ a, p a * tv (k a) (l a) := by
  have hpoint : ∀ b, |p.bind k b - p.bind l b| ≤
      ∑ a, p a * |k a b - l a b| := by
    intro b
    simp only [bind_apply]
    rw [← Finset.sum_sub_distrib]
    have heq : (∑ a, (p a * k a b - p a * l a b)) =
        ∑ a, p a * (k a b - l a b) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [heq]
    calc
      |∑ a, p a * (k a b - l a b)| ≤ ∑ a, |p a * (k a b - l a b)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, p a * |k a b - l a b| := by
        apply Finset.sum_congr rfl
        intro a _
        rw [abs_mul, abs_of_nonneg (p.nonneg a)]
  unfold tv
  calc
    (1 / 2 : ℝ) * ∑ b, |p.bind k b - p.bind l b| ≤
        (1 / 2 : ℝ) * ∑ b, ∑ a, p a * |k a b - l a b| :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ ↦ hpoint b)) (by norm_num)
    _ = ∑ a, p a * ((1 / 2 : ℝ) * ∑ b, |k a b - l a b|) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum]
      ring

/-- A kernel repair confined to a bad input event changes the output by at
most that event's probability under the common input law. -/
theorem tv_bind_same_le_eventMass (p : FinDist α) (k l : α → FinDist β)
    (bad : α → Prop) [DecidablePred bad]
    (hgood : ∀ a, ¬ bad a → k a = l a) :
    tv (p.bind k) (p.bind l) ≤ p.eventMass bad := by
  apply (tv_bind_same_le p k l).trans
  unfold eventMass
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : bad a
  · rw [if_pos ha]
    exact (mul_le_mul_of_nonneg_left (tv_le_one (k a) (l a)) (p.nonneg a)).trans_eq (mul_one _)
  · rw [if_neg ha, hgood a ha, tv_self, mul_zero]

/-- A deterministic readout is the same finite operation as binding Dirac
kernels. This identifies coupled readouts with the shared-input TV estimate. -/
theorem map_eq_bind_dirac [DecidableEq β] (p : FinDist α) (f : α → β) :
    p.map f = p.bind (fun a ↦ dirac (f a)) := by
  ext b
  simp only [map_apply, bind_apply, dirac_apply]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b
  · simp [h]
  · simp [h, Ne.symm h]

/-- The finite coupling inequality for two readouts of one joint randomness
source, with no positivity or independence requirement. -/
theorem tv_maps_le_disagreement [DecidableEq β]
    (p : FinDist α) (f g : α → β) :
    tv (p.map f) (p.map g) ≤ p.eventMass (fun a ↦ f a ≠ g a) := by
  rw [map_eq_bind_dirac, map_eq_bind_dirac]
  apply tv_bind_same_le_eventMass
  intro a ha
  simp only [not_not] at ha
  rw [ha]

end FinDist
end ForestSampling
