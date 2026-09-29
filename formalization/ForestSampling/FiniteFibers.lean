import ForestSampling.SurvivorProcess
import ForestSampling.MatchingLaplace

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling
namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- An explicit positive fiber of a uniform finite law has the uniform
conditional expectation of its full subtype, with no omitted hidden states. -/
theorem uniform_conditionOn_expectation [Nonempty α]
    (E : α → Prop) [DecidablePred E] [Nonempty {a // E a}]
    (hE : 0 < (uniform α).eventMass E) (f : α → ℝ) :
    ((uniform α).conditionOn E hE).expectation f =
      (uniform {a // E a}).expectation (fun a ↦ f a.1) := by
  rw [uniform_conditionOn_eq_map_subtype, expectation_map]
  rfl

/-- Fiberwise bounds average under a uniform finite law. Surjectivity makes
all displayed fibers inhabited; applications may use the finite image type. -/
theorem uniform_expectation_le_by_fibers [Nonempty α]
    (g : α → β) (hg : Function.Surjective g) (f : α → ℝ) (c : β → ℝ)
    (hbound : ∀ b, letI : Nonempty {a // g a = b} := ⟨⟨(hg b).choose, (hg b).choose_spec⟩⟩
      (uniform {a // g a = b}).expectation (fun a ↦ f a.1) ≤ c b) :
    (uniform α).expectation f ≤ (uniform α).expectation (c ∘ g) := by
  have hpos : ∀ b, 0 < (uniform α).eventMass (fun a ↦ g a = b) := by
    intro b
    exact (uniform α).eventMass_pos_of_exists (uniform_strictlyPositive α) _ (hg b)
  rw [expectation_eq_sum_conditionOn (uniform α) g hpos f]
  calc
    _ ≤ ∑ b, (uniform α).eventMass (fun a ↦ g a = b) * c b := by
      apply Finset.sum_le_sum
      intro b _
      let : Nonempty {a // g a = b} := ⟨⟨(hg b).choose, (hg b).choose_spec⟩⟩
      rw [uniform_conditionOn_expectation]
      exact mul_le_mul_of_nonneg_left (hbound b) ((uniform α).eventMass_nonneg _)
    _ = ((uniform α).map g).expectation c := by
      unfold expectation
      apply Finset.sum_congr rfl
      intro b _
      rfl
    _ = _ := (uniform α).expectation_map g c

/-- Exact expectation under a dependent retained joint law. -/
theorem expectation_sigmaJoint {Ω : α → Type*} [∀ a, Fintype (Ω a)]
    (p : FinDist α) (q : ∀ a, FinDist (Ω a)) (f : (a : α) × Ω a → ℝ) :
    (sigmaJoint p q).expectation f =
      p.expectation (fun a ↦ (q a).expectation (fun b ↦ f ⟨a,b⟩)) := by
  unfold expectation
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [sigmaJoint_apply]
  ring

/-- An equivalence of full finite fibers preserves their uniform averages. -/
theorem uniform_expectation_equiv [Nonempty α] [Nonempty β]
    (e : α ≃ β) (f : β → ℝ) :
    (uniform α).expectation (f ∘ e) = (uniform β).expectation f := by
  rw [← expectation_map, uniform_map_equiv]

/-- A witness-indexed disintegration bound avoids inventing values on
unreachable fibers. The comparison weight is constant on each actual fiber. -/
theorem uniform_expectation_le_by_witness_fibers [Nonempty α]
    (g : α → β) (f w : α → ℝ)
    (hw : ∀ a b, g a = g b → w a = w b)
    (hbound : ∀ a, letI : Nonempty {b // g b = g a} := ⟨⟨a, rfl⟩⟩
      (uniform {b // g b = g a}).expectation (fun b ↦ f b.1) ≤ w a) :
    (uniform α).expectation f ≤ (uniform α).expectation w := by
  classical
  let Image := {b : β // ∃ a, g a = b}
  let readout : α → Image := fun a ↦ ⟨g a, a, rfl⟩
  let representative : Image → α := fun b ↦ b.2.choose
  have hrep (b : Image) : g (representative b) = b.1 := b.2.choose_spec
  have hsurj : Function.Surjective readout := by
    intro b
    refine ⟨representative b, ?_⟩
    exact Subtype.ext (hrep b)
  let c : Image → ℝ := fun b ↦ w (representative b)
  have hlocal : ∀ b : Image,
      letI : Nonempty {a // readout a = b} := ⟨⟨(hsurj b).choose, (hsurj b).choose_spec⟩⟩
      (uniform {a // readout a = b}).expectation (fun a ↦ f a.1) ≤ c b := by
    intro b
    let : Nonempty {a // readout a = b} := ⟨⟨(hsurj b).choose, (hsurj b).choose_spec⟩⟩
    let : Nonempty {a // g a = g (representative b)} := ⟨⟨representative b, rfl⟩⟩
    let e : {a // readout a = b} ≃ {a // g a = g (representative b)} :=
      Equiv.subtypeEquivRight (fun a ↦ by
        constructor
        · intro ha
          exact (congrArg Subtype.val ha).trans (hrep b).symm
        · intro ha
          exact Subtype.ext (ha.trans (hrep b)))
    have he := uniform_expectation_equiv e (fun a ↦ f a.1)
    change (uniform {a // readout a = b}).expectation (fun a ↦ f a.1) =
      (uniform {a // g a = g (representative b)}).expectation (fun a ↦ f a.1) at he
    rw [he]
    exact hbound (representative b)
  have hh := uniform_expectation_le_by_fibers readout hsurj f c hlocal
  have heq : c ∘ readout = w := by
    funext a
    exact hw _ a (hrep (readout a))
  rwa [heq] at hh


/-- Two finite expectation operators commute when their laws are fixed. -/
theorem expectation_comm (p : FinDist α) (q : FinDist β) (f : α → β → ℝ) :
    p.expectation (fun a ↦ q.expectation (f a)) =
      q.expectation (fun b ↦ p.expectation (fun a ↦ f a b)) := by
  unfold expectation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring


end FinDist
end ForestSampling
