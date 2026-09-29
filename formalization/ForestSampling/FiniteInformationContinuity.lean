import ForestSampling.FiniteInformation
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling.FinDist
noncomputable section

variable {T α β γ : Type*} [TopologicalSpace T]
variable [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Coordinate marginals of a continuous finite-law family remain
continuous because their atom masses are finite sums. -/
theorem continuous_leftMarginal (p : T → FinDist (α × β))
    (hmass : ∀ ab, Continuous (fun t ↦ p t ab)) (a : α) :
    Continuous (fun t ↦ (p t).leftMarginal a) := by
  simp only [leftMarginal_apply]
  apply continuous_finsetSum
  intro b _
  exact hmass (a,b)

theorem continuous_rightMarginal (p : T → FinDist (α × β))
    (hmass : ∀ ab, Continuous (fun t ↦ p t ab)) (b : β) :
    Continuous (fun t ↦ (p t).rightMarginal b) := by
  simp only [rightMarginal_apply]
  apply continuous_finsetSum
  intro a _
  exact hmass (a,b)

/-- Strictly positive continuous finite-law families have continuous KL.
The parameter domain may itself be a subtype, such as positive times. -/
theorem continuous_klDivergence (p q : T → FinDist α)
    (hp : ∀ t, (p t).StrictlyPositive) (hq : ∀ t, (q t).StrictlyPositive)
    (hpm : ∀ a, Continuous (fun t ↦ p t a)) (hqm : ∀ a, Continuous (fun t ↦ q t a)) :
    Continuous (fun t ↦ (p t).klDivergence (q t)) := by
  unfold klDivergence
  apply continuous_finsetSum
  intro a _
  exact (hpm a).mul (((hpm a).div (hqm a) (fun t ↦ (hq t a).ne')).log
    (fun t ↦ (div_pos (hp t a) (hq t a)).ne'))

/-- Pair mutual information is continuous on a positive finite-law
family; positivity is needed only on the chosen parameter domain. -/
theorem continuous_mutualInformation [Nonempty α] [Nonempty β]
    (p : T → FinDist (α × β)) (hp : ∀ t, (p t).StrictlyPositive)
    (hmass : ∀ ab, Continuous (fun t ↦ p t ab)) :
    Continuous (fun t ↦ (p t).mutualInformation) := by
  apply continuous_klDivergence p (fun t ↦ (p t).leftMarginal.prod (p t).rightMarginal) hp
    (fun t ↦ prod_strictlyPositive ((p t).leftMarginal_positive (hp t))
      ((p t).rightMarginal_positive (hp t))) hmass
  intro ab
  exact (continuous_leftMarginal p hmass ab.1).mul (continuous_rightMarginal p hmass ab.2)

/-- Posterior atom probabilities are continuous finite ratios with
strictly positive conditioning marginals. -/
theorem continuous_conditionalRight [Nonempty β]
    (p : T → FinDist (α × β)) (hp : ∀ t, (p t).StrictlyPositive)
    (hmass : ∀ ab, Continuous (fun t ↦ p t ab)) (a : α) (b : β) :
    Continuous (fun t ↦ (p t).conditionalRight (hp t) a b) := by
  exact (hmass (a,b)).div (continuous_leftMarginal p hmass a)
    (fun t ↦ ((p t).leftMarginal_positive (hp t) a).ne')

/-- Conditional mutual information is continuous as the finite average
of continuous, strictly positive posterior pair laws. -/
theorem continuous_conditionalMutualInformation [Nonempty α] [Nonempty β]
    (p : T → FinDist (γ × (α × β))) (hp : ∀ t, (p t).StrictlyPositive)
    (hmass : ∀ zab, Continuous (fun t ↦ p t zab)) :
    Continuous (fun t ↦ (p t).conditionalMutualInformation (hp t)) := by
  unfold conditionalMutualInformation
  apply continuous_finsetSum
  intro z _
  apply (continuous_leftMarginal p hmass z).mul
  exact continuous_mutualInformation (fun t ↦ (p t).conditionalRight (hp t) z)
    (fun t ↦ (p t).conditionalRight_positive (hp t) z)
    (fun ab ↦ continuous_conditionalRight p hp hmass z ab)

end
end ForestSampling.FinDist
