import ForestSampling.PairConditionals
import ForestSampling.FiniteInformation

set_option autoImplicit false

namespace ForestSampling
namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem leftMarginal_map_swap (p : FinDist (α × β)) :
    (p.map (Equiv.prodComm α β)).leftMarginal = p.rightMarginal := by
  simp only [leftMarginal, rightMarginal, map_comp]
  rfl

theorem rightMarginal_map_swap (p : FinDist (α × β)) :
    (p.map (Equiv.prodComm α β)).rightMarginal = p.leftMarginal := by
  simp only [leftMarginal, rightMarginal, map_comp]
  rfl

theorem prod_map_swap (p : FinDist α) (q : FinDist β) :
    (p.prod q).map (Equiv.prodComm α β) = q.prod p := by
  ext ba
  rw [map_equiv_apply]
  simp only [Equiv.prodComm_symm, Equiv.prodComm_apply, prod_apply]
  exact mul_comm _ _

/-- Mutual information is unchanged when the ordered pair is reversed. -/
theorem mutualInformation_map_swap (p : FinDist (α × β)) :
    (p.map (Equiv.prodComm α β)).mutualInformation = p.mutualInformation := by
  rw [mutualInformation, leftMarginal_map_swap, rightMarginal_map_swap,
    ← prod_map_swap, klDivergence_map_equiv]
  rfl

end FinDist

namespace MaskedState

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Reversing the coordinate readout reverses the actual conditional pair. -/
theorem exactPair_swap (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (y : MaskedState N V) (i j : Position N) :
    y.exactPair p hp j i = (y.exactPair p hp i j).map (Equiv.prodComm V V) := by
  simp only [exactPair, FinDist.conditionalMap, FinDist.map_comp]
  rfl

theorem exactPair_mutualInformation_swap (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (y : MaskedState N V) (i j : Position N) :
    (y.exactPair p hp j i).mutualInformation = (y.exactPair p hp i j).mutualInformation := by
  rw [exactPair_swap, FinDist.mutualInformation_map_swap]

end MaskedState
end ForestSampling
