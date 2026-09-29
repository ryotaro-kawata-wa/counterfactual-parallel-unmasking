import ForestSampling.ForestModel
import Mathlib.Combinatorics.SimpleGraph.Hasse

set_option autoImplicit false

namespace ForestSampling

namespace Rooting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

/-- A strictly descending, single-parent orientation excludes cycles. We
choose a maximal-depth vertex on a hypothetical cycle; both of its cycle
neighbors would have to be its unique parent. -/
theorem isAcyclic (r : Rooting G) : G.IsAcyclic := by
  classical
  intro u c hc
  obtain ⟨v, hv, hmax⟩ := c.support.toFinset.exists_max_image r.depth
    ⟨u, by simp⟩
  have hv' : v ∈ c.support := List.mem_toFinset.mp hv
  let d := c.rotate v hv'
  have hd : d.IsCycle := hc.rotate hv'
  have hmax' (w : ι) (hw : w ∈ d.support) : r.depth w ≤ r.depth v := by
    exact hmax w (List.mem_toFinset.mpr ((c.mem_support_rotate_iff v hv').mp hw))
  have hparent (w : ι) (hadj : G.Adj v w) (hw : w ∈ d.support) : r.parent v = w := by
    rcases r.edge_oriented hadj with ⟨_, heq⟩ | ⟨hroot, heq⟩
    · exact heq
    · have hh := r.parent_depth_lt w hroot
      rw [heq] at hh
      exact False.elim ((not_lt_of_ge (hmax' w hw)) hh)
  have hs := hparent d.snd (d.adj_snd hd.not_nil)
    (List.mem_of_mem_tail (d.snd_mem_tail_support hd.not_nil))
  have hp := hparent d.penultimate (d.adj_penultimate hd.not_nil).symm
    (List.mem_of_mem_dropLast (d.penultimate_mem_dropLast_support hd.not_nil))
  exact hd.snd_ne_penultimate (hs.symm.trans hp)

end Rooting

namespace PathGraph

/-- The explicit left-to-right rooting of the path on `Fin N`. This also
handles the empty path without introducing a distinguished vertex. -/
def rooting (N : ℕ) : Rooting (SimpleGraph.pathGraph N) where
  roots := Finset.univ.filter (fun i ↦ i.val = 0)
  parent i := ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  depth i := i.val
  root_iff_depth_zero i := by simp
  parent_adj i hi := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [SimpleGraph.pathGraph_adj]
    exact Or.inl (by simp only; omega)
  parent_depth_lt i hi := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only
    omega
  edge_oriented := by
    intro i j hij
    rw [SimpleGraph.pathGraph_adj] at hij
    rcases hij with hij | hij
    · right
      constructor
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · apply Fin.ext; simp only; omega
    · left
      constructor
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · apply Fin.ext; simp only; omega

theorem isAcyclic (N : ℕ) : (SimpleGraph.pathGraph N).IsAcyclic :=
  (rooting N).isAcyclic

@[simp] theorem roots_succ (n : ℕ) : (rooting (n + 1)).roots = {0} := by
  ext i
  simp only [rooting, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h ↦ Fin.ext h, fun h ↦ congrArg Fin.val h⟩

@[simp] theorem parent_succ (n : ℕ) (i : Fin n) :
    (rooting (n + 1)).parent i.succ = i.castSucc := by
  apply Fin.ext
  simp [rooting]

end PathGraph
end ForestSampling
