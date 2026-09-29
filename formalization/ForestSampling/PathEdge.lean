import ForestSampling.PathGraph

set_option autoImplicit false

namespace ForestSampling
namespace PathGraph

/-- Every ordered adjacent pair is represented by exactly one of the
path's consecutive edge indices, in one of the two orientations. -/
theorem exists_edge_index {n : ℕ} {i j : Position (n + 1)}
    (hij : (SimpleGraph.pathGraph (n + 1)).Adj i j) :
    ∃ e : Fin n, (e.castSucc = i ∧ e.succ = j) ∨ (e.castSucc = j ∧ e.succ = i) := by
  rw [SimpleGraph.pathGraph_adj] at hij
  rcases hij with hij | hij
  · let e : Fin n := ⟨i.val, by have hj := j.isLt; omega⟩
    exact ⟨e, Or.inl ⟨Fin.ext rfl, Fin.ext hij⟩⟩
  · let e : Fin n := ⟨j.val, by have hi := i.isLt; omega⟩
    exact ⟨e, Or.inr ⟨Fin.ext rfl, Fin.ext hij⟩⟩

def otherIncidentEdges {n : ℕ} (j : Position (n + 1)) (e : Fin n) : Finset (Fin n) :=
  (Finset.univ.erase e).filter (fun k ↦ k.castSucc = j ∨ k.succ = j)

/-- Removing an incident edge from a path leaves at most one other
incident edge. This is the exact endpoint/interior distinction needed by
the uniform edge-signal calculation. -/
theorem otherIncidentEdges_card_le_one {n : ℕ} (j : Position (n + 1)) (e : Fin n)
    (he : e.castSucc = j ∨ e.succ = j) : (otherIncidentEdges j e).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [otherIncidentEdges, Finset.mem_filter, Finset.mem_erase,
    Finset.mem_univ, and_true] at ha hb
  have hae : a.val ≠ e.val := fun h ↦ ha.1 (Fin.ext h)
  have hbe : b.val ≠ e.val := fun h ↦ hb.1 (Fin.ext h)
  have he' : e.val = j.val ∨ e.val + 1 = j.val := by
    rcases he with h | h
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (congrArg Fin.val h)
  have ha' : a.val = j.val ∨ a.val + 1 = j.val := by
    rcases ha.2 with h | h
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (congrArg Fin.val h)
  have hb' : b.val = j.val ∨ b.val + 1 = j.val := by
    rcases hb.2 with h | h
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (congrArg Fin.val h)
  apply Fin.ext
  omega

/-- Two indexed path edges with the same two ordered endpoints agree,
irrespective of the orientation used to describe them. -/
theorem edge_index_unique {n : ℕ} {i j : Position (n + 1)} {e k : Fin n}
    (he : (e.castSucc = i ∧ e.succ = j) ∨ (e.castSucc = j ∧ e.succ = i))
    (hk : (k.castSucc = i ∧ k.succ = j) ∨ (k.castSucc = j ∧ k.succ = i)) : k = e := by
  apply Fin.ext
  rcases he with ⟨hei, hej⟩ | ⟨hej, hei⟩ <;>
    rcases hk with ⟨hki, hkj⟩ | ⟨hkj, hki⟩ <;>
    have hi := congrArg Fin.val hei <;> have hj := congrArg Fin.val hej <;>
    have hki' := congrArg Fin.val hki <;> have hkj' := congrArg Fin.val hkj <;>
    simp only [Fin.val_castSucc, Fin.val_succ] at * <;> omega

end PathGraph
end ForestSampling
