import ForestSampling.FiniteProbability

set_option autoImplicit false

open scoped BigOperators

namespace ForestSampling

universe u

/-- Positions of a length-`N` sequence. -/
abbrev Position (N : ℕ) := Fin N

/-- A complete assignment of vocabulary values to all sequence positions. -/
abbrev Configuration (N : ℕ) (V : Type u) := Position N → V

namespace Configuration

variable {N : ℕ} {V : Type u}

@[ext]
theorem ext {x y : Configuration N V} (h : ∀ i, x i = y i) : x = y :=
  funext h

end Configuration

namespace FinDist

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- The exact marginal at one position. -/
def positionMarginal (p : FinDist (Configuration N V)) (i : Position N) :
    FinDist V :=
  p.map (fun x ↦ x i)

@[simp]
theorem positionMarginal_apply (p : FinDist (Configuration N V))
    (i : Position N) (a : V) :
    p.positionMarginal i a = ∑ x, if x i = a then p x else 0 := rfl

theorem positionMarginal_strictlyPositive
    (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (i : Position N) :
    (p.positionMarginal i).StrictlyPositive := by
  apply p.map_strictlyPositive_of_surjective hp
  intro a
  exact ⟨fun _ ↦ a, rfl⟩

end FinDist

/-- A committed history stores exactly the committed coordinates and values. -/
structure History (N : ℕ) (V : Type u) where
  committed : Finset (Position N)
  value : committed → V

namespace History

variable {N : ℕ} {V : Type u} [DecidableEq V]

/-- Positions not yet committed. -/
def uncommitted (h : History N V) : Finset (Position N) :=
  Finset.univ \ h.committed

@[simp]
theorem mem_uncommitted_iff (h : History N V) (i : Position N) :
    i ∈ h.uncommitted ↔ i ∉ h.committed := by
  simp [uncommitted]

/-- A complete assignment agrees with a committed history. -/
def Agrees (h : History N V) (x : Configuration N V) : Prop :=
  ∀ i : h.committed, x i.1 = h.value i

noncomputable instance (h : History N V) (x : Configuration N V) :
    Decidable (h.Agrees x) :=
  Classical.propDecidable _

/-- Extend a history, using `fallback` at every uncommitted position. -/
def extension (h : History N V) (fallback : V) : Configuration N V :=
  fun i ↦ if hi : i ∈ h.committed then h.value ⟨i, hi⟩ else fallback

theorem extension_agrees (h : History N V) (fallback : V) :
    h.Agrees (h.extension fallback) := by
  intro i
  simp [extension]

theorem agrees_nonempty (h : History N V) [Nonempty V] :
    ∃ x, h.Agrees x := by
  let fallback : V := Classical.choice (inferInstance : Nonempty V)
  exact ⟨h.extension fallback, h.extension_agrees fallback⟩

/-- An extension whose chosen uncommitted coordinate is forced to `a`. -/
def extensionAt (h : History N V) (j : Position N) (a : V) :
    Configuration N V :=
  fun i ↦ if hij : i = j then a
    else if hi : i ∈ h.committed then h.value ⟨i, hi⟩ else a

theorem extensionAt_agrees (h : History N V) {j : Position N}
    (hj : j ∉ h.committed) (a : V) :
    h.Agrees (h.extensionAt j a) := by
  intro i
  have hij : i.1 ≠ j := by
    intro heq
    apply hj
    simpa [heq] using i.2
  simp [extensionAt, hij, i.2]

@[simp]
theorem extensionAt_apply (h : History N V) (j : Position N) (a : V) :
    h.extensionAt j a j = a := by
  simp [extensionAt]

/-- Probability of a committed history under a complete target law. -/
noncomputable def probability [Fintype V] (p : FinDist (Configuration N V))
    (h : History N V) : ℝ :=
  p.eventMass h.Agrees

theorem probability_pos [Fintype V] (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (h : History N V) [Nonempty V] :
    0 < h.probability p := by
  exact p.eventMass_pos_of_exists hp h.Agrees h.agrees_nonempty

/-- The complete target law conditional on a committed history. -/
noncomputable def conditionalLaw [Fintype V] (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (h : History N V) [Nonempty V] :
    FinDist (Configuration N V) :=
  p.conditionOn h.Agrees (h.probability_pos p hp)

/-- Exact singleton conditional at an uncommitted position. -/
noncomputable def exactRow [Fintype V] (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (h : History N V) [Nonempty V]
    (j : Position N) : FinDist V :=
  p.conditionalMap h.Agrees (h.probability_pos p hp) (fun x ↦ x j)

theorem exactRow_strictlyPositive [Fintype V]
    (p : FinDist (Configuration N V)) (hp : p.StrictlyPositive)
    (h : History N V) [Nonempty V] {j : Position N}
    (hj : j ∉ h.committed) :
    (h.exactRow p hp j).StrictlyPositive := by
  apply p.conditionalMap_strictlyPositive hp h.Agrees
    (h.probability_pos p hp) (fun x ↦ x j)
  intro a
  exact ⟨h.extensionAt j a, h.extensionAt_agrees hj a, h.extensionAt_apply j a⟩

end History

/-- The residual vertex type attached to a committed history. -/
abbrev ResidualVertex {N : ℕ} {V : Type u} (h : History N V) :=
  {i : Position N // i ∈ h.uncommitted}

/-- The hidden forest induced on the uncommitted positions. -/
def residualGraph {N : ℕ} {V : Type u} [DecidableEq V]
    (G : SimpleGraph (Position N)) (h : History N V) :
    SimpleGraph (ResidualVertex h) :=
  G.induce {i | i ∈ h.uncommitted}

/-- A rooted orientation of every component of an undirected forest. -/
structure Rooting {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) where
  roots : Finset ι
  parent : ι → ι
  depth : ι → ℕ
  root_iff_depth_zero : ∀ i, i ∈ roots ↔ depth i = 0
  parent_adj : ∀ i, i ∉ roots → G.Adj (parent i) i
  parent_depth_lt : ∀ i, i ∉ roots → depth (parent i) < depth i
  edge_oriented : ∀ {i j}, G.Adj i j →
    (i ∉ roots ∧ parent i = j) ∨ (j ∉ roots ∧ parent j = i)

namespace Rooting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : SimpleGraph ι}

/-- Nonroot vertices of a rooted forest. -/
def nonRoots (r : Rooting G) : Finset ι :=
  Finset.univ \ r.roots

@[simp]
theorem mem_nonRoots_iff (r : Rooting G) (i : ι) :
    i ∈ r.nonRoots ↔ i ∉ r.roots := by
  simp [nonRoots]

theorem parent_ne_self (r : Rooting G) {i : ι} (hi : i ∉ r.roots) :
    r.parent i ≠ i := by
  intro hparent
  have hlt := r.parent_depth_lt i hi
  rw [hparent] at hlt
  exact (Nat.lt_irrefl _ hlt)

end Rooting

/-- Endpoint kernels are total maps; only their values on oriented edges matter. -/
abbrev EndpointKernel (N : ℕ) (V : Type u) [Fintype V] :=
  Position N → Position N → V → FinDist V

namespace ForestFactorization

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- The right-hand side of the rooted forest factorization in (S0). -/
def mass (p : FinDist (Configuration N V))
    (K : EndpointKernel N V) (G : SimpleGraph (Position N))
    (r : Rooting G) (x : Configuration N V) : ℝ :=
  (∏ i ∈ r.roots, p.positionMarginal i (x i)) *
    ∏ j ∈ r.nonRoots, K (r.parent j) j (x (r.parent j)) (x j)

/-- Forest factorization (S0), for the selected componentwise roots. -/
def Holds (p : FinDist (Configuration N V))
    (K : EndpointKernel N V) (G : SimpleGraph (Position N))
    (r : Rooting G) : Prop :=
  ∀ x, p x = mass p K G r x

/-- Endpoint compatibility (C0). -/
def EndpointCompatible (p : FinDist (Configuration N V))
    (K : EndpointKernel N V) (G : SimpleGraph (Position N)) : Prop :=
  ∀ ⦃i j⦄, G.Adj i j → ∀ a b,
    p.positionMarginal i a * K i j a b =
      p.positionMarginal j b * K j i b a

end ForestFactorization

/-- The finite forest-structured target data and assumptions (S0--C0). -/
structure ForestModel (N : ℕ) (V : Type u) [Fintype V] [DecidableEq V] where
  target : FinDist (Configuration N V)
  target_positive : target.StrictlyPositive
  graph : SimpleGraph (Position N)
  graph_acyclic : graph.IsAcyclic
  kernel : EndpointKernel N V
  kernel_positive : ∀ ⦃i j⦄, graph.Adj i j → ∀ a,
    (kernel i j a).StrictlyPositive
  rooting : Rooting graph
  factorizes : ForestFactorization.Holds target kernel graph rooting
  endpoint_compatible :
    ForestFactorization.EndpointCompatible target kernel graph

namespace ForestModel

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Exact marginal exposed by a forest model. -/
def marginal (M : ForestModel N V) (i : Position N) : FinDist V :=
  M.target.positionMarginal i

theorem marginal_strictlyPositive (M : ForestModel N V) (i : Position N) :
    (M.marginal i).StrictlyPositive :=
  M.target.positionMarginal_strictlyPositive M.target_positive i

/-- All histories have positive target probability when the vocabulary is nonempty. -/
theorem history_probability_pos (M : ForestModel N V) [Nonempty V]
    (h : History N V) :
    0 < h.probability M.target :=
  h.probability_pos M.target M.target_positive

end ForestModel

/-! ## Boundary conditionals and response assumptions -/

/-- Values on every position other than the designated source and readout. -/
abbrev CompleteBoundary (N : ℕ) (V : Type u)
    (i j : Position N) :=
  {k : Position N // k ≠ i ∧ k ≠ j} → V

namespace CompleteBoundary

variable {N : ℕ} {V : Type u}

/-- The event fixing a source value and all coordinates outside source/readout. -/
def Event (i j : Position N) (a : V) (z : CompleteBoundary N V i j)
    (x : Configuration N V) : Prop :=
  x i = a ∧ ∀ k, x k.1 = z k

noncomputable instance [DecidableEq V] (i j : Position N) (a : V)
    (z : CompleteBoundary N V i j) (x : Configuration N V) :
    Decidable (Event i j a z x) :=
  Classical.propDecidable _

/-- A complete assignment realizing a boundary event and a prescribed readout. -/
def extension [DecidableEq V] (i j : Position N) (a b : V)
    (z : CompleteBoundary N V i j) : Configuration N V :=
  fun k ↦ if hki : k = i then a
    else if hkj : k = j then b else z ⟨k, hki, hkj⟩

theorem extension_mem [DecidableEq V] (i j : Position N) (a b : V)
    (z : CompleteBoundary N V i j) :
    Event i j a z (extension i j a b z) := by
  constructor
  · simp [extension]
  · intro k
    simp [extension, k.2.1, k.2.2]

theorem extension_readout [DecidableEq V] {i j : Position N}
    (hij : i ≠ j) (a b : V) (z : CompleteBoundary N V i j) :
    extension i j a b z j = b := by
  simp [extension, hij.symm]

end CompleteBoundary

namespace FinDist

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

theorem boundaryEventMass_pos (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (i j : Position N) (a : V)
    (z : CompleteBoundary N V i j) :
    0 < p.eventMass (CompleteBoundary.Event i j a z) := by
  apply p.eventMass_pos_of_exists hp
  exact ⟨CompleteBoundary.extension i j a a z,
    CompleteBoundary.extension_mem i j a a z⟩

/-- Boundary-conditioned singleton row used in the response assumptions. -/
noncomputable def boundaryRow (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) (i j : Position N) (a : V)
    (z : CompleteBoundary N V i j) : FinDist V :=
  p.conditionalMap (CompleteBoundary.Event i j a z)
    (p.boundaryEventMass_pos hp i j a z) (fun x ↦ x j)

theorem boundaryRow_strictlyPositive (p : FinDist (Configuration N V))
    (hp : p.StrictlyPositive) {i j : Position N} (hij : i ≠ j)
    (a : V) (z : CompleteBoundary N V i j) :
    (p.boundaryRow hp i j a z).StrictlyPositive := by
  apply p.conditionalMap_strictlyPositive hp
    (CompleteBoundary.Event i j a z)
    (p.boundaryEventMass_pos hp i j a z) (fun x ↦ x j)
  intro b
  exact ⟨CompleteBoundary.extension i j a b z,
    CompleteBoundary.extension_mem i j a b z,
    CompleteBoundary.extension_readout hij a b z⟩

end FinDist

namespace ForestModel

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Exact marginal tail at threshold `t`. -/
noncomputable def tailSet (M : ForestModel N V) (i : Position N) (t : ℝ) : Finset V :=
  Finset.univ.filter fun a ↦ M.marginal i a ≤ t

@[simp]
theorem mem_tailSet_iff (M : ForestModel N V) (i : Position N)
    (t : ℝ) (a : V) :
    a ∈ M.tailSet i t ↔ M.marginal i a ≤ t := by
  simp [tailSet]

/-- Maximum response of readout `j` to source `i` at a complete boundary. -/
noncomputable def directedResponse [Nonempty V] (M : ForestModel N V)
    {i j : Position N} (_hij : i ≠ j) (z : CompleteBoundary N V i j) : ℝ :=
  Finset.sup' (Finset.univ : Finset (V × V)) Finset.univ_nonempty
    (fun ab ↦ FinDist.tv
      (M.target.boundaryRow M.target_positive i j ab.1 z)
      (M.target.boundaryRow M.target_positive i j ab.2 z))

theorem pair_response_le_directedResponse [Nonempty V]
    (M : ForestModel N V) {i j : Position N} (hij : i ≠ j)
    (z : CompleteBoundary N V i j) (a b : V) :
    FinDist.tv
      (M.target.boundaryRow M.target_positive i j a z)
      (M.target.boundaryRow M.target_positive i j b z) ≤
      M.directedResponse hij z := by
  exact Finset.le_sup' (fun ab : V × V ↦ FinDist.tv
    (M.target.boundaryRow M.target_positive i j ab.1 z)
    (M.target.boundaryRow M.target_positive i j ab.2 z))
    (Finset.mem_univ (a, b))

/-- Pointwise form of the tail-response condition (RT).

This avoids an artificial convention for maxima over empty or singleton
tails: the condition is vacuous for an empty tail and tautological for a
singleton because `tv p p = 0` (the latter identity is proved below).
-/
def TailResponseRegular (M : ForestModel N V)
    (responseConstant responseExponent : ℝ) : Prop :=
  0 ≤ responseConstant ∧ 0 < responseExponent ∧
    ∀ (i j : Position N), i ≠ j →
      ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
      ∀ (z : CompleteBoundary N V i j) (a b : V),
        a ∈ M.tailSet i t → b ∈ M.tailSet i t →
        FinDist.tv
          (M.target.boundaryRow M.target_positive i j a z)
          (M.target.boundaryRow M.target_positive i j b z) ≤
          responseConstant * t ^ responseExponent

/-- Pointwise oriented form of two-sided edge nondegeneracy (UEN).

Quantification over all ordered adjacent pairs includes both orientations of
each undirected edge.
-/
def EdgeNondegenerate [Nonempty V] (M : ForestModel N V)
    (edgeSignal : ℝ) : Prop :=
  0 < edgeSignal ∧ edgeSignal ≤ 1 ∧
    ∀ ⦃i j : Position N⦄ (hij : M.graph.Adj i j)
      (z : CompleteBoundary N V i j),
      edgeSignal ≤ M.directedResponse hij.ne z

end ForestModel

end ForestSampling
