import ForestSampling.MatchingRetirement
import ForestSampling.SurvivorProcess
import ForestSampling.HardCollisionAffinity
import ForestSampling.CollisionActivity

set_option autoImplicit false
open scoped BigOperators

namespace ForestSampling

/-- The deterministic retirement ledger of one complete execution. Batch
entries retain survivor size, active batch size, and newly internal edges. -/
structure CollisionLedger where
  queryVertices : ℕ
  batches : List (ℕ × ℕ × ℕ)

namespace CollisionLedger

/-- Sum of active batch sizes in the retained execution. -/
def activeVertices (L : CollisionLedger) : ℕ := (L.batches.map (fun b ↦ b.2.1)).sum
/-- Total collisions on still-unretired edges. -/
def collisions (L : CollisionLedger) : ℕ := (L.batches.map (fun b ↦ b.2.2)).sum
/-- Positive batch excess, including zero for inactive commits. -/
def excess (L : CollisionLedger) : ℕ := (L.batches.map (fun b ↦ b.2.1 - 1)).sum
/-- Compensating activity in the uniform-survivor Laplace argument. -/
noncomputable def activity (L : CollisionLedger) : ℝ :=
  (L.batches.map (fun b ↦ ((b.2.1 - 1 : ℕ) : ℝ)^2 / b.1)).sum

/-- Active vertices exceed positive batch excess by at most one per round. -/
theorem activeVertices_le_excess_add_length (L : CollisionLedger) :
    L.activeVertices ≤ L.excess + L.batches.length := by
  obtain ⟨q, batches⟩ := L
  induction batches with
  | nil => simp [activeVertices, excess]
  | cons b rest ih =>
      simp only [activeVertices, excess, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

/-- Re-index a list sum by its actual finite ordinal positions. -/
theorem sum_get {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  have h := congrArg List.sum (List.map_ofFn (f := l.get) (g := f))
  simpa only [List.sum_ofFn, List.ofFn_get, Function.comp_apply] using h.symm

/-- The list-valued ledger has the Cauchy--Schwarz activity lower bound,
provided its actual excess is at least N/8. -/
theorem activity_lower_bound (L : CollisionLedger) (N R : ℕ)
    (hN : 0 < N) (hR : 0 < R) (hlen : L.batches.length ≤ R)
    (hb : ∀ b ∈ L.batches, b.2.1 ≤ b.1 ∧ b.1 ≤ N)
    (hexcess : (N : ℝ)/8 ≤ (L.excess : ℝ)) :
    (N : ℝ)/(64*(R : ℝ)) ≤ L.activity := by
  have he : (L.excess : ℝ) =
      ∑ i : Fin L.batches.length, (((L.batches.get i).2.1 - 1 : ℕ) : ℝ) := by
    have hn := sum_get L.batches (fun b ↦ b.2.1 - 1)
    change _ = L.excess at hn
    exact_mod_cast hn.symm
  have ha : L.activity = ∑ i : Fin L.batches.length,
      (((L.batches.get i).2.1 - 1 : ℕ) : ℝ)^2 / (L.batches.get i).1 :=
    (sum_get L.batches _).symm
  rw [ha]
  apply CollisionBudget.activity_lower_bound N R hN hR
    (by simpa using hlen) (fun i ↦ (L.batches.get i).1) (fun i ↦ (L.batches.get i).2.1)
    (fun i ↦ (hb _ (List.get_mem _ _)).1) (fun i ↦ (hb _ (List.get_mem _ _)).2)
  rwa [← he]


end CollisionLedger

/-- An analytic operation record retains observable states or committed
values, together with the complete whole-edge retirement disclosure. -/
inductive RetirementObservation (N K : ℕ) (V : Type*)
  | query (state : MaskedState N V) (after : HardMatching.SurvivorRecord N K)
  | commit (batch : Finset (Position N)) (values : batch → V)
      (after : HardMatching.SurvivorRecord N K)

namespace RetirementObservation

/-- Every operation records the resulting survivor record. -/
def after {N K : ℕ} {V : Type*} : RetirementObservation N K V → HardMatching.SurvivorRecord N K
  | .query _ r => r
  | .commit _ _ r => r

/-- Query ordinals count only counterfactual queries. -/
def isQuery {N K : ℕ} {V : Type*} : RetirementObservation N K V → Bool
  | .query _ _ => true
  | .commit _ _ _ => false

end RetirementObservation

namespace Program

variable {N K B : ℕ}
open HardMatching HardMatching.SurvivorRecord

/-- Compute the actual analytic retirement ledger along the original program
path. Queries use their actual frozen replies; values follow the retained
path. The compatible-instance witness is preserved at every operation. -/
noncomputable def retirementLedger (I : InstanceIndex N K)
    (O : FrozenOracle N (HardVocabulary K B)) :
    {h : History N (HardVocabulary K B)} → (p : Program N (HardVocabulary K B) h) →
    (r : SurvivorRecord N K) → r.Compatible I → RetainedPath O p → CollisionLedger
  | _, .done _, _, _, _ => ⟨0, []⟩
  | _, .query state _ next, r, hI, path =>
      let r' := r.queryUpdate I hI state
      let L := retirementLedger I O (next (O.readState state)) r'
        (r.compatible_queryUpdate I hI state) path
      ⟨r'.retired.card - r.retired.card + L.queryVertices, L.batches⟩
  | _, .commit batch _ _ next, r, hI, path =>
      let r' := r.commitUpdate I hI batch
      let L := retirementLedger I O (next path.1) r'
        (r.compatible_commitUpdate I hI batch) path.2
      ⟨L.queryVertices,
        (N - r.retired.card, (batch \ r.retired).card,
          I.1.internalEdgeCount (batch \ r.retired)) :: L.batches⟩


/-- The actual operation trace exposes submitted states, committed values,
and the updated analytic record. It retains precisely the data needed to
identify adaptive prefix events in the joint instance--midpoint law. -/
noncomputable def retirementTrace (I : InstanceIndex N K)
    (O : FrozenOracle N (HardVocabulary K B)) :
    {h : History N (HardVocabulary K B)} → (p : Program N (HardVocabulary K B) h) →
    (r : SurvivorRecord N K) → r.Compatible I → RetainedPath O p →
      List (RetirementObservation N K (HardVocabulary K B))
  | _, .done _, _, _, _ => []
  | _, .query state _ next, r, hI, path =>
      let r' := r.queryUpdate I hI state
      RetirementObservation.query state r' ::
        retirementTrace I O (next (O.readState state)) r'
          (r.compatible_queryUpdate I hI state) path
  | _, .commit batch _ _ next, r, hI, path =>
      let r' := r.commitUpdate I hI batch
      RetirementObservation.commit batch path.1 r' ::
        retirementTrace I O (next path.1) r'
          (r.compatible_commitUpdate I hI batch) path.2

/-- The ledger has exactly one entry per actual commit, including commits
whose active batch is empty. -/
theorem retirementLedger_length (I : InstanceIndex N K)
    (O : FrozenOracle N (HardVocabulary K B))
    {h : History N (HardVocabulary K B)} (p : Program N (HardVocabulary K B) h)
    (r : SurvivorRecord N K) (hI : r.Compatible I) (path : RetainedPath O p) :
    (retirementLedger I O p r hI path).batches.length = retainedRoundCount O p path := by
  induction p generalizing r with
  | done complete => rfl
  | query state respects next ih => exact ih (O.readState state) _ _ path
  | commit batch nonempty fresh next ih =>
      simpa only [retirementLedger, List.length_cons, retainedRoundCount, Nat.add_comm] using
        congrArg (fun n : ℕ ↦ n + 1)
          (ih path.1 (r.commitUpdate I hI batch) (r.compatible_commitUpdate I hI batch) path.2)

/-- Every original matching edge is retired exactly once, by a query or its
first active commit. This doubled integer form avoids division conventions. -/
theorem retirementLedger_identity (I : InstanceIndex N K)
    (O : FrozenOracle N (HardVocabulary K B))
    {h : History N (HardVocabulary K B)} (p : Program N (HardVocabulary K B) h)
    (r : SurvivorRecord N K) (hI : r.Compatible I)
    (hcommitted : h.committed ⊆ r.retired) (path : RetainedPath O p) :
    N + 2 * (retirementLedger I O p r hI path).collisions =
      r.retired.card + (retirementLedger I O p r hI path).queryVertices +
        2 * (retirementLedger I O p r hI path).activeVertices := by
  induction p generalizing r with
  | done complete =>
      have hr : r.retired = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro i
        apply hcommitted
        rw [complete]
        exact Finset.mem_univ i
      simp [retirementLedger, CollisionLedger.collisions, CollisionLedger.activeVertices, hr]
  | query state respects next ih =>
      let r' := r.queryUpdate I hI state
      have hsub : r.retired ⊆ r'.retired :=
        subset_retirementClosure_left I.1 r.retired (r.queryHits I state)
      have hcard := Finset.card_le_card hsub
      have hh := ih (O.readState state) r' (r.compatible_queryUpdate I hI state)
        (hcommitted.trans hsub) path
      change N + 2 * (retirementLedger I O (next (O.readState state)) r' _ path).collisions =
        r.retired.card +
          (r'.retired.card - r.retired.card +
            (retirementLedger I O (next (O.readState state)) r' _ path).queryVertices) +
          2 * (retirementLedger I O (next (O.readState state)) r' _ path).activeVertices
      omega
  | @commit h batch nonempty fresh next ih =>
      let r' := r.commitUpdate I hI batch
      have hsub : r.retired ⊆ r'.retired := subset_retirementClosure_left I.1 r.retired batch
      have hbsub : batch ⊆ r'.retired := subset_retirementClosure_touched I.1 r.retired batch
      have hhist : (h.appendBatch batch fresh path.1).committed ⊆ r'.retired := by
        rw [History.appendBatch_committed]
        exact Finset.union_subset (hcommitted.trans hsub) hbsub
      have hh := ih path.1 r' (r.compatible_commitUpdate I hI batch) hhist path.2
      have hc := I.1.retirement_card_ledger r.retired batch hI.regionClosed
      change r'.retired.card + 2 * I.1.internalEdgeCount (batch \ r.retired) =
        r.retired.card + 2 * (batch \ r.retired).card at hc
      simp only [retirementLedger, CollisionLedger.collisions, CollisionLedger.activeVertices,
        List.map_cons, List.sum_cons]
      change N + 2 * (I.1.internalEdgeCount (batch \ r.retired) +
        (retirementLedger I O (next path.1) r' _ path.2).collisions) =
        r.retired.card + (retirementLedger I O (next path.1) r' _ path.2).queryVertices +
          2 * ((batch \ r.retired).card +
            (retirementLedger I O (next path.1) r' _ path.2).activeVertices)
      omega

/-- Every ledger batch uses at most the currently surviving vertices, and
no survivor population exceeds the original public length. -/
theorem retirementLedger_batch_bounds (I : InstanceIndex N K)
    (O : FrozenOracle N (HardVocabulary K B))
    {h : History N (HardVocabulary K B)} (p : Program N (HardVocabulary K B) h)
    (r : SurvivorRecord N K) (hI : r.Compatible I) (path : RetainedPath O p) :
    ∀ b ∈ (retirementLedger I O p r hI path).batches, b.2.1 ≤ b.1 ∧ b.1 ≤ N := by
  induction p generalizing r with
  | done complete => simp [retirementLedger]
  | query state respects next ih => exact ih (O.readState state) _ _ path
  | commit batch nonempty fresh next ih =>
      intro b hb
      change b ∈ _ :: _ at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · constructor
        · have hs : batch \ r.retired ⊆ Finset.univ \ r.retired :=
            by
              intro i hi
              exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
          have hc := Finset.card_le_card hs
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ r.retired),
            Finset.card_univ, Fintype.card_fin] at hc
          exact hc
        · exact Nat.sub_le _ _
      · exact ih path.1 _ _ path.2 b hb


/-- Specialization of the actual integer ledger to the initial empty record,
written in the manuscript's edge rather than endpoint normalization. -/
theorem retirementLedger_initial_identity (I : InstanceIndex N K)
    (O : FrozenOracle N (HardVocabulary K B))
    (p : Program N (HardVocabulary K B) (History.empty N (HardVocabulary K B)))
    (path : RetainedPath O p) :
    let L := retirementLedger I O p (SurvivorRecord.initial N K)
      (SurvivorRecord.compatible_initial I) path
    (N : ℝ)/2 = (L.queryVertices : ℝ)/2 + L.activeVertices - L.collisions := by
  let L := retirementLedger I O p (SurvivorRecord.initial N K)
    (SurvivorRecord.compatible_initial I) path
  have hi := retirementLedger_identity I O p (SurvivorRecord.initial N K)
    (SurvivorRecord.compatible_initial I) (by simp [History.empty]) path
  have hh : N + 2 * L.collisions = L.queryVertices + 2 * L.activeVertices := by
    simpa only [L, SurvivorRecord.initial, Finset.card_empty, Nat.zero_add] using hi
  have hr : (N : ℝ) + 2 * (L.collisions : ℝ) =
      (L.queryVertices : ℝ) + 2 * (L.activeVertices : ℝ) := by exact_mod_cast hh
  change (N : ℝ)/2 = (L.queryVertices : ℝ)/2 + L.activeVertices - L.collisions
  linarith

/-- The actual complete execution supplies the activity input needed by the
collision-tail theorem whenever query deletions and rounds are small. -/
theorem retirementLedger_initial_activity (I : InstanceIndex N K)
    (O : FrozenOracle N (HardVocabulary K B))
    (p : Program N (HardVocabulary K B) (History.empty N (HardVocabulary K B)))
    (path : RetainedPath O p) (R : ℕ) (hN : 0 < N) (hR : 0 < R)
    (hrounds : retainedRoundCount O p path ≤ R) (hRN : (R : ℝ) ≤ (N : ℝ)/8)
    (hqueries : ((retirementLedger I O p (SurvivorRecord.initial N K)
      (SurvivorRecord.compatible_initial I) path).queryVertices : ℝ)/2 ≤ (N : ℝ)/4) :
    (N : ℝ)/(64*(R : ℝ)) ≤
      (retirementLedger I O p (SurvivorRecord.initial N K)
        (SurvivorRecord.compatible_initial I) path).activity := by
  let L := retirementLedger I O p (SurvivorRecord.initial N K)
    (SurvivorRecord.compatible_initial I) path
  have hlen : L.batches.length ≤ R := by
    rw [retirementLedger_length]
    exact hrounds
  have hb := retirementLedger_batch_bounds I O p (SurvivorRecord.initial N K)
    (SurvivorRecord.compatible_initial I) path
  apply L.activity_lower_bound N R hN hR hlen hb
  have hledger := retirementLedger_initial_identity I O p path
  change (N : ℝ)/2 = (L.queryVertices : ℝ)/2 + L.activeVertices - L.collisions at hledger
  have he := L.activeVertices_le_excess_add_length
  have he' : (L.activeVertices : ℝ) ≤ L.excess + L.batches.length := by exact_mod_cast he
  have hl' : (L.batches.length : ℝ) ≤ R := by exact_mod_cast hlen
  have hz : (0 : ℝ) ≤ L.collisions := Nat.cast_nonneg _
  change (L.queryVertices : ℝ)/2 ≤ (N : ℝ)/4 at hqueries
  linarith


end Program
end ForestSampling
