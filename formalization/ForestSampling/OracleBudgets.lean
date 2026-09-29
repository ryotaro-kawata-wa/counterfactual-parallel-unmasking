import ForestSampling.ProgramMidpoint

set_option autoImplicit false

namespace ForestSampling

universe u v

namespace Program

variable {N : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Pathwise budgets for a fixed frozen oracle. Queries follow that oracle's
actual reply, while every possible fresh batch assignment is still covered.
This permits bounds depending on the preprocessing bank actually realized by
that oracle, as in the current finite upper theorem. -/
def WithinOracleBudgets (O : FrozenOracle N V) :
    {h : History N V} → Program N V h → ℕ → ℕ → Prop
  | _, .done _, _, _ => True
  | _, .query state _ next, Q, R =>
      0 < Q ∧ WithinOracleBudgets O (next (O.readState state)) (Q - 1) R
  | _, .commit _ _ _ next, Q, R =>
      0 < R ∧ ∀ z, WithinOracleBudgets O (next z) Q (R - 1)

/-- A budget valid for all arbitrary replies is also valid for each particular
frozen map. The reverse implication is deliberately not assumed. -/
theorem WithinBudgets.withinOracleBudgets (O : FrozenOracle N V)
    {h : History N V} {p : Program N V h} {Q R : ℕ}
    (hbudget : p.WithinBudgets Q R) : p.WithinOracleBudgets O Q R := by
  induction p generalizing Q R with
  | done complete => trivial
  | query state respects next ih =>
      exact ⟨hbudget.1, ih (O.readState state) (hbudget.2 (O.readState state))⟩
  | commit batch nonempty fresh next ih =>
      exact ⟨hbudget.1, fun z ↦ ih z (hbudget.2 z)⟩

/-- Oracle-specific budgets bound every retained path, regardless of whether
commits use oracle products, exact joint conditionals, or midpoint kernels. -/
theorem retainedPath_withinOracleBudgets (O : FrozenOracle N V)
    {h : History N V} (p : Program N V h) (path : RetainedPath O p)
    (Q R : ℕ) (hbudget : p.WithinOracleBudgets O Q R) :
    retainedQueryCount O p path ≤ Q ∧ retainedRoundCount O p path ≤ R := by
  induction p generalizing Q R with
  | done complete => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | query state respects next ih =>
      obtain ⟨hQ, hnext⟩ := hbudget
      obtain ⟨hq, hr⟩ := ih (O.readState state) path (Q - 1) R hnext
      change 1 + retainedQueryCount O (next (O.readState state)) path ≤ Q ∧
        retainedRoundCount O (next (O.readState state)) path ≤ R
      omega
  | commit batch nonempty fresh next ih =>
      obtain ⟨hR, hnext⟩ := hbudget
      obtain ⟨hq, hr⟩ := ih path.1 path.2 Q (R - 1) (hnext path.1)
      change retainedQueryCount O (next path.1) path.2 ≤ Q ∧
        1 + retainedRoundCount O (next path.1) path.2 ≤ R
      omega

/-- For a nonempty vocabulary, all finite query prefixes extend to retained
paths. Hence the inductive oracle-specific budget is exactly the intended
all-path resource statement, not merely a sufficient syntactic test. -/
theorem withinOracleBudgets_iff_retainedCounts [Nonempty V]
    (O : FrozenOracle N V) {h : History N V} (p : Program N V h) (Q R : ℕ) :
    p.WithinOracleBudgets O Q R ↔
      ∀ path : RetainedPath O p,
        retainedQueryCount O p path ≤ Q ∧ retainedRoundCount O p path ≤ R := by
  constructor
  · intro hb path
    exact retainedPath_withinOracleBudgets O p path Q R hb
  · intro hall
    induction p generalizing Q R with
    | done complete => trivial
    | query state respects next ih =>
        have hpath : Nonempty (RetainedPath O (next (O.readState state))) := by
          exact ⟨replay O _ (fun _ ↦ Classical.choice (inferInstance : Nonempty V))⟩
        obtain ⟨path⟩ := hpath
        have hcount := (hall path).1
        refine ⟨by change 1 + _ ≤ Q at hcount; omega, ?_⟩
        apply ih (O.readState state)
        intro path
        have hh := hall path
        change 1 + retainedQueryCount O (next (O.readState state)) path ≤ Q ∧
          retainedRoundCount O (next (O.readState state)) path ≤ R at hh
        omega
    | commit batch nonempty fresh next ih =>
        let z : batch → V := fun _ ↦ Classical.choice (inferInstance : Nonempty V)
        let path := replay O (next z) (fun _ ↦ Classical.choice (inferInstance : Nonempty V))
        have hcount := (hall ⟨z, path⟩).2
        refine ⟨by change 1 + _ ≤ R at hcount; omega, ?_⟩
        intro z
        apply ih z
        intro path
        have hh := hall ⟨z, path⟩
        change retainedQueryCount O (next z) path ≤ Q ∧
          1 + retainedRoundCount O (next z) path ≤ R at hh
        omega

end Program

namespace Sampler

variable {N : ℕ} {V : Type u} {Seed : Type v} [Fintype V] [DecidableEq V]

/-- A fixed oracle's realized-preprocessing budget, uniform over seeds and all
sampled outcomes. The distinguished all-mask reply stays outside the query
counter, matching the existing submission convention. -/
def WithinOracleBudgets (A : Sampler N V Seed) (O : FrozenOracle N V) (Q R : ℕ) : Prop :=
  ∀ w, (A.program w (O.readState (MaskedState.allMask N V))).WithinOracleBudgets O Q R

/-- The earlier universal-reply contract implies the sharper oracle-indexed
resource semantics when the same public bound is available. -/
theorem WithinBudgets.withinOracleBudgets {A : Sampler N V Seed} {Q R : ℕ}
    (hbudget : A.WithinBudgets Q R) (O : FrozenOracle N V) :
    A.WithinOracleBudgets O Q R := by
  intro w
  exact Program.WithinBudgets.withinOracleBudgets O (hbudget w _)

end Sampler
end ForestSampling
