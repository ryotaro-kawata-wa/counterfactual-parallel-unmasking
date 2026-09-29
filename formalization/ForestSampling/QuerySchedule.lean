import ForestSampling.Algorithm

set_option autoImplicit false

namespace ForestSampling

/-- One actual counterfactual state submission, with the no-remasking
obligation retained in its type. All masked rows share this one query. -/
structure Submission {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (h : History N V) where
  state : MaskedState N V
  respects : state.RespectsHistory h

namespace Submission

variable {N : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable {h : History N V}

abbrev Reply (q : Submission h) := MaskedPosition q.state → FinDist V

end Submission

namespace Program

variable {N : ℕ} {V Index : Type*} [Fintype V] [DecidableEq V] [DecidableEq Index]
variable {h : History N V}

/-- Increasing either all-path resource allowance preserves the contract. -/
theorem withinBudgets_mono (p : Program N V h) {Q R Q' R' : ℕ}
    (hp : WithinBudgets p Q R) (hQ : Q ≤ Q') (hR : R ≤ R') :
    WithinBudgets p Q' R' := by
  induction p generalizing Q R Q' R' with
  | done complete => trivial
  | query state respects next ih =>
      exact ⟨lt_of_lt_of_le hp.1 hQ, fun reply ↦
        ih reply (hp.2 reply) (Nat.sub_le_sub_right hQ 1) hR⟩
  | commit batch nonempty fresh next ih =>
      exact ⟨lt_of_lt_of_le hp.1 hR, fun z ↦
        ih z (hp.2 z) hQ (Nat.sub_le_sub_right hR 1)⟩

/-- A reply table stores only replies already supplied through actual
query constructors; its arbitrary initial values are overwritten by the
schedule before they can be used for a scheduled readout. -/
abbrev ReplyTable (queries : Index → Submission h) := ∀ i, (queries i).Reply

/-- Enumerate a finite public query schedule and then continue with the
collected reply table. Each index creates exactly one `Program.query`. -/
noncomputable def runQuerySchedule (queries : Index → Submission h) :
    List Index → ReplyTable queries → (ReplyTable queries → Program N V h) → Program N V h
  | [], replies, next => next replies
  | i :: todo, replies, next =>
      .query (queries i).state (queries i).respects (fun reply ↦
        runQuerySchedule queries todo (Function.update replies i reply) next)

/-- The deterministic table update performed when a fixed frozen oracle
answers every state in the finite schedule. -/
noncomputable def fillQueryReplies (queries : Index → Submission h) (O : FrozenOracle N V) :
    List Index → ReplyTable queries → ReplyTable queries
  | [], replies => replies
  | i :: todo, replies =>
      fillQueryReplies queries O todo (Function.update replies i (O.readState (queries i).state))

theorem fillQueryReplies_at (queries : Index → Submission h) (O : FrozenOracle N V)
    (todo : List Index) (replies : ReplyTable queries) (i : Index) :
    fillQueryReplies queries O todo replies i =
      if i ∈ todo then O.readState (queries i).state else replies i := by
  induction todo generalizing replies with
  | nil => simp [fillQueryReplies]
  | cons j todo ih =>
      simp only [fillQueryReplies, ih, List.mem_cons]
      by_cases hi : i ∈ todo
      · simp [hi]
      · by_cases hij : i = j
        · subst i
          simp [hi]
        · simp [hi, hij]

/-- A schedule covering every index replaces the whole table by the
actual frozen oracle replies, independently of its initial contents. -/
theorem fillQueryReplies_eq (queries : Index → Submission h) (O : FrozenOracle N V)
    (todo : List Index) (hcover : ∀ i, i ∈ todo) (replies : ReplyTable queries) :
    fillQueryReplies queries O todo replies = (fun i ↦ O.readState (queries i).state) := by
  funext i
  rw [fillQueryReplies_at, if_pos (hcover i)]

/-- Concrete query enumeration has exactly the expected evaluator: the
continuation receives the answers to the listed states and no oracle access
is used when constructing the schedule. -/
theorem eval_runQuerySchedule (queries : Index → Submission h) (O : FrozenOracle N V)
    (todo : List Index) (replies : ReplyTable queries)
    (next : ReplyTable queries → Program N V h) :
    eval O (runQuerySchedule queries todo replies next) =
      eval O (next (fillQueryReplies queries O todo replies)) := by
  induction todo generalizing replies with
  | nil => rfl
  | cons i todo ih => exact ih _

/-- The all-path resource contract counts actual query constructors. It
quantifies over every possible reply, so this bound survives failed screens. -/
theorem runQuerySchedule_withinBudgets (queries : Index → Submission h)
    (todo : List Index) (replies : ReplyTable queries)
    (next : ReplyTable queries → Program N V h) (Q R : ℕ)
    (hnext : ∀ replies, WithinBudgets (next replies) Q R) :
    WithinBudgets (runQuerySchedule queries todo replies next) (todo.length + Q) R := by
  induction todo generalizing replies with
  | nil => simpa [runQuerySchedule] using hnext replies
  | cons i todo ih =>
      constructor
      · simp
      · intro reply
        have hbudget : (i :: todo).length + Q - 1 = todo.length + Q := by simp
        change WithinBudgets _ ((i :: todo).length + Q - 1) R
        rw [hbudget]
        exact ih (Function.update replies i reply)

end Program
end ForestSampling
