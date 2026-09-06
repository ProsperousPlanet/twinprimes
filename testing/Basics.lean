def blocked (TPC p : Nat) : Prop :=
  (TPC % p = 1 ∨ TPC % p = p - 1) ∧
  TPC - 1 ≠ p ∧
  TPC + 1 ≠ p


def lift (TPC M k : Nat) : Nat :=
  TPC + k * M


-- Apply the same operation recursively to a completed state.

def iterateState {State : Type} (next : State → State) :
    Nat → State → State
  | 0, state =>
      state
  | Nat.succ n, state =>
      iterateState next n (next state)


-- If the starting state survives, and one application
-- of the recursive rule always preserves survival,
-- then every later recursively generated state survives.

theorem recursive_carry
    {State : Type}
    (survives : State → Prop)
    (next : State → State)
    (one_step :
      ∀ state,
        survives state →
        survives (next state))
    (start : State)
    (start_survives : survives start) :
    ∀ n,
      survives (iterateState next n start) := by

  intro n

  induction n generalizing start with

  | zero =>
      exact start_survives

  | succ n ih =>
      exact ih
        (next start)
        (one_step start start_survives)


#check recursive_carry
