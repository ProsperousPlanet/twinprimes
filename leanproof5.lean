import Init.Omega


-- A number is prime when it is at least 2
-- and has no proper divisor at least 2.

def IsPrime (n : Nat) : Prop :=
  2 ≤ n ∧
  ∀ d,
    2 ≤ d →
    d < n →
    ¬ d ∣ n


-- A twin center has prime unit neighbors.

def TwinCenter (c : Nat) : Prop :=
  IsPrime (c - 1) ∧ IsPrime (c + 1)


-- Carry a state forward by whole copies
-- of a completed period M.

def lift (c M k : Nat) : Nat :=
  c + k * M


-- The complete M-state is unchanged by the carry.

theorem carry_preserves_state
    (c M k : Nat) :
    lift c M k % M = c % M := by

  simp [lift, Nat.add_mod]


-- More strongly:
-- if q is already contained in the completed period M,
-- then its individual clock state can never be changed
-- by any later whole-period carry.

theorem completed_clock_is_immutable
    (c M q k : Nat)
    (hq : q ∣ M) :
    lift c M k % q = c % q := by

  have hzero : M % q = 0 :=
    Nat.mod_eq_zero_of_dvd hq

  simp [lift, Nat.add_mod, Nat.mul_mod, hzero]


-- The two reflected boundary phases of a clock.

def BoundaryClosed (c q : Nat) : Prop :=
  c % q = 1 ∨ c % q = q - 1


-- Therefore an already completed clock can never
-- change whether the carried state lies on its
-- +1 or -1 boundary.

theorem completed_boundary_is_immutable
    (c M q k : Nat)
    (hq : q ∣ M) :
    BoundaryClosed (lift c M k) q ↔
    BoundaryClosed c q := by

  unfold BoundaryClosed

  rw [completed_clock_is_immutable
        c M q k hq]


-- A proper divisor closes one of the two neighbors.

def closes (c d : Nat) : Prop :=
  (d ∣ c - 1 ∧ c - 1 ≠ d) ∨
  (d ∣ c + 1 ∧ c + 1 ≠ d)


-- "known d" means that d belongs to the
-- completed divisor/clock state.

def Accepted
    (known : Nat → Prop)
    (c : Nat) : Prop :=
  ∀ d,
    known d →
    ¬ closes c d


-- The state is complete for c when every possible
-- proper divisor of either neighbor is already known.

def CompleteFor
    (known : Nat → Prop)
    (c : Nat) : Prop :=

  (∀ d,
      2 ≤ d →
      d < c - 1 →
      d ∣ c - 1 →
      known d)

  ∧

  (∀ d,
      2 ≤ d →
      d < c + 1 →
      d ∣ c + 1 →
      known d)


-- Survival against a complete divisor state
-- proves that both neighbors are prime.

theorem accepted_is_twin
    (known : Nat → Prop)
    (c : Nat)
    (hc : 3 ≤ c)
    (hcomplete : CompleteFor known c)
    (haccepted : Accepted known c) :
    TwinCenter c := by

  constructor

  · constructor

    · omega

    · intro d hd2 hdlt hddiv

      have hknown :=
        hcomplete.1 d hd2 hdlt hddiv

      have hopen :=
        haccepted d hknown

      apply hopen

      left

      constructor
      · exact hddiv
      · omega


  · constructor

    · omega

    · intro d hd2 hdlt hddiv

      have hknown :=
        hcomplete.2 d hd2 hdlt hddiv

      have hopen :=
        haccepted d hknown

      apply hopen

      right

      constructor
      · exact hddiv
      · omega


-- Package exactly what is required for a
-- completed surviving state.

def Certified
    (known : Nat → Prop)
    (c : Nat) : Prop :=
  3 ≤ c ∧
  Accepted known c ∧
  CompleteFor known c


theorem certified_is_twin
    (known : Nat → Prop)
    (c : Nat)
    (h : Certified known c) :
    TwinCenter c := by

  exact accepted_is_twin
    known
    c
    h.1
    h.2.2
    h.2.1


-- Repeated completed-state handoff.

def iterateState
    (next : Nat → Nat) :
    Nat → Nat → Nat
  | 0, c =>
      c
  | Nat.succ n, c =>
      iterateState next n (next c)


-- If every completed successor is certified,
-- then every recursively generated state is
-- again a twin center.

theorem recursive_certified_carry
    (known : Nat → Nat → Prop)
    (next : Nat → Nat)

    (next_certified :
      ∀ c,
        Certified
          (known c)
          (next c))

    (start : Nat)
    (start_is_twin :
      TwinCenter start) :

    ∀ n,
      TwinCenter
        (iterateState next n start) := by

  intro n

  induction n generalizing start with

  | zero =>
      exact start_is_twin

  | succ n ih =>

      have hnext :
          TwinCenter (next start) :=
        certified_is_twin
          (known start)
          (next start)
          (next_certified start)

      exact ih
        (next start)
        hnext


-- If every completed successor is larger,
-- the recursive centers move strictly forward.

theorem recursive_centers_move_forward
    (next : Nat → Nat)
    (grows :
      ∀ c,
        c < next c) :
    ∀ c n,
      iterateState next n c ≤
      iterateState next (n + 1) c := by

  intro c n

  induction n generalizing c with

  | zero =>
      simp [iterateState]
      exact Nat.le_of_lt (grows c)

  | succ n ih =>
      simp [iterateState]
      exact ih (next c)


#check carry_preserves_state
#check completed_clock_is_immutable
#check completed_boundary_is_immutable
#check accepted_is_twin
#check certified_is_twin
#check recursive_certified_carry
#check recursive_centers_move_forward
