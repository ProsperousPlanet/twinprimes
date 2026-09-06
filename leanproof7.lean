import Init.Omega
import Init.Data.Nat.Coprime
import Init.Data.Nat.Div.Lemmas


-- Pascal recursion:
-- every new relation either uses the new object
-- or does not use it.

def choose : Nat → Nat → Nat
  | _, 0 =>
      1
  | 0, Nat.succ _ =>
      0
  | Nat.succ n, Nat.succ r =>
      choose n r + choose n (Nat.succ r)


theorem pascal_extension
    (n r : Nat) :
    choose (Nat.succ n) (Nat.succ r)
      =
    choose n r + choose n (Nat.succ r) := by

  rfl


-- Carry a completed state forward.

def lift
    (c M k : Nat) : Nat :=
  c + k * M


-- Every old clock contained in M is immutable.

theorem completed_clock_is_immutable
    (c M q k : Nat)
    (hq : q ∣ M) :
    lift c M k % q = c % q := by

  have hzero :
      M % q = 0 :=
    Nat.mod_eq_zero_of_dvd hq

  simp [lift, Nat.add_mod, Nat.mul_mod, hzero]


-- A clock makes only the binary decision:
-- boundary or not boundary.

def ClosedBy
    (c q : Nat) : Prop :=
  c % q = 1 ∨
  c % q = q - 1


-- Every old binary decision is immutable.

theorem binary_choice_is_immutable
    (c M q k : Nat)
    (hq : q ∣ M) :
    ClosedBy (lift c M k) q ↔
    ClosedBy c q := by

  unfold ClosedBy

  rw [
    completed_clock_is_immutable
      c M q k hq
  ]


-- CRT bridge:
-- if M and the new cycle p are coprime,
-- two different lifts among the first p copies
-- cannot occupy the same p-state.

theorem coprime_lifts_are_distinct
    (c M p k1 k2 : Nat)
    (hcop : Nat.Coprime M p)
    (hk1 : k1 < p)
    (hk2 : k2 < p)
    (hres :
      lift c M k1 % p =
      lift c M k2 % p) :
    k1 = k2 := by

  rcases Nat.le_total k1 k2 with hle | hle

  · rcases Nat.le.dest hle with ⟨d, hd⟩

    have hk2eq :
        k2 = k1 + d :=
      hd.symm

    subst k2

    rcases Nat.mod_eq_mod_iff.mp hres with
      ⟨a, b, hEq⟩

    have hEq' :
        (c + k1 * M) + a * p
          =
        (c + k1 * M) + (d * M + b * p) := by

      simpa [
        lift,
        Nat.add_mul,
        Nat.add_assoc
      ] using hEq

    have hEq'' :
        a * p = d * M + b * p :=
      Nat.add_left_cancel hEq'

    have hpa :
        p ∣ a * p :=
      Nat.dvd_mul_left p a

    have hpb :
        p ∣ b * p :=
      Nat.dvd_mul_left p b

    have hsum :
        p ∣ d * M + b * p := by

      rw [← hEq'']

      exact hpa

    have hdM :
        p ∣ d * M :=
      (Nat.dvd_add_iff_left hpb).2 hsum

    have hd :
        p ∣ d := by

      apply hcop.symm.dvd_of_dvd_mul_left

      simpa [Nat.mul_comm] using hdM

    have hdlt :
        d < p := by

      omega

    have hz :
        d % p = 0 :=
      Nat.mod_eq_zero_of_dvd hd

    rw [Nat.mod_eq_of_lt hdlt] at hz

    omega


  · rcases Nat.le.dest hle with ⟨d, hd⟩

    have hk1eq :
        k1 = k2 + d :=
      hd.symm

    subst k1

    rcases Nat.mod_eq_mod_iff.mp hres with
      ⟨a, b, hEq⟩

    have hEq' :
        (c + k2 * M) + (d * M + a * p)
          =
        (c + k2 * M) + b * p := by

      simpa [
        lift,
        Nat.add_mul,
        Nat.add_assoc
      ] using hEq

    have hEq'' :
        d * M + a * p = b * p :=
      Nat.add_left_cancel hEq'

    have hpa :
        p ∣ a * p :=
      Nat.dvd_mul_left p a

    have hpb :
        p ∣ b * p :=
      Nat.dvd_mul_left p b

    have hsum :
        p ∣ d * M + a * p := by

      rw [hEq'']

      exact hpb

    have hdM :
        p ∣ d * M :=
      (Nat.dvd_add_iff_left hpa).2 hsum

    have hd :
        p ∣ d := by

      apply hcop.symm.dvd_of_dvd_mul_left

      simpa [Nat.mul_comm] using hdM

    have hdlt :
        d < p := by

      omega

    have hz :
        d % p = 0 :=
      Nat.mod_eq_zero_of_dvd hd

    rw [Nat.mod_eq_of_lt hdlt] at hz

    omega


-- A new coprime cycle cannot close every copy.
--
-- There are already three distinct p-states among
-- lifts 0, 1 and 2 when p > 2, while there are only
-- two closed boundary states: +1 and -1.

theorem new_cycle_has_survivor
    (c M p : Nat)
    (hp : 2 < p)
    (hcop : Nat.Coprime M p) :
    ∃ k,
      k < p ∧
      ¬ ClosedBy (lift c M k) p := by

  have h01 :
      lift c M 0 % p ≠
      lift c M 1 % p := by

    intro h

    have hk :=
      coprime_lifts_are_distinct
        c M p 0 1
        hcop
        (by omega)
        (by omega)
        h

    omega


  have h02 :
      lift c M 0 % p ≠
      lift c M 2 % p := by

    intro h

    have hk :=
      coprime_lifts_are_distinct
        c M p 0 2
        hcop
        (by omega)
        (by omega)
        h

    omega


  have h12 :
      lift c M 1 % p ≠
      lift c M 2 % p := by

    intro h

    have hk :=
      coprime_lifts_are_distinct
        c M p 1 2
        hcop
        (by omega)
        (by omega)
        h

    omega


  by_cases h0 :
      ClosedBy (lift c M 0) p

  · by_cases h1 :
        ClosedBy (lift c M 1) p

    · by_cases h2 :
          ClosedBy (lift c M 2) p

      · unfold ClosedBy at h0 h1 h2

        rcases h0 with h0 | h0 <;>
        rcases h1 with h1 | h1 <;>
        rcases h2 with h2 | h2 <;>
        omega

      · exact ⟨2, by omega, h2⟩

    · exact ⟨1, by omega, h1⟩

  · exact ⟨0, by omega, h0⟩


-- The full bridge:
--
-- choose a surviving lift of the new coprime cycle.
-- Every old binary decision remains exactly unchanged,
-- while the new cycle also leaves this copy open.

theorem crt_bridge
    (c M p : Nat)
    (hp : 2 < p)
    (hcop : Nat.Coprime M p) :
    ∃ k,
      k < p
      ∧
      (∀ q,
        q ∣ M →
        (ClosedBy (lift c M k) q ↔
         ClosedBy c q))
      ∧
      ¬ ClosedBy (lift c M k) p := by

  obtain ⟨k, hk, hnew⟩ :=
    new_cycle_has_survivor
      c M p hp hcop

  refine ⟨k, hk, ?_, hnew⟩

  intro q hq

  exact binary_choice_is_immutable
    c M q k hq


#check pascal_extension
#check completed_clock_is_immutable
#check binary_choice_is_immutable

#check coprime_lifts_are_distinct
#check new_cycle_has_survivor
#check crt_bridge
