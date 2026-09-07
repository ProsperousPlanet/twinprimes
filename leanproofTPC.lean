import Init.Omega
import Init.Data.Nat.Coprime
import Init.Data.Nat.Div.Lemmas


namespace TwinPrimeClock



/-!
=====================================================================
1. Prime clocks: the sieve
=====================================================================

The construction does not accept arbitrary moduli as clocks.

The opened clock list P is the sieve state.  Every member of P is prime,
every member was opened before the current candidate p, and every earlier
integer greater than 1 is already divisible by some opened clock.

A new candidate p opens only when none of the opened clocks divides it.
Therefore an opened candidate has no proper divisor and is prime.
-/


def PrimeNat
    (p : Nat) : Prop :=
  1 < p
    ∧
  ∀ d,
    d ∣ p →
    d = 1 ∨ d = p


structure SieveState
    (P : List Nat)
    (p : Nat) : Prop where
  clocks_are_prime :
    ∀ q,
      q ∈ P →
      PrimeNat q

  clocks_are_earlier :
    ∀ q,
      q ∈ P →
      q < p

  earlier_numbers_are_covered :
    ∀ n,
      1 < n →
      n < p →
      ∃ q,
        q ∈ P ∧ q ∣ n


-- After the locked 2,3 base has been established, every later clock
-- candidate is greater than 2.  It opens exactly when no old clock divides it.

def OpensClock
    (P : List Nat)
    (p : Nat) : Prop :=
  2 < p
    ∧
  ∀ q,
    q ∈ P →
    p % q ≠ 0


theorem open_clock_not_divisible
    (P : List Nat)
    (p q : Nat)
    (hopen : OpensClock P p)
    (hq : q ∈ P) :
    ¬ q ∣ p := by

  intro hdiv

  have hzero :
      p % q = 0 :=
    Nat.mod_eq_zero_of_dvd hdiv

  exact
    (hopen.2 q hq) hzero


-- This is the Sieve of Eratosthenes step used by the construction:
-- a number opens a new clock only if it is prime.

theorem sieve_open_is_prime
    (P : List Nat)
    (p : Nat)
    (hstate : SieveState P p)
    (hopen : OpensClock P p) :
    PrimeNat p := by

  have hp2 :
      2 < p :=
    hopen.1

  constructor

  · exact
      Nat.lt_trans
        (by decide : 1 < 2)
        hp2

  · intro d hd

    by_cases h1 : d = 1

    · exact Or.inl h1

    by_cases hpEq : d = p

    · exact Or.inr hpEq

    exfalso

    have hp0 :
        0 < p :=
      Nat.zero_lt_of_lt hp2

    have hdpos :
        0 < d :=
      Nat.pos_of_dvd_of_pos hd hp0

    have hdle :
        d ≤ p :=
      Nat.le_of_dvd hp0 hd

    have honele :
        1 ≤ d :=
      Nat.succ_le_of_lt hdpos

    have hdgt1 :
        1 < d :=
      Nat.lt_of_le_of_ne
        honele
        (Ne.symm h1)

    have hdltp :
        d < p :=
      Nat.lt_of_le_of_ne
        hdle
        hpEq

    obtain ⟨q, hqmem, hqdvd⟩ :=
      hstate.earlier_numbers_are_covered
        d hdgt1 hdltp

    have hqdp :
        q ∣ p :=
      Nat.dvd_trans hqdvd hd

    exact
      (open_clock_not_divisible
        P p q hopen hqmem) hqdp


-- Conversely, a prime candidate greater than 2 cannot be divisible by an
-- earlier prime clock, so it necessarily opens.

theorem prime_candidate_opens_clock
    (P : List Nat)
    (p : Nat)
    (hstate : SieveState P p)
    (hp : 2 < p)
    (hprime : PrimeNat p) :
    OpensClock P p := by

  constructor

  · exact hp

  · intro q hqmem

    intro hzero

    have hqdvd :
        q ∣ p :=
      Nat.dvd_of_mod_eq_zero hzero

    rcases hprime.2 q hqdvd with hq1 | hqp

    · have hqgt1 :
          1 < q :=
        (hstate.clocks_are_prime q hqmem).1

      omega

    · have hqlt :
          q < p :=
        hstate.clocks_are_earlier q hqmem

      omega


-- Thus the sieve opens exactly the prime candidates.

theorem sieve_open_iff_prime
    (P : List Nat)
    (p : Nat)
    (hstate : SieveState P p)
    (hp : 2 < p) :
    OpensClock P p ↔ PrimeNat p := by

  constructor

  · intro hopen

    exact
      sieve_open_is_prime
        P p hstate hopen

  · intro hprime

    exact
      prime_candidate_opens_clock
        P p hstate hp hprime


-- Since every old clock was opened earlier, the new clock is genuinely new.

theorem opened_clock_is_new
    (P : List Nat)
    (p : Nat)
    (hstate : SieveState P p) :
    p ∉ P := by

  intro hpMem

  have hlt :
      p < p :=
    hstate.clocks_are_earlier p hpMem

  omega

-- A position is open in every currently opened clock.

def AllClocksOpen
    (P : List Nat)
    (x : Nat) : Prop :=
  ∀ q,
    q ∈ P →
    x % q ≠ 0


-- This is the exact finite walk used by phases(p):
-- start after p and advance p*p positions.

def phaseEnd
    (p : Nat) : Nat :=
  p + p * p


-- A saved phase position is one of the values that Python
-- would append to A.

def PhasePosition
    (P : List Nat)
    (p x : Nat) : Prop :=
  p < x
    ∧ x ≤ phaseEnd p
    ∧ AllClocksOpen (p :: P) x

    def CrossPosition
    (P : List Nat)
    (p n : Nat) : Prop :=
  ∃ a b,
    PhasePosition P p a
      ∧ PhasePosition P p b
      ∧ n = a * b
/-!
=====================================================================
2. Pascal relationships
=====================================================================

A level is represented by a finite list of opened clocks.

For any number r, relationProducts P r contains the products obtained
by choosing exactly r clocks from P.

When a new clock p is added, every old relationship has exactly two
possibilities:

  * do not use p;
  * use p, multiplying the old relationship by p.

This is the Pascal recursion used by the construction.
-/


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


def extendRelation
    (R p : Nat) : Nat :=
  R * p


def relationProducts : List Nat → Nat → List Nat
  | _, 0 =>
      [1]
  | [], Nat.succ _ =>
      []
  | p :: P, Nat.succ r =>
      (relationProducts P r).map
          (fun R => extendRelation R p)
        ++
      relationProducts P (Nat.succ r)


-- Once the sieve opens p and p is adjoined to P, it is literally a
-- degree-one Pascal relationship.

theorem new_clock_is_degree_one_relation
    (P : List Nat)
    (p : Nat) :
    p ∈ relationProducts (p :: P) 1 := by

  simp [
    relationProducts,
    extendRelation
  ]


-- The recursion itself is the Pascal split:
-- old degree-(r+1) relationships, together with degree-r
-- relationships extended by the new clock p.

theorem pascal_relation_split
    (P : List Nat)
    (p r : Nat) :
    relationProducts (p :: P) (Nat.succ r)
      =
    (relationProducts P r).map
        (fun R => extendRelation R p)
      ++
    relationProducts P (Nat.succ r) := by

  rfl


-- The number of generated relationships is exactly the corresponding
-- entry of Pascal's triangle.

theorem relation_count_is_choose
    (P : List Nat)
    (r : Nat) :
    (relationProducts P r).length
      =
    choose P.length r := by

  induction P generalizing r with

  | nil =>
      cases r <;>
      rfl

  | cons p P ih =>
      cases r with

      | zero =>
          rfl

      | succ r =>
          simp [
            relationProducts,
            choose,
            ih
          ]


-- The count extension is literally the Pascal theorem already proved.

theorem relation_count_pascal_extension
    (P : List Nat)
    (p r : Nat) :
    (relationProducts (p :: P) (Nat.succ r)).length
      =
    choose (Nat.succ P.length) (Nat.succ r) := by

  calc
    (relationProducts (p :: P) (Nat.succ r)).length
        =
      (relationProducts P r).length
        +
      (relationProducts P (Nat.succ r)).length := by
          simp [relationProducts]

    _ =
      choose P.length r
        +
      choose P.length (Nat.succ r) := by
          rw [
            relation_count_is_choose P r,
            relation_count_is_choose P (Nat.succ r)
          ]

    _ =
      choose (Nat.succ P.length) (Nat.succ r) := by
          exact
            (pascal_extension P.length r).symm


-- A previous relationship remains present when a new clock is added.

theorem old_relation_mem_next
    (P : List Nat)
    (p r R : Nat)
    (hR : R ∈ relationProducts P r) :
    R ∈ relationProducts (p :: P) r := by

  cases r with

  | zero =>
      simpa [relationProducts] using hR

  | succ r =>
      rw [pascal_relation_split]

      exact
        List.mem_append.mpr
          (Or.inr hR)


-- The second Pascal branch extends an old relationship by p.

theorem extended_relation_mem_next
    (P : List Nat)
    (p r R : Nat)
    (hR : R ∈ relationProducts P r) :
    extendRelation R p
      ∈
    relationProducts (p :: P) (Nat.succ r) := by

  rw [pascal_relation_split]

  apply List.mem_append.mpr
  left

  exact
    List.mem_map.mpr
      ⟨R, hR, rfl⟩


/-!
=====================================================================
3. Completed period
=====================================================================

The completed period of a level is the product of its opened clocks.

Adding the new clock p changes the completed period from M to M*p.
-/


def completedPeriod : List Nat → Nat
  | [] =>
      1
  | p :: P =>
      completedPeriod P * p


def nextPeriod
    (M p : Nat) : Nat :=
  M * p


theorem completedPeriod_next
    (P : List Nat)
    (p : Nat) :
    completedPeriod (p :: P)
      =
    nextPeriod (completedPeriod P) p := by

  rfl


-- A prime clock q which does not divide p is coprime to p.

theorem primeNat_coprime_of_not_dvd
    (q p : Nat)
    (hq : PrimeNat q)
    (hnot : ¬ q ∣ p) :
    Nat.Coprime q p := by

  unfold Nat.Coprime

  have hgdivq :
      q.gcd p ∣ q :=
    Nat.gcd_dvd_left q p

  rcases hq.2 (q.gcd p) hgdivq with hg1 | hgq

  · exact hg1

  · exfalso

    apply hnot

    have hgdivp :
        q.gcd p ∣ p :=
      Nat.gcd_dvd_right q p

    rw [hgq] at hgdivp

    exact hgdivp


-- If every member of P is coprime to p, their completed product is coprime
-- to p as well.

theorem completedPeriod_coprime_of_members
    (P : List Nat)
    (p : Nat)
    (hcop :
      ∀ q,
        q ∈ P →
        Nat.Coprime q p) :
    Nat.Coprime (completedPeriod P) p := by

  revert hcop

  induction P with

  | nil =>
      intro hcop

      exact Nat.coprime_one_left p

  | cons q P ih =>
      intro hcop

      have hqcop :
          Nat.Coprime q p :=
        hcop q (by simp)

      have htail :
          ∀ r,
            r ∈ P →
            Nat.Coprime r p := by

        intro r hr

        exact
          hcop r (by simp [hr])

      have hPcop :
          Nat.Coprime (completedPeriod P) p :=
        ih htail

      simpa [completedPeriod] using
        Nat.Coprime.mul_left hPcop hqcop


-- The sieve therefore supplies exactly the coprimality hypothesis required
-- by the CRT/lift construction.

theorem opened_clock_coprime_completedPeriod
    (P : List Nat)
    (p : Nat)
    (hstate : SieveState P p)
    (hopen : OpensClock P p) :
    Nat.Coprime (completedPeriod P) p := by

  apply
    completedPeriod_coprime_of_members
      P p

  intro q hqmem

  exact
    primeNat_coprime_of_not_dvd
      q p
      (hstate.clocks_are_prime q hqmem)
      (open_clock_not_divisible
        P p q hopen hqmem)


-- This is the direct interface between the sieve and the rest of the proof.
-- The opened value p is prime, is new, enters Pascal at degree one, every
-- clock in the enlarged list is prime, and p is coprime to the old period.

theorem sieve_to_pascal_period
    (P : List Nat)
    (p : Nat)
    (hstate : SieveState P p)
    (hopen : OpensClock P p) :
    PrimeNat p
      ∧ p ∉ P
      ∧ (∀ q,
          q ∈ (p :: P) →
          PrimeNat q)
      ∧ p ∈ relationProducts (p :: P) 1
      ∧ Nat.Coprime (completedPeriod P) p := by

  have hpprime :
      PrimeNat p :=
    (sieve_open_iff_prime
      P p hstate hopen.1).1 hopen

  have hnew :
      p ∉ P :=
    opened_clock_is_new
      P p hstate

  have hallprime :
      ∀ q,
        q ∈ (p :: P) →
        PrimeNat q := by

    intro q hq

    simp at hq

    rcases hq with hEq | hOld

    · subst q
      exact hpprime

    · exact
        hstate.clocks_are_prime
          q hOld

  exact
    ⟨
      hpprime,
      hnew,
      hallprime,
      new_clock_is_degree_one_relation P p,
      opened_clock_coprime_completedPeriod
        P p hstate hopen
    ⟩


-- Every Pascal-generated relationship is contained in the completed period.

theorem relation_divides_completedPeriod
    (P : List Nat)
    (r R : Nat)
    (hR : R ∈ relationProducts P r) :
    R ∣ completedPeriod P := by

  induction P generalizing r R with

  | nil =>
      cases r with

      | zero =>
          simp [relationProducts] at hR
          subst R
          exact ⟨1, rfl⟩

      | succ r =>
          simp [relationProducts] at hR

  | cons p P ih =>
      cases r with

      | zero =>
          simp [relationProducts] at hR
          subst R
          exact ⟨completedPeriod (p :: P), by simp⟩

      | succ r =>
          rw [pascal_relation_split] at hR

          have hsplit :
              R ∈ (relationProducts P r).map
                    (fun S => extendRelation S p)
                ∨
              R ∈ relationProducts P (Nat.succ r) :=
            List.mem_append.mp hR

          rcases hsplit with hnew | hold

          · rcases List.mem_map.mp hnew with
              ⟨S, hS, hEq⟩

            subst R

            have hdiv :
                S ∣ completedPeriod P :=
              ih r S hS

            rcases hdiv with ⟨d, hd⟩

            refine ⟨d, ?_⟩

            simp [
              completedPeriod,
              extendRelation,
              hd,
              Nat.mul_left_comm,
              Nat.mul_comm
            ]

          · have hdiv :
                R ∣ completedPeriod P :=
              ih (Nat.succ r) R hold

            rcases hdiv with ⟨d, hd⟩

            refine ⟨d * p, ?_⟩

            simp [
              completedPeriod,
              hd,
              Nat.mul_assoc
            ]


-- Both Pascal branches are therefore contained in the next period.

theorem pascal_relations_divide_next_period
    (P : List Nat)
    (p r R : Nat)
    (hR : R ∈ relationProducts P r) :
    R ∣ completedPeriod (p :: P)
      ∧
    extendRelation R p
      ∣ completedPeriod (p :: P) := by

  constructor

  · exact
      relation_divides_completedPeriod
        (p :: P)
        r
        R
        (old_relation_mem_next P p r R hR)

  · exact
      relation_divides_completedPeriod
        (p :: P)
        (Nat.succ r)
        (extendRelation R p)
        (extended_relation_mem_next P p r R hR)


/-!
=====================================================================
4. Carrying a completed state
=====================================================================

A completed state c modulo M is carried forward by whole copies of M.
Every relationship dividing M keeps exactly the same residue.
-/


def lift
    (c M k : Nat) : Nat :=
  c + k * M


theorem completed_relation_is_immutable
    (c M q k : Nat)
    (hq : q ∣ M) :
    lift c M k % q = c % q := by

  have hzero :
      M % q = 0 :=
    Nat.mod_eq_zero_of_dvd hq

  simp [
    lift,
    Nat.add_mod,
    Nat.mul_mod,
    hzero
  ]


/-!
=====================================================================
5. Twin-prime boundaries
=====================================================================
-/


def AtPlusOne
    (c q : Nat) : Prop :=
  c % q = 1


def AtMinusOne
    (c q : Nat) : Prop :=
  c % q = q - 1


def OnBoundary
    (c q : Nat) : Prop :=
  AtPlusOne c q ∨ AtMinusOne c q


def SafeAt
    (c q : Nat) : Prop :=
  ¬ OnBoundary c q


-- Boundary readings are exactly divisibility of the reflected neighbors.

theorem plus_boundary_gives_divisor
    (c q : Nat)
    (h : AtPlusOne c q) :
    q ∣ c - 1 := by

  unfold AtPlusOne at h

  have hdiv :=
    Nat.mod_add_div c q

  rw [h] at hdiv

  refine ⟨c / q, ?_⟩

  omega


theorem minus_boundary_gives_divisor
    (c q : Nat)
    (hq : 0 < q)
    (h : AtMinusOne c q) :
    q ∣ c + 1 := by

  unfold AtMinusOne at h

  have hdiv :=
    Nat.mod_add_div c q

  rw [h] at hdiv

  refine ⟨c / q + 1, ?_⟩

  rw [
    Nat.mul_add,
    Nat.mul_one
  ]

  omega
-- --------------------------------------------------
-- Conversely, a divisor of a reflected neighbor
-- appears as the corresponding clock boundary.
--
-- Together with the preceding two theorems, this makes
-- reflected divisibility and the ±1 clock states equivalent.
-- --------------------------------------------------

theorem divisor_gives_plus_boundary
    (c q : Nat)
    (hq : 1 < q)
    (hc : 0 < c)
    (hdiv : q ∣ c - 1) :
    AtPlusOne c q := by

  rcases hdiv with ⟨d, hd⟩

  have hcEq :
      c = q * d + 1 := by
    omega

  unfold AtPlusOne

  rw [hcEq]

  simp [
    Nat.add_mod,
    Nat.mod_eq_of_lt hq
  ]


theorem divisor_gives_minus_boundary
    (c q : Nat)
    (hq : 1 < q)
    (hdiv : q ∣ c + 1) :
    AtMinusOne c q := by

  rcases hdiv with ⟨d, hd⟩

  cases d with

  | zero =>
      simp at hd

  | succ d =>

      have hcEq :
          c = q * d + (q - 1) := by

        simp [Nat.mul_succ] at hd
        omega

      have hlt :
          q - 1 < q := by
        omega

      unfold AtMinusOne

      rw [hcEq]

      simp [
        Nat.add_mod,
        Nat.mod_eq_of_lt hlt
      ]


-- If an opened prime q divides either reflected neighbor,
-- then the center is closed at that q-clock.

theorem old_factor_closes_either_boundary
    (c q : Nat)
    (hq : 1 < q)
    (hc : 0 < c)
    (hdiv :
      q ∣ c - 1
        ∨
      q ∣ c + 1) :
    ¬ SafeAt c q := by

  intro hsafe

  apply hsafe

  rcases hdiv with hleft | hright

  · left

    exact
      divisor_gives_plus_boundary
        c q hq hc hleft

  · right

    exact
      divisor_gives_minus_boundary
        c q hq hright

-- Same-boundary relationships extend by the same multiplication R -> R*p
-- used in the Pascal construction.

theorem plus_relation_extends
    (c R p : Nat)
    (hcop : Nat.Coprime R p)
    (hR : R ∣ c - 1)
    (hp : AtPlusOne c p) :
    extendRelation R p ∣ c - 1 := by

  unfold extendRelation

  have hpdiv :
      p ∣ c - 1 :=
    plus_boundary_gives_divisor
      c p hp

  exact
    hcop.mul_dvd_of_dvd_of_dvd
      hR hpdiv


theorem minus_relation_extends
    (c R p : Nat)
    (hp0 : 0 < p)
    (hcop : Nat.Coprime R p)
    (hR : R ∣ c + 1)
    (hp : AtMinusOne c p) :
    extendRelation R p ∣ c + 1 := by

  unfold extendRelation

  have hpdiv :
      p ∣ c + 1 :=
    minus_boundary_gives_divisor
      c p hp0 hp

  exact
    hcop.mul_dvd_of_dvd_of_dvd
      hR hpdiv


/-!
=====================================================================
6. The locked 2-and-3 block
=====================================================================

The construction begins with 2 and 3 completed together as the block 6.
Every later completed period contains that block, so carrying by the period
cannot change its state.
-/


def LockedBlock
    (c B : Nat) : Prop :=
  c % B = 0


def baseBlock : Nat :=
  2 * 3


def baseClocks : List Nat :=
  [2, 3]


theorem two_is_prime_clock :
    PrimeNat 2 := by

  constructor

  · omega

  · intro d hd

    have hdpos :
        0 < d :=
      Nat.pos_of_dvd_of_pos hd (by omega)

    have hdle :
        d ≤ 2 :=
      Nat.le_of_dvd (by omega) hd

    omega


theorem three_is_prime_clock :
    PrimeNat 3 := by

  constructor

  · omega

  · intro d hd

    have hdpos :
        0 < d :=
      Nat.pos_of_dvd_of_pos hd (by omega)

    have hdle :
        d ≤ 3 :=
      Nat.le_of_dvd (by omega) hd

    by_cases h1 : d = 1

    · exact Or.inl h1

    by_cases h3 : d = 3

    · exact Or.inr h3

    have h2 :
        d = 2 := by
      omega

    subst d

    have hzero :
        3 % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd hd

    simp at hzero


-- The first non-base candidate is 5.  The clocks 2 and 3 are exactly the
-- prime sieve state below 5, and 5 survives both of them.

theorem base_sieve_state_five :
    SieveState baseClocks 5 := by

  refine ⟨?_, ?_, ?_⟩

  · intro q hq

    simp [baseClocks] at hq

    rcases hq with h2 | h3

    · subst q
      exact two_is_prime_clock

    · subst q
      exact three_is_prime_clock

  · intro q hq

    simp [baseClocks] at hq

    rcases hq with h2 | h3

    · subst q
      omega

    · subst q
      omega

  · intro n hn hlt

    by_cases h2 : n = 2

    · subst n

      exact
        ⟨
          2,
          by simp [baseClocks],
          Nat.dvd_refl 2
        ⟩

    by_cases h3 : n = 3

    · subst n

      exact
        ⟨
          3,
          by simp [baseClocks],
          Nat.dvd_refl 3
        ⟩

    have h4 :
        n = 4 := by
      omega

    subst n

    exact
      ⟨
        2,
        by simp [baseClocks],
        ⟨2, rfl⟩
      ⟩


theorem five_opens_from_base :
    OpensClock baseClocks 5 := by

  constructor

  · omega

  · intro q hq

    simp [baseClocks] at hq

    rcases hq with h2 | h3

    · subst q
      decide

    · subst q
      decide


def Locked23
    (c : Nat) : Prop :=
  LockedBlock c baseBlock


theorem base_completed_period :
    completedPeriod baseClocks = baseBlock := by

  simp [
    baseClocks,
    completedPeriod,
    baseBlock,
    Nat.mul_comm
  ]


theorem base_six_is_locked :
    Locked23 6 := by

  simp [
    Locked23,
    LockedBlock,
    baseBlock
  ]

-- A reflected boundary is acceptable at q either because the q-clock
-- is not on ±1, or because that reflected neighbor is q itself.

def BoundaryAllowed
    (c q : Nat) : Prop :=
  SafeAt c q
    ∨ c - 1 = q
    ∨ c + 1 = q


-- This is the exact center condition used by level(p, start):
--
--   * remain on the locked 6-lattice;
--   * every opened clock passes its reflected-boundary test;
--   * neither reflected neighbor is one of the clock-generated
--     crosswise products from the saved phase positions.

def TwinCenterAt
    (P : List Nat)
    (p c : Nat) : Prop :=
  Locked23 c
    ∧
  (∀ q,
    q ∈ (p :: P) →
    BoundaryAllowed c q)
    ∧
  ¬ CrossPosition P p (c - 1)
    ∧
  ¬ CrossPosition P p (c + 1)

theorem locked_block_is_carried
    (c M B k : Nat)
    (hB : B ∣ M)
    (hlock : LockedBlock c B) :
    LockedBlock (lift c M k) B := by

  unfold LockedBlock at hlock ⊢

  rw [
    completed_relation_is_immutable
      c M B k hB
  ]

  exact hlock


theorem locked_block_never_becomes_boundary
    (c B : Nat)
    (hB : 2 < B)
    (hlock : LockedBlock c B) :
    ¬ OnBoundary c B := by

  unfold LockedBlock at hlock
  unfold OnBoundary AtPlusOne AtMinusOne

  intro h
  rcases h with hplus | hminus

  · omega
  · omega


theorem locked23_is_carried_forever
    (c M k : Nat)
    (h6 : baseBlock ∣ M)
    (hlock : Locked23 c) :
    Locked23 (lift c M k) := by

  exact
    locked_block_is_carried
      c M baseBlock k h6 hlock


theorem locked23_never_becomes_boundary
    (c M k : Nat)
    (h6 : baseBlock ∣ M)
    (hlock : Locked23 c) :
    ¬ OnBoundary (lift c M k) baseBlock := by

  have hcarried :
      Locked23 (lift c M k) :=
    locked23_is_carried_forever
      c M k h6 hlock

  have hgt :
      2 < baseBlock := by
    simp [baseBlock]

  exact
    locked_block_never_becomes_boundary
      (lift c M k)
      baseBlock
      hgt
      hcarried


-- The base block remains contained in every recursive period enlargement.

theorem baseBlock_divides_next
    (M p : Nat)
    (h6 : baseBlock ∣ M) :
    baseBlock ∣ nextPeriod M p := by

  rcases h6 with ⟨d, hd⟩

  refine ⟨d * p, ?_⟩

  simp [
    nextPeriod,
    hd,
    Nat.mul_assoc
  ]


/-!
=====================================================================
7. The new coprime clock
=====================================================================

If M and p are coprime, the first p lifts occupy distinct residues modulo p.
Since only +1 and -1 are boundary residues, p > 2 guarantees a safe lift.
-/


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


theorem new_cycle_has_survivor
    (c M p : Nat)
    (hp : 2 < p)
    (hcop : Nat.Coprime M p) :
    ∃ k,
      k < p ∧
      SafeAt (lift c M k) p := by

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

  unfold SafeAt

  by_cases h0 :
      OnBoundary (lift c M 0) p

  · by_cases h1 :
        OnBoundary (lift c M 1) p

    · by_cases h2 :
          OnBoundary (lift c M 2) p

      · unfold OnBoundary AtPlusOne AtMinusOne at h0 h1 h2

        rcases h0 with h0 | h0 <;>
        rcases h1 with h1 | h1 <;>
        rcases h2 with h2 | h2 <;>
        omega

      · exact ⟨2, by omega, h2⟩

    · exact ⟨1, by omega, h1⟩

  · exact ⟨0, by omega, h0⟩


/-!
=====================================================================
8. Sieve / Pascal / CRT recursive step
=====================================================================

This is the complete structural step used by the construction.

Given the current sieve state P and completed period M = completedPeriod P:

  * the sieve proves that the newly opened p is prime;
  * p is new and enters Pascal as a degree-one relationship;
  * the sieve proves p is coprime to M;
  * every Pascal-generated old relationship divides M and is immutable;
  * the locked 2*3 block remains locked;
  * the new prime clock p has a safe carried state;
  * Pascal keeps every old relationship and creates its extension R*p;
  * both branches divide the next completed period M*p;
  * every clock in the enlarged list remains prime;
  * the number of relationships remains the corresponding Pascal count.

The source of p, the Pascal extension, and the CRT carry are therefore one
continuous recursive construction.
-/


theorem crt_bridge
    (c M p : Nat)
    (hp : 2 < p)
    (hcop : Nat.Coprime M p) :
    ∃ k,
      k < p
      ∧
      (∀ q,
        q ∣ M →
        lift c M k % q = c % q)
      ∧
      SafeAt (lift c M k) p := by

  obtain ⟨k, hk, hnew⟩ :=
    new_cycle_has_survivor
      c M p hp hcop

  refine ⟨k, hk, ?_, hnew⟩

  intro q hq

  exact
    completed_relation_is_immutable
      c M q k hq


theorem pascal_crt_recursive_step
    (P : List Nat)
    (c p : Nat)
    (hstate : SieveState P p)
    (hopen : OpensClock P p)
    (h6 : baseBlock ∣ completedPeriod P)
    (hlock : Locked23 c) :
    ∃ k,
      k < p
      ∧ PrimeNat p
      ∧ p ∉ P
      ∧ (∀ q,
          q ∈ (p :: P) →
          PrimeNat q)
      ∧ p ∈ relationProducts (p :: P) 1
      ∧ Locked23 (lift c (completedPeriod P) k)
      ∧ SafeAt (lift c (completedPeriod P) k) baseBlock
      ∧ SafeAt (lift c (completedPeriod P) k) p
      ∧
        (∀ r R,
          R ∈ relationProducts P r →
          lift c (completedPeriod P) k % R = c % R)
      ∧ completedPeriod (p :: P)
          = nextPeriod (completedPeriod P) p
      ∧ baseBlock ∣ completedPeriod (p :: P)
      ∧
        (∀ r R,
          R ∈ relationProducts P r →
          (R ∈ relationProducts (p :: P) r)
            ∧
          (extendRelation R p
            ∈ relationProducts (p :: P) (Nat.succ r)))
      ∧
        (∀ r R,
          R ∈ relationProducts P r →
          R ∣ completedPeriod (p :: P)
            ∧
          extendRelation R p
            ∣ completedPeriod (p :: P))
      ∧
        (∀ r,
          (relationProducts (p :: P) r).length
            =
          choose (p :: P).length r) := by

  have hsieve :=
    sieve_to_pascal_period
      P p hstate hopen

  have hpprime :
      PrimeNat p :=
    hsieve.1

  have hpnew :
      p ∉ P :=
    hsieve.2.1

  have hallprime :
      ∀ q,
        q ∈ (p :: P) →
        PrimeNat q :=
    hsieve.2.2.1

  have hpPascal :
      p ∈ relationProducts (p :: P) 1 :=
    hsieve.2.2.2.1

  have hcop :
      Nat.Coprime (completedPeriod P) p :=
    hsieve.2.2.2.2

  have hp :
      2 < p :=
    hopen.1

  obtain ⟨k, hk, hold, hnew⟩ :=
    crt_bridge
      c
      (completedPeriod P)
      p
      hp
      hcop

  have hbase :
      Locked23 (lift c (completedPeriod P) k) :=
    locked23_is_carried_forever
      c
      (completedPeriod P)
      k
      h6
      hlock

  have hbaseSafe :
      SafeAt (lift c (completedPeriod P) k) baseBlock := by

    unfold SafeAt

    exact
      locked23_never_becomes_boundary
        c
        (completedPeriod P)
        k
        h6
        hlock

  have h6next :
      baseBlock ∣ completedPeriod (p :: P) := by

    rw [completedPeriod_next]

    exact
      baseBlock_divides_next
        (completedPeriod P) p h6

  refine ⟨
    k,
    hk,
    hpprime,
    hpnew,
    hallprime,
    hpPascal,
    hbase,
    hbaseSafe,
    hnew,
    ?_,
    completedPeriod_next P p,
    h6next,
    ?_,
    ?_,
    ?_
  ⟩

  · intro r R hR

    exact
      hold R
        (relation_divides_completedPeriod
          P r R hR)

  · intro r R hR

    exact
      ⟨
        old_relation_mem_next
          P p r R hR,
        extended_relation_mem_next
          P p r R hR
      ⟩

  · intro r R hR

    exact
      pascal_relations_divide_next_period
        P p r R hR

  · intro r

    cases r with

    | zero =>
        rfl

    | succ r =>
        simpa using
          relation_count_pascal_extension
            P p r


-- The base state is the completed 2*3 period from which the recursion starts.

theorem base_state_is_ready :
    completedPeriod baseClocks = baseBlock
      ∧ Locked23 6
      ∧ SieveState baseClocks 5
      ∧ OpensClock baseClocks 5 := by

  exact
    ⟨
      base_completed_period,
      base_six_is_locked,
      base_sieve_state_five,
      five_opens_from_base
    ⟩
/-!
=====================================================================
9. Clock-phase positions are prime
=====================================================================

The saved phase positions are not obtained by an external primality test.

They are exactly the positions in the finite p*p clock walk at which every
opened clock is nonzero.

If such a position x were composite, write x = d*e with d a proper divisor.
The phase-window bound forces at least one of d or e to be at most p.
That factor is therefore detected either by the p-clock itself or by one
of the earlier opened clocks.

Hence every saved phase position is prime.
-/


theorem phase_position_is_prime
    (P : List Nat)
    (p x : Nat)
    (hstate : SieveState P p)
    (hopen : OpensClock P p)
    (hx : PhasePosition P p x) :
    PrimeNat x := by

  have hp :
      2 < p :=
    hopen.1

  have hxgt :
      p < x :=
    hx.1

  have hxle :
      x ≤ p + p * p := by

    simpa [phaseEnd] using hx.2.1

  have hxopen :
      AllClocksOpen (p :: P) x :=
    hx.2.2

  -- Any nontrivial factor at or below p is already visible
  -- to one of the opened clocks.

  have factor_at_most_p_is_closed :
      ∀ f,
        1 < f →
        f ≤ p →
        f ∣ x →
        False := by

    intro f hfgt hfle hfdiv

    by_cases hfp :
        f = p

    · subst f

      have hzero :
          x % p = 0 :=
        Nat.mod_eq_zero_of_dvd hfdiv

      exact
        (hxopen p (by simp)) hzero

    · have hflt :
          f < p := by
        omega

      obtain ⟨q, hqmem, hqdiv⟩ :=
        hstate.earlier_numbers_are_covered
          f hfgt hflt

      have hqdx :
          q ∣ x :=
        Nat.dvd_trans hqdiv hfdiv

      have hzero :
          x % q = 0 :=
        Nat.mod_eq_zero_of_dvd hqdx

      exact
        (hxopen q (by simp [hqmem])) hzero

  constructor

  · omega

  · intro d hd

    by_cases hd1 :
        d = 1

    · exact Or.inl hd1

    by_cases hdx :
        d = x

    · exact Or.inr hdx

    exfalso

    have hxpos :
        0 < x := by
      omega

    have hdpos :
        0 < d :=
      Nat.pos_of_dvd_of_pos hd hxpos

    have hdgt1 :
        1 < d := by
      omega

    rcases hd with ⟨e, he⟩

    have he0 :
        e ≠ 0 := by

      intro hezero
      subst e
      simp at he
      omega

    have he1 :
        e ≠ 1 := by

      intro heone
      subst e
      simp at he

      exact
        hdx he.symm

    have hegt1 :
        1 < e := by
      omega

    have hedvd :
        e ∣ x := by

      refine ⟨d, ?_⟩

      calc
        x = d * e := he
        _ = e * d := Nat.mul_comm d e

    -- If both factors were greater than p, their product would already
    -- exceed the entire p*p phase window.

    have hsmall :
        d ≤ p ∨ e ≤ p := by

      by_cases hdp :
          d ≤ p

      · exact Or.inl hdp

      by_cases hep :
          e ≤ p

      · exact Or.inr hep

      · have hdge :
            p + 1 ≤ d := by
          omega

        have hege :
            p + 1 ≤ e := by
          omega

        have hmul :
            (p + 1) * (p + 1) ≤ d * e :=
          Nat.mul_le_mul hdge hege

        have hmulx :
            (p + 1) * (p + 1) ≤ x := by

          rw [he]

          exact hmul

        have hgap :
            p + p * p <
              (p + 1) * (p + 1) := by

          calc
            p + p * p
                = p * (p + 1) := by
                    simp [
                      Nat.mul_add,
                      Nat.add_comm
                    ]

            _ < (p + 1) * (p + 1) :=
              Nat.mul_lt_mul_of_pos_right
                (by omega)
                (by omega)

        omega

    rcases hsmall with hdsmall | hesmall

    · have hddvd :
          d ∣ x :=
        ⟨e, he⟩

      exact
        factor_at_most_p_is_closed
          d hdgt1 hdsmall hddvd

    · exact
        factor_at_most_p_is_closed
          e hegt1 hesmall hedvd
/-!
=====================================================================
10. Degree-two certification domain
=====================================================================

The phase window

    p < x <= p + p*p

certifies degree-one positions.

The cross-position construction certifies the next degree.

If n is composite, every opened clock is nonzero at n, and

    n < (p+1) * phaseEnd p,

then every nontrivial factor of n is greater than p.

Writing n = d*e, both d and e must also lie inside phaseEnd p.
Hence both are saved PhasePositions and n is a CrossPosition.

Thus, below this bound, a composite number cannot survive both
the opened clocks and the degree-two cross-position test.
-/


def certificationEnd
    (p : Nat) : Nat :=
  (p + 1) * phaseEnd p


theorem surviving_composite_is_cross_position
    (P : List Nat)
    (p n : Nat)
    (hstate : SieveState P p)
    (_hopen : OpensClock P p)
    (hn1 : 1 < n)
    (hbound : n < certificationEnd p)
    (hnopen : AllClocksOpen (p :: P) n)
    (hcomp : ¬ PrimeNat n) :
    CrossPosition P p n := by

  -- Since n > 1 but is not prime, it has a proper
  -- nontrivial divisor.

  have hproper :
      ∃ d,
        d ∣ n
          ∧ d ≠ 1
          ∧ d ≠ n := by

    apply Classical.byContradiction
    intro hnone

    apply hcomp

    constructor

    · exact hn1

    · intro d hd

      by_cases hd1 :
          d = 1

      · exact Or.inl hd1

      · by_cases hdn :
            d = n

        · exact Or.inr hdn

        · exfalso

          apply hnone

          exact
            ⟨d, hd, hd1, hdn⟩


  obtain ⟨d, hddvd, hd1, hdn⟩ :=
    hproper

  rcases hddvd with ⟨e, he⟩


  have hnpos :
      0 < n := by
    omega


  have hdpos :
      0 < d :=
    Nat.pos_of_dvd_of_pos
      ⟨e, he⟩
      hnpos


  have hdgt1 :
      1 < d := by
    omega


  have he0 :
      e ≠ 0 := by

    intro hzero
    subst e

    simp at he
    omega


  have he1 :
      e ≠ 1 := by

    intro hone
    subst e

    simp at he

    exact
      hdn he.symm


  have hegt1 :
      1 < e := by
    omega


  have hedvd :
      e ∣ n := by

    refine ⟨d, ?_⟩

    calc
      n = d * e := he
      _ = e * d := Nat.mul_comm d e


  -- Every nontrivial factor of this surviving number
  -- must lie above the newest opened clock p.
  --
  -- If it were at or below p, an opened clock would
  -- divide n, contradicting AllClocksOpen.

  have factor_above_p :
      ∀ f,
        1 < f →
        f ∣ n →
        p < f := by

    intro f hfgt hfdiv

    by_cases hfle :
        f ≤ p

    · by_cases hEq :
          f = p

      · subst f

        have hzero :
            n % p = 0 :=
          Nat.mod_eq_zero_of_dvd hfdiv

        exfalso

        exact
          (hnopen p (by simp)) hzero

      · have hflt :
            f < p := by
          omega

        obtain ⟨q, hqmem, hqdiv⟩ :=
          hstate.earlier_numbers_are_covered
            f hfgt hflt

        have hqdn :
            q ∣ n :=
          Nat.dvd_trans
            hqdiv hfdiv

        have hzero :
            n % q = 0 :=
          Nat.mod_eq_zero_of_dvd hqdn

        exfalso

        exact
          (hnopen q (by simp [hqmem])) hzero

    · omega


  have hdgtp :
      p < d :=
    factor_above_p
      d hdgt1 ⟨e, he⟩


  have hegtp :
      p < e :=
    factor_above_p
      e hegt1 hedvd


  -- The certification bound now forces each factor
  -- back inside the saved phase window.
  --
  -- If d extended past phaseEnd p, then because
  -- e >= p+1, their product would already reach the
  -- certification boundary.

  have hdle :
      d ≤ phaseEnd p := by

    by_cases hgood :
        d ≤ phaseEnd p

    · exact hgood

    · have hEndLe :
          phaseEnd p ≤ d := by
        omega

      have hp1e :
          p + 1 ≤ e := by
        omega

      have hmul :
          (p + 1) * phaseEnd p
            ≤ e * d :=
        Nat.mul_le_mul
          hp1e hEndLe

      have hmuln :
          (p + 1) * phaseEnd p
            ≤ n := by

        rw [he]

        simpa [Nat.mul_comm] using hmul

      exfalso

      unfold certificationEnd at hbound
      omega


  have hele :
      e ≤ phaseEnd p := by

    by_cases hgood :
        e ≤ phaseEnd p

    · exact hgood

    · have hEndLe :
          phaseEnd p ≤ e := by
        omega

      have hp1d :
          p + 1 ≤ d := by
        omega

      have hmul :
          (p + 1) * phaseEnd p
            ≤ d * e :=
        Nat.mul_le_mul
          hp1d hEndLe

      have hmuln :
          (p + 1) * phaseEnd p
            ≤ n := by

        rw [he]

        exact hmul

      exfalso

      unfold certificationEnd at hbound
      omega


  -- A divisor of an all-open number is itself all-open:
  -- otherwise the same opened clock would also divide n.

  have hdopen :
      AllClocksOpen (p :: P) d := by

    intro q hq hzero

    have hqd :
        q ∣ d :=
      Nat.dvd_of_mod_eq_zero hzero

    have hqn :
        q ∣ n :=
      Nat.dvd_trans
        hqd
        ⟨e, he⟩

    have hnzero :
        n % q = 0 :=
      Nat.mod_eq_zero_of_dvd hqn

    exact
      (hnopen q hq) hnzero


  have heopen :
      AllClocksOpen (p :: P) e := by

    intro q hq hzero

    have hqe :
        q ∣ e :=
      Nat.dvd_of_mod_eq_zero hzero

    have hqn :
        q ∣ n :=
      Nat.dvd_trans
        hqe
        hedvd

    have hnzero :
        n % q = 0 :=
      Nat.mod_eq_zero_of_dvd hqn

    exact
      (hnopen q hq) hnzero


  -- Therefore both factors are exactly saved
  -- clock-phase positions.

  have hdphase :
      PhasePosition P p d :=
    ⟨hdgtp, hdle, hdopen⟩


  have hephase :
      PhasePosition P p e :=
    ⟨hegtp, hele, heopen⟩


  -- Hence n is one of the crosswise products.

  exact
    ⟨
      d,
      e,
      hdphase,
      hephase,
      he
    ⟩

/-!
=====================================================================
11. The twin-center state and its recursive transport
=====================================================================

The construction now has three formally distinct pieces.

1. The completed 2,3 state fixes the six-spaced center lattice.

2. The opened prime clocks determine whether either reflected neighbor
   is closed by an already known prime factor.

3. The finite phase/cross construction detects every remaining composite
   reflected neighbor inside the certified degree-two domain.

The first center is 6.

The clock-interior part of that state is recursively transported when
a new coprime prime clock is opened.  Completed old clock states remain
immutable, while the new clock contributes a safe interior state.

A certified TwinCenterAt is therefore an actual twin-prime center:
both reflected neighbors are prime.
-/


-- --------------------------------------------------
-- Every opened clock itself divides the completed period.
-- --------------------------------------------------

theorem member_divides_completedPeriod
    (P : List Nat)
    (q : Nat)
    (hq : q ∈ P) :
    q ∣ completedPeriod P := by

  induction P with

  | nil =>
      simp at hq

  | cons a P ih =>

      simp at hq

      rcases hq with hEq | hTail

      · subst q

        exact
          Nat.dvd_mul_left
            a
            (completedPeriod P)

      · have hdiv :
            q ∣ completedPeriod P :=
          ih hTail

        rcases hdiv with ⟨d, hd⟩

        refine ⟨d * a, ?_⟩

        simp [
          completedPeriod,
          hd,
          Nat.mul_assoc
        ]


-- --------------------------------------------------
-- Safe boundary state is immutable for any clock
-- already contained in the completed period.
-- --------------------------------------------------

theorem safeAt_is_immutable
    (c M q k : Nat)
    (hq : q ∣ M) :
    SafeAt (lift c M k) q
      ↔
    SafeAt c q := by

  unfold SafeAt
  unfold OnBoundary
  unfold AtPlusOne
  unfold AtMinusOne

  rw [
    completed_relation_is_immutable
      c M q k hq
  ]


-- --------------------------------------------------
-- The clock-interior state carried by the recursion.
-- --------------------------------------------------

def InteriorClockState
    (P : List Nat)
    (c : Nat) : Prop :=
  Locked23 c
    ∧
  ∀ q,
    q ∈ P →
    SafeAt c q


-- The original center 6 already has the complete
-- interior state of the locked 2,3 system.

theorem six_is_initial_interior_clock_state :
    InteriorClockState baseClocks 6 := by

  unfold InteriorClockState

  constructor

  · exact
      base_six_is_locked

  · intro q hq

    simp [baseClocks] at hq

    rcases hq with h2 | h3

    · subst q

      simp [
        SafeAt,
        OnBoundary,
        AtPlusOne,
        AtMinusOne
      ]

    · subst q

      simp [
        SafeAt,
        OnBoundary,
        AtPlusOne,
        AtMinusOne
      ]


-- --------------------------------------------------
-- Recursive transport of the complete interior clock state.
--
-- Every old clock divides the completed period, so its
-- residue and therefore its SafeAt state are immutable.
--
-- Coprimality with the newly opened p-clock supplies a
-- new safe state for p.
--
-- Thus P -> p :: P carries the interior state inductively.
-- --------------------------------------------------

theorem interior_clock_state_recursive_step
    (P : List Nat)
    (c p : Nat)
    (hstate : SieveState P p)
    (hopen : OpensClock P p)
    (h6 : baseBlock ∣ completedPeriod P)
    (hinterior : InteriorClockState P c) :
    ∃ k,
      k < p
        ∧
      InteriorClockState
        (p :: P)
        (lift c (completedPeriod P) k) := by

  have hp :
      2 < p :=
    hopen.1

  have hcop :
      Nat.Coprime (completedPeriod P) p :=
    opened_clock_coprime_completedPeriod
      P p hstate hopen

  obtain ⟨k, hk, hold, hnew⟩ :=
    crt_bridge
      c
      (completedPeriod P)
      p
      hp
      hcop

  refine ⟨k, hk, ?_⟩

  unfold InteriorClockState

  constructor

  · exact
      locked23_is_carried_forever
        c
        (completedPeriod P)
        k
        h6
        hinterior.1

  · intro q hq

    simp at hq

    rcases hq with hEq | hOld

    · subst q

      exact hnew

    · have hqdiv :
          q ∣ completedPeriod P :=
        member_divides_completedPeriod
          P q hOld

      exact
        (safeAt_is_immutable
          c
          (completedPeriod P)
          q
          k
          hqdiv).2
            (hinterior.2 q hOld)


-- --------------------------------------------------
-- The first actual TwinCenterAt is 6 at the first
-- non-base prime level p = 5.
-- --------------------------------------------------

theorem six_is_initial_twin_center :
    TwinCenterAt baseClocks 5 6 := by

  unfold TwinCenterAt

  refine ⟨
    base_six_is_locked,
    ?_,
    ?_,
    ?_
  ⟩

  -- Every opened clock passes the boundary rule.

  · intro q hq

    simp [baseClocks] at hq

    rcases hq with h5 | h2 | h3

    · subst q

      simp [
        BoundaryAllowed,
        SafeAt,
        OnBoundary,
        AtPlusOne,
        AtMinusOne
      ]

    · subst q

      simp [
        BoundaryAllowed,
        SafeAt,
        OnBoundary,
        AtPlusOne,
        AtMinusOne
      ]

    · subst q

      simp [
        BoundaryAllowed,
        SafeAt,
        OnBoundary,
        AtPlusOne,
        AtMinusOne
      ]


  -- 5 cannot be a cross-position because each phase
  -- factor is strictly greater than 5.

  · intro hcross

    unfold CrossPosition at hcross

    rcases hcross with
      ⟨a, b, ha, hb, hab⟩

    have ha5 :
        5 < a :=
      ha.1

    have hb5 :
        5 < b :=
      hb.1

    have ha6 :
        6 ≤ a := by
      omega

    have hb6 :
        6 ≤ b := by
      omega

    have hmul :
        6 * 6 ≤ a * b :=
      Nat.mul_le_mul
        ha6 hb6

    simp at hmul

    omega


  -- 7 cannot be a cross-position for the same reason.

  · intro hcross

    unfold CrossPosition at hcross

    rcases hcross with
      ⟨a, b, ha, hb, hab⟩

    have ha5 :
        5 < a :=
      ha.1

    have hb5 :
        5 < b :=
      hb.1

    have ha6 :
        6 ≤ a := by
      omega

    have hb6 :
        6 ≤ b := by
      omega

    have hmul :
        6 * 6 ≤ a * b :=
      Nat.mul_le_mul
        ha6 hb6

    simp at hmul

    omega


-- --------------------------------------------------
-- A certified twin center is a TwinCenterAt lying
-- inside the degree-two certification domain.
-- --------------------------------------------------

def CertifiedTwinCenterAt
    (P : List Nat)
    (p c : Nat) : Prop :=
  2 < c
    ∧
  TwinCenterAt P p c
    ∧
  c + 1 < certificationEnd p


theorem six_is_initial_certified_twin_center :
    CertifiedTwinCenterAt
      baseClocks 5 6 := by

  unfold CertifiedTwinCenterAt

  refine ⟨
    by omega,
    six_is_initial_twin_center,
    ?_
  ⟩

  simp [
    certificationEnd,
    phaseEnd
  ]


-- --------------------------------------------------
-- Certification theorem:
--
-- Inside certificationEnd p, TwinCenterAt means that
-- both reflected neighbors are actually prime.
--
-- If a neighbor were composite:
--
--   * any factor belonging to an opened clock would put
--     the center on that clock's reflected boundary;
--
--   * otherwise the composite survives every opened clock,
--     so degree-two completeness makes it a CrossPosition.
--
-- TwinCenterAt excludes both cases.
-- --------------------------------------------------

theorem certified_twin_center_gives_twin_primes
    (P : List Nat)
    (p c : Nat)
    (hstate : SieveState P p)
    (hopen : OpensClock P p)
    (hcert :
      CertifiedTwinCenterAt P p c) :
    PrimeNat (c - 1)
      ∧
    PrimeNat (c + 1) := by

  rcases hcert with
    ⟨hc2, htwin, hcertBound⟩

  have hallprime :
      ∀ q,
        q ∈ (p :: P) →
        PrimeNat q :=
    (sieve_to_pascal_period
      P p hstate hopen).2.2.1


  -- Since a certified center is locked to the six-lattice
  -- and is positive, it is at least 6.

  have hmod6 :
      c % baseBlock = 0 := by

    simpa [
      Locked23,
      LockedBlock
    ] using htwin.1

  have hdiv6 :
      baseBlock ∣ c :=
    Nat.dvd_of_mod_eq_zero hmod6

  have hbasele :
      baseBlock ≤ c :=
    Nat.le_of_dvd
      (by omega)
      hdiv6

  have hc6 :
      6 ≤ c := by

    simpa [baseBlock] using hbasele


  constructor


  -- ==================================================
  -- Left reflected neighbor c - 1
  -- ==================================================

  · apply Classical.byContradiction
    intro hcompLeft

    have hleftOpen :
        AllClocksOpen
          (p :: P)
          (c - 1) := by

      unfold AllClocksOpen

      intro q hq hzero

      have hqprime :
          PrimeNat q :=
        hallprime q hq

      have hqgt1 :
          1 < q :=
        hqprime.1

      have hdiv :
          q ∣ c - 1 :=
        Nat.dvd_of_mod_eq_zero
          hzero

      have hplus :
          AtPlusOne c q :=
        divisor_gives_plus_boundary
          c q
          hqgt1
          (by omega)
          hdiv

      have hallowed :
          BoundaryAllowed c q :=
        htwin.2.1 q hq

      unfold BoundaryAllowed at hallowed

      rcases hallowed with
        hsafe | hEqLeft | hEqRight

      · apply hsafe

        exact
          Or.inl hplus

      · apply hcompLeft

        rw [hEqLeft]

        exact hqprime

      · have hle :
            q ≤ c - 1 :=
          Nat.le_of_dvd
            (by omega)
            hdiv

        omega


    have hleftBound :
        c - 1 < certificationEnd p := by
      omega

    have hleftGt1 :
        1 < c - 1 := by
      omega

    have hcross :
        CrossPosition
          P p (c - 1) :=
      surviving_composite_is_cross_position
        P
        p
        (c - 1)
        hstate
        hopen
        hleftGt1
        hleftBound
        hleftOpen
        hcompLeft

    exact
      htwin.2.2.1 hcross


  -- ==================================================
  -- Right reflected neighbor c + 1
  -- ==================================================

  · apply Classical.byContradiction
    intro hcompRight

    have hrightOpen :
        AllClocksOpen
          (p :: P)
          (c + 1) := by

      unfold AllClocksOpen

      intro q hq hzero

      have hqprime :
          PrimeNat q :=
        hallprime q hq

      have hqgt1 :
          1 < q :=
        hqprime.1

      have hdiv :
          q ∣ c + 1 :=
        Nat.dvd_of_mod_eq_zero
          hzero

      have hminus :
          AtMinusOne c q :=
        divisor_gives_minus_boundary
          c q
          hqgt1
          hdiv

      have hallowed :
          BoundaryAllowed c q :=
        htwin.2.1 q hq

      unfold BoundaryAllowed at hallowed

      rcases hallowed with
        hsafe | hEqLeft | hEqRight

      · apply hsafe

        exact
          Or.inr hminus

      · have hdivLeft :
            q ∣ c - 1 := by

          rw [hEqLeft]

          exact
            Nat.dvd_refl q

        have hplus :
            AtPlusOne c q :=
          divisor_gives_plus_boundary
            c q
            hqgt1
            (by omega)
            hdivLeft

        unfold AtPlusOne at hplus
        unfold AtMinusOne at hminus

        omega

      · apply hcompRight

        rw [hEqRight]

        exact hqprime


    have hrightGt1 :
        1 < c + 1 := by
      omega

    have hcross :
        CrossPosition
          P p (c + 1) :=
      surviving_composite_is_cross_position
        P
        p
        (c + 1)
        hstate
        hopen
        hrightGt1
        hcertBound
        hrightOpen
        hcompRight

    exact
      htwin.2.2.2 hcross
/-!
=====================================================================
12. Binary prime logic as a fixed Pascal band
=====================================================================

The Pascal recursion is the binary logic of the construction.

At every new clock there are exactly two relationship branches:

    0 : retain the old relationship;
    1 : append the new prime, R -> R*p.

The locked 2,3 base supplies the initial two zero choices.

After that base has been completed, every newly opened prime is carried
through the 1-branch.  The resulting logical history therefore has the
form

    0, 0, 1, 1, 1, 1, ...

If a Pascal row has n binary choices, the all-1 exterior edge has
degree n.

A history containing exactly the two initial zero choices and then only
1 choices has degree

    n - 2.

Hence its distance from the all-1 edge is permanently

    n - (n - 2) = 2.

The construction therefore moves indefinitely downward through Pascal's
triangle while remaining in the same band, exactly two positions from
the all-1 edge.

This section makes that geometric/logical correspondence explicit and
then joins it to the recursively transported clock state.
-/


-- --------------------------------------------------
-- Distance from the all-yes exterior Pascal edge.
--
-- Degree P.length is the all-yes edge.
-- --------------------------------------------------

def pascalEdgeDistance
    (P : List Nat)
    (r : Nat) : Nat :=
  P.length - r


-- --------------------------------------------------
-- The twin-prime logical path contains exactly two
-- initial zero choices.
--
-- Therefore, in a row with P.length binary choices,
-- its degree is P.length - 2.
-- --------------------------------------------------

def twinPascalDegree
    (P : List Nat) : Nat :=
  P.length - 2


-- A relationship lies on the fixed logical band when
-- it occurs at exactly that degree.

def TwinPascalBand
    (P : List Nat)
    (R : Nat) : Prop :=
  R ∈ relationProducts
        P
        (twinPascalDegree P)


-- --------------------------------------------------
-- The band is exactly two positions from the
-- all-yes exterior edge.
-- --------------------------------------------------

theorem twin_pascal_band_is_two_from_yes_edge
    (P : List Nat)
    (h2 : 2 ≤ P.length) :
    pascalEdgeDistance
      P
      (twinPascalDegree P)
      = 2 := by

  unfold pascalEdgeDistance
  unfold twinPascalDegree

  omega


-- --------------------------------------------------
-- The locked 2,3 base represents the two initial
-- zero choices.
--
-- With two choices and zero yes-extensions,
--
--     degree = 2 - 2 = 0.
--
-- The degree-zero relation is 1.
-- --------------------------------------------------

theorem locked_base_starts_twin_pascal_band :
    TwinPascalBand
      baseClocks
      1 := by

  simp [
    TwinPascalBand,
    twinPascalDegree,
    baseClocks,
    relationProducts
  ]


-- The base is already exactly two positions from
-- the chosen all-yes edge.

theorem locked_base_is_two_from_yes_edge :
    pascalEdgeDistance
      baseClocks
      (twinPascalDegree baseClocks)
      = 2 := by

  apply
    twin_pascal_band_is_two_from_yes_edge

  simp [baseClocks]


-- --------------------------------------------------
-- Sieve success is the gateway into the Pascal
-- yes-branch.
--
-- The sieve first certifies p as prime.
-- The same p then enters Pascal as the new
-- degree-one relationship.
-- --------------------------------------------------

theorem opened_prime_enters_pascal_yes
    (P : List Nat)
    (p : Nat)
    (hstate : SieveState P p)
    (hopen : OpensClock P p) :
    PrimeNat p
      ∧
    p ∈ relationProducts
          (p :: P)
          1 := by

  have hsieve :=
    sieve_to_pascal_period
      P p hstate hopen

  exact
    ⟨
      hsieve.1,
      hsieve.2.2.2.1
    ⟩


-- --------------------------------------------------
-- Taking another yes-branch increases both
--
--     row depth
--
-- and
--
--     relationship degree
--
-- by exactly one.
--
-- Therefore the distance from the all-yes edge
-- does not change.
-- --------------------------------------------------

theorem twin_pascal_degree_yes_step
    (P : List Nat)
    (p : Nat)
    (h2 : 2 ≤ P.length) :
    twinPascalDegree (p :: P)
      =
    Nat.succ (twinPascalDegree P) := by

  unfold twinPascalDegree

  change
    Nat.succ P.length - 2
      =
    Nat.succ (P.length - 2)

  omega


-- --------------------------------------------------
-- This is the actual Pascal movement:
--
--     R -> R*p
--
-- takes a relationship on the two-from-edge band
-- to another relationship on the same band in the
-- next row.
-- --------------------------------------------------

theorem twin_pascal_yes_step
    (P : List Nat)
    (p R : Nat)
    (h2 : 2 ≤ P.length)
    (hR : TwinPascalBand P R) :
    TwinPascalBand
      (p :: P)
      (extendRelation R p) := by

  unfold TwinPascalBand at hR ⊢

  rw [
    twin_pascal_degree_yes_step
      P p h2
  ]

  exact
    extended_relation_mem_next
      P
      p
      (twinPascalDegree P)
      R
      hR


-- --------------------------------------------------
-- The Pascal coefficient at this band is exactly
-- the coefficient already generated by choose.
--
-- The geometry is therefore not merely pictorial:
-- it is literally one of the indexed Pascal degrees
-- already present in relationProducts.
-- --------------------------------------------------

theorem twin_pascal_band_count
    (P : List Nat) :
    (relationProducts
      P
      (twinPascalDegree P)).length
      =
    choose
      P.length
      (twinPascalDegree P) := by

  exact
    relation_count_is_choose
      P
      (twinPascalDegree P)


-- --------------------------------------------------
-- Concrete first yes-step:
--
--     0,0
--
-- becomes
--
--     0,0,1
--
-- when 5 opens.
--
-- The degree-zero relation 1 becomes
--
--     1*5 = 5.
-- --------------------------------------------------

theorem five_is_first_pascal_yes :
    TwinPascalBand
      (5 :: baseClocks)
      5 := by

  have hbase :
      TwinPascalBand
        baseClocks
        1 :=
    locked_base_starts_twin_pascal_band

  have h2 :
      2 ≤ baseClocks.length := by

    simp [baseClocks]

  have hstep :=
    twin_pascal_yes_step
      baseClocks
      5
      1
      h2
      hbase

  simpa [extendRelation] using hstep


-- --------------------------------------------------
-- The center-state recursion and the Pascal recursion
-- are congruent recursive operations.
--
-- The clock state advances
--
--     P -> p :: P
--
-- through the CRT carry.
--
-- At exactly the same recursive step, the Pascal
-- relationship advances
--
--     R -> R*p.
--
-- If the relationship began in the two-from-edge
-- band, it remains there.
-- --------------------------------------------------

theorem clock_state_and_pascal_band_advance_together
    (P : List Nat)
    (c p R : Nat)
    (h2 : 2 ≤ P.length)
    (hstate : SieveState P p)
    (hopen : OpensClock P p)
    (h6 :
      baseBlock ∣ completedPeriod P)
    (hinterior :
      InteriorClockState P c)
    (hband :
      TwinPascalBand P R) :
    ∃ k,
      k < p
        ∧
      InteriorClockState
        (p :: P)
        (lift c (completedPeriod P) k)
        ∧
      TwinPascalBand
        (p :: P)
        (extendRelation R p)
        ∧
      pascalEdgeDistance
        (p :: P)
        (twinPascalDegree (p :: P))
        = 2 := by

  obtain ⟨k, hk, hnextInterior⟩ :=
    interior_clock_state_recursive_step
      P
      c
      p
      hstate
      hopen
      h6
      hinterior

  have hnextBand :
      TwinPascalBand
        (p :: P)
        (extendRelation R p) :=
    twin_pascal_yes_step
      P
      p
      R
      h2
      hband

  have h2next :
      2 ≤ (p :: P).length := by

    change
      2 ≤ Nat.succ P.length

    omega

  have hdistance :
      pascalEdgeDistance
        (p :: P)
        (twinPascalDegree (p :: P))
        = 2 :=
    twin_pascal_band_is_two_from_yes_edge
      (p :: P)
      h2next

  exact
    ⟨
      k,
      hk,
      hnextInterior,
      hnextBand,
      hdistance
    ⟩


-- --------------------------------------------------
-- The initial center 6 and the initial Pascal state
-- therefore begin together.
-- --------------------------------------------------

theorem six_starts_clock_and_pascal_geometry :
    InteriorClockState
        baseClocks
        6
      ∧
    TwinPascalBand
        baseClocks
        1
      ∧
    pascalEdgeDistance
        baseClocks
        (twinPascalDegree baseClocks)
        = 2 := by

  exact
    ⟨
      six_is_initial_interior_clock_state,
      locked_base_starts_twin_pascal_band,
      locked_base_is_two_from_yes_edge
    ⟩
/-!
=====================================================================
13. Prime logic is the Pascal recursion
=====================================================================

The preceding construction has already established the logical
interpretation of the Pascal recursion.

For a valid sieve state, a candidate p has a binary outcome:

    0 : p does not open;
    1 : p opens.

Opening is equivalent to primality.

When p opens, the same p enters the Pascal construction as the new
degree-one relation.  Every existing relation R then has exactly the
two Pascal branches

    0 : R,
    1 : R*p.

Thus a successful prime opening is exactly the YES branch of the
same binary recursion which generates Pascal's triangle.

The locked 2,3 base supplies the two initial zero choices.  Every
subsequent opened prime supplies one complete YES step.

Hence the distinguished logical path of the construction is

    0, 0, 1, 1, 1, 1, ...

and each later 1 is simultaneously:

    * a sieve-certified prime;
    * a new opened clock;
    * a new degree-one Pascal input;
    * the extension R -> R*p of every inherited relationship;
    * a new completed coprime clock state.

The logical clock recursion and the Pascal recursion are therefore
the same recursive operation viewed in two representations.
-/


-- --------------------------------------------------
-- The locked 2,3 state is the initial 0,0 state.
--
-- Two choices have been made, but no YES-extension
-- has yet been taken.  Hence the Pascal degree is 0.
-- --------------------------------------------------

theorem locked23_is_pascal_zero_zero :
    baseClocks.length = 2
      ∧
    twinPascalDegree baseClocks = 0
      ∧
    TwinPascalBand baseClocks 1 := by

  constructor

  · simp [baseClocks]

  · constructor

    · simp [
        twinPascalDegree,
        baseClocks
      ]

    · exact
        locked_base_starts_twin_pascal_band


-- --------------------------------------------------
-- Prime logic and Pascal YES are the same decision.
--
-- Under a valid sieve state:
--
--     p opens
--
-- iff
--
--     p is prime and therefore enters the new
--     Pascal row as its degree-one input.
-- --------------------------------------------------

theorem prime_logic_yes_iff_pascal_yes
    (P : List Nat)
    (p : Nat)
    (hstate : SieveState P p)
    (hp : 2 < p) :
    OpensClock P p
      ↔
    (PrimeNat p
      ∧
     p ∈ relationProducts (p :: P) 1) := by

  constructor

  · intro hopen

    exact
      ⟨
        sieve_open_is_prime
          P p hstate hopen,
        new_clock_is_degree_one_relation
          P p
      ⟩

  · intro hyes

    exact
      prime_candidate_opens_clock
        P
        p
        hstate
        hp
        hyes.1


-- --------------------------------------------------
-- One logical YES is one complete Pascal/clock step.
--
-- This theorem collects the connections already proved
-- elsewhere in the file into one statement.
-- --------------------------------------------------

theorem twin_prime_logic_yes_is_complete_pascal_step
    (P : List Nat)
    (c p R : Nat)
    (h2 : 2 ≤ P.length)
    (hstate : SieveState P p)
    (hopen : OpensClock P p)
    (h6 :
      baseBlock ∣ completedPeriod P)
    (hinterior :
      InteriorClockState P c)
    (hband :
      TwinPascalBand P R) :
    ∃ k,
      k < p
        ∧
      PrimeNat p
        ∧
      p ∈ relationProducts
            (p :: P) 1
        ∧
      InteriorClockState
        (p :: P)
        (lift c (completedPeriod P) k)
        ∧
      TwinPascalBand
        (p :: P)
        (extendRelation R p)
        ∧
      pascalEdgeDistance
        (p :: P)
        (twinPascalDegree (p :: P))
        = 2
        ∧
      (∀ r S,
        S ∈ relationProducts P r →
          S ∈ relationProducts
                (p :: P) r
            ∧
          extendRelation S p
            ∈ relationProducts
                (p :: P)
                (Nat.succ r))
        ∧
      (∀ r,
        (relationProducts
          (p :: P) r).length
          =
        choose
          (p :: P).length r) := by

  have hprimePascal :
      PrimeNat p
        ∧
      p ∈ relationProducts
            (p :: P) 1 :=
    opened_prime_enters_pascal_yes
      P p hstate hopen

  obtain
    ⟨
      k,
      hk,
      hnextInterior,
      hnextBand,
      hdistance
    ⟩ :=
    clock_state_and_pascal_band_advance_together
      P
      c
      p
      R
      h2
      hstate
      hopen
      h6
      hinterior
      hband

  refine
    ⟨
      k,
      hk,
      hprimePascal.1,
      hprimePascal.2,
      hnextInterior,
      hnextBand,
      hdistance,
      ?_,
      ?_
    ⟩

  · intro r S hS

    exact
      ⟨
        old_relation_mem_next
          P p r S hS,
        extended_relation_mem_next
          P p r S hS
      ⟩

  · intro r

    exact
      relation_count_is_choose
        (p :: P)
        r


def PascalTwinState
    (P : List Nat)
    (c R : Nat) : Prop :=
  InteriorClockState P c
    ∧
  TwinPascalBand P R
    ∧
  (pascalEdgeDistance
      P
      (twinPascalDegree P)
      = 2)
/-!
-- =====================================================================
-- 14. Reddit Requested twin-prime formulation
-- =====================================================================
--
-- The requested external formulation is
--
--     ∃ p : Nat,
--       n ≤ p ∧
--       Prime p ∧
--       Prime (p + 2).
--
-- This file uses PrimeNat rather than Mathlib's Prime predicate, so the
-- same statement in the vocabulary already proved here is
--
--     ∃ p : Nat,
--       n ≤ p ∧
--       PrimeNat p ∧
--       PrimeNat (p + 2).
--
-- Our construction uses the center c of the pair instead:
--
--     c - 1, c + 1.
--
-- The following theorem proves that the two formulations are exactly
-- equivalent under the coordinate change
--
--     p = c - 1.
-- =====================================================================
-/

def TwinPrimeCenterForm : Prop :=
  ∀ n : Nat,
    ∃ c : Nat,
      n + 1 ≤ c
        ∧
      PrimeNat (c - 1)
        ∧
      PrimeNat (c + 1)


def TwinPrimeConjecture : Prop :=
  ∀ n : Nat,
    ∃ p : Nat,
      n ≤ p
        ∧
      PrimeNat p
        ∧
      PrimeNat (p + 2)


theorem twin_prime_center_form_iff_twin_prime_conjecture :
    TwinPrimeCenterForm ↔ TwinPrimeConjecture := by

  constructor

  · intro hcenter n

    obtain ⟨c, hlarge, hleft, hright⟩ :=
      hcenter n

    refine
      ⟨
        c - 1,
        ?_,
        hleft,
        ?_
      ⟩

    · omega

    · have heq :
          (c - 1) + 2 = c + 1 := by
        omega

      rw [heq]

      exact hright


  · intro htpc n

    obtain ⟨p, hlarge, hp, hp2⟩ :=
      htpc n

    refine
      ⟨
        p + 1,
        ?_,
        ?_,
        ?_
      ⟩

    · omega

    · have heq :
          (p + 1) - 1 = p := by
        omega

      rw [heq]

      exact hp

    · have heq :
          (p + 1) + 1 = p + 2 := by
        omega

      rw [heq]

      exact hp2


#check twin_prime_center_form_iff_twin_prime_conjecture

#check locked23_is_pascal_zero_zero
#check prime_logic_yes_iff_pascal_yes
#check twin_prime_logic_yes_is_complete_pascal_step

#check twin_pascal_band_is_two_from_yes_edge
#check locked_base_starts_twin_pascal_band
#check locked_base_is_two_from_yes_edge
#check opened_prime_enters_pascal_yes
#check twin_pascal_degree_yes_step
#check twin_pascal_yes_step
#check twin_pascal_band_count
#check five_is_first_pascal_yes
#check clock_state_and_pascal_band_advance_together
#check six_starts_clock_and_pascal_geometry

#check member_divides_completedPeriod
#check safeAt_is_immutable
#check six_is_initial_interior_clock_state
#check interior_clock_state_recursive_step
#check six_is_initial_twin_center
#check six_is_initial_certified_twin_center
#check certified_twin_center_gives_twin_primes
#check surviving_composite_is_cross_position
#check divisor_gives_plus_boundary
#check divisor_gives_minus_boundary
#check old_factor_closes_either_boundary
#check phase_position_is_prime
#check sieve_open_is_prime
#check prime_candidate_opens_clock
#check sieve_open_iff_prime
#check opened_clock_is_new

#check pascal_extension
#check new_clock_is_degree_one_relation
#check pascal_relation_split
#check relation_count_is_choose
#check relation_count_pascal_extension
#check old_relation_mem_next
#check extended_relation_mem_next

#check completedPeriod_next
#check primeNat_coprime_of_not_dvd
#check completedPeriod_coprime_of_members
#check opened_clock_coprime_completedPeriod
#check sieve_to_pascal_period
#check relation_divides_completedPeriod
#check pascal_relations_divide_next_period

#check completed_relation_is_immutable
#check plus_relation_extends
#check minus_relation_extends

#check base_completed_period
#check two_is_prime_clock
#check three_is_prime_clock
#check base_sieve_state_five
#check five_opens_from_base
#check base_six_is_locked
#check locked23_is_carried_forever
#check locked23_never_becomes_boundary
#check baseBlock_divides_next

#check coprime_lifts_are_distinct
#check new_cycle_has_survivor
#check crt_bridge
#check pascal_crt_recursive_step
#check base_state_is_ready

end TwinPrimeClock
