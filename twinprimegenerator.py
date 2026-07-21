#!/usr/bin/env python3
"""
Twin Prime Geometry — exploratory simulator

This program models the ideas currently under discussion:

1. Internal recursive loops approaching sqrt(2) and sqrt(3).
2. The Fibonacci-ratio loop approaching phi.
3. The combined root experiment:
       sqrt(2)^2 + sqrt(3)^2 = 5
       (1 + sqrt(5)) / 2 = phi
4. Completion states:
       N(a, b) = 2a + 3b
   so 3 = N(0,1) and 5 = N(1,1).
5. Crossings of the 2- and 3-systems:
       2(3n) = 3(2n) = 6n
6. The reflected boundaries:
       6n - 1, 6n, 6n + 1

This is an experimental model, not yet a proof.
Change the values in CONFIGURATION to test different ranges.
"""

from fractions import Fraction
from math import isqrt, sqrt


# ============================================================
# CONFIGURATION
# ============================================================
# Largest INTEGER allowed in the scan.
# A twin-prime pair is counted only when BOTH primes are <= MAX_NUMBER.
# For example, MAX_NUMBER = 1_000_000 counts pairs (p, p+2) with
# p + 2 <= 1_000_000.
#
MAX_NUMBER = 4_000_000

# Include the exceptional first twin-prime pair (3, 5).
# Every later twin-prime pair has a centre divisible by 6.
INCLUDE_EXCEPTIONAL_PAIR = True

# Printing thousands of pairs can make the terminal difficult to read.
# Set this to True when you want every pair printed.
PRINT_EACH_TWIN_CENTRE = False

# When False, blocked centres are not printed.
# Set True only for small MAX_NUMBER values.
PRINT_BLOCKED_CENTRES = False

# Optional early stopping condition.
# Example: set to 20 to stop after finding 20 total twin-prime pairs.
STOP_AFTER_TWIN_CENTRES = None
# ============================================================
# DEMONSTRATION DISPLAY LIMITS
#
# These values only control how many example rows are printed.
# They do not alter the equations, generated sequences, or
# twin-prime scan results.
# ============================================================
ROOT_ITERATIONS = 10
PHI_ITERATIONS = 10
COUPLED_ITERATIONS = 10
REPEATED_ROOT_ITERATIONS = 8

MAX_A_COMPLETIONS = 6
MAX_B_COMPLETIONS = 4
MAX_PHI_TIER = 4

# ============================================================
# PRIME AND FACTOR TOOLS
# ============================================================

def build_prime_table(limit):
    """
    Build a fast lookup table for primality from 0 through limit.

    This is the Sieve of Eratosthenes. It is used only to check the
    generated 6n +/- 1 boundaries efficiently.

    prime_table[number] is:
        True  -> number is prime
        False -> number is not prime
    """
    if limit < 0:
        raise ValueError("limit must be non-negative")

    prime_table = bytearray(b"\x01") * (limit + 1)

    if limit >= 0:
        prime_table[0] = 0
    if limit >= 1:
        prime_table[1] = 0

    divisor = 2

    while divisor * divisor <= limit:
        if prime_table[divisor]:
            first_composite = divisor * divisor
            count = ((limit - first_composite) // divisor) + 1

            prime_table[
                first_composite : limit + 1 : divisor
            ] = b"\x00" * count

        divisor += 1

    return prime_table


def is_prime(number):
    """Return True when number is prime."""
    if number < 2:
        return False
    if number == 2:
        return True
    if number % 2 == 0:
        return False

    divisor = 3
    limit = isqrt(number)

    while divisor <= limit:
        if number % divisor == 0:
            return False
        divisor += 2

    return True


def smallest_factor_pair(number):
    """
    Return the smallest nontrivial factor pair.

    A composite boundary can be interpreted as being crossed
    or blocked by another factor system.
    """
    if number < 4:
        return None

    if number % 2 == 0:
        return 2, number // 2

    divisor = 3
    limit = isqrt(number)

    while divisor <= limit:
        if number % divisor == 0:
            return divisor, number // divisor
        divisor += 2

    return None


def describe_boundary(number):
    """Describe a boundary as open/prime or blocked/composite."""
    if is_prime(number):
        return f"{number}: OPEN (prime)"

    factors = smallest_factor_pair(number)

    if factors is None:
        return f"{number}: neither prime nor positive composite"

    return f"{number}: BLOCKED ({factors[0]} x {factors[1]})"


# ============================================================
# ROOT AND PHI LOOPS
# ============================================================

def root_step(value, dimension):
    """
    Internal root recursion:

        x_next = (x + d)/(x + 1)

    At the fixed point:

        x = (x + d)/(x + 1)
        x^2 = d
        x = sqrt(d)
    """
    return (value + dimension) / (value + 1)


def phi_step(value):
    """
    Golden-ratio completion recursion:

        x_next = 1 + 1/x

    At the fixed point:

        x^2 = x + 1
        x = phi
    """
    return 1 + Fraction(1, value)


def show_root_loop(dimension, iterations):
    """Display exact rational steps toward sqrt(dimension)."""
    value = Fraction(1, 1)
    target = sqrt(dimension)

    print(f"\nROOT LOOP: d={dimension}, target=sqrt({dimension})")
    print("step | exact fraction | decimal        | error")
    print("-" * 59)

    for step in range(iterations + 1):
        decimal = float(value)
        error = abs(decimal - target)

        print(
            f"{step:>4} | {str(value):<14} | "
            f"{decimal:<14.10f} | {error:.3e}"
        )

        value = root_step(value, dimension)


def show_phi_loop(iterations):
    """Display Fibonacci-ratio steps toward phi."""
    value = Fraction(1, 1)
    phi = (1 + sqrt(5)) / 2

    print("\nPHI COMPLETION LOOP")
    print("step | exact fraction | decimal        | error")
    print("-" * 59)

    for step in range(iterations + 1):
        decimal = float(value)
        error = abs(decimal - phi)

        print(
            f"{step:>4} | {str(value):<14} | "
            f"{decimal:<14.10f} | {error:.3e}"
        )

        value = phi_step(value)


def show_coupled_loop(iterations):
    """
    Run the root-2 and root-3 loops together.

    As the two roots complete:

        combined = sqrt(r2^2 + r3^2) -> sqrt(5)
        phi_candidate = (1 + combined)/2 -> phi
    """
    r2 = Fraction(1, 1)
    r3 = Fraction(1, 1)

    print("\nCOUPLED ROOT-2 / ROOT-3 LOOP")
    print("step | r2          | r3          | combined    | phi candidate")
    print("-" * 72)

    for step in range(iterations + 1):
        r2_decimal = float(r2)
        r3_decimal = float(r3)

        combined = sqrt(r2_decimal**2 + r3_decimal**2)
        phi_candidate = (1 + combined) / 2

        print(
            f"{step:>4} | "
            f"{r2_decimal:<11.8f} | "
            f"{r3_decimal:<11.8f} | "
            f"{combined:<11.8f} | "
            f"{phi_candidate:.8f}"
        )

        r2 = root_step(r2, 2)
        r3 = root_step(r3, 3)


def show_repeated_root_loop(iterations):
    """
    Repeated-root doorway:

        s_0 = 2
        s_(r+1) = sqrt(s_r)

    Every finite s_r remains greater than 1.
    """
    scale = 2.0

    print("\nREPEATED-ROOT DOORWAY")
    print("step | s_r              | 1/sqrt(s_r)")
    print("-" * 49)

    for step in range(iterations + 1):
        reciprocal = 1 / sqrt(scale)
        print(f"{step:>4} | {scale:<16.12f} | {reciprocal:.12f}")
        scale = sqrt(scale)


# ============================================================
# COMPLETION STATES
# ============================================================

def completion_value(a, b):
    """
    Additive completion state:

        N(a,b) = 2a + 3b

    This models reachability, not factorization.
    """
    return 2*a + 3*b


def show_completion_grid(max_a, max_b):
    """Show how completed 2- and 3-operations reach integers."""
    print("\nCOMPLETION GRID: N(a,b) = 2a + 3b")
    print("a = completed 2-operations")
    print("b = completed 3-operations\n")

    header = "b\\a | " + " ".join(f"{a:>4}" for a in range(max_a + 1))
    print(header)
    print("-" * len(header))

    for b in range(max_b + 1):
        row = [
            f"{completion_value(a, b):>4}"
            for a in range(max_a + 1)
        ]
        print(f"{b:>3} | " + " ".join(row))

    print("\nImportant seed states:")
    print(f"  N(0,1) = {completion_value(0,1)}")
    print(f"  N(1,1) = {completion_value(1,1)}")
    print("  Holding b=1 gives: 3, 5, 7, 9, 11, ...")


# ============================================================
# SHARED PHI TIERS
# ============================================================

def show_phi_tiers(max_tier):
    """
    Give both systems the same completed scale phi^k.

    Their first crossing in every tier is:

        2*3*phi^k = 3*2*phi^k = 6*phi^k
    """
    phi = (1 + sqrt(5)) / 2

    print("\nSHARED PHI TIERS")
    print("tier | unit phi^k    | 2-system crossing | 3-system crossing")
    print("-" * 68)

    for tier in range(max_tier + 1):
        unit = phi**tier
        system_2 = 2 * 3 * unit
        system_3 = 3 * 2 * unit

        print(
            f"{tier:>4} | "
            f"{unit:<13.9f} | "
            f"{system_2:<17.9f} | "
            f"{system_3:.9f}"
        )


# ============================================================
# CROSSING CENTRES
# ============================================================

def scan_crossing_centres():
    """
    Scan the 2-and-3 crossing centres:

        centre = 6n
        left   = 6n - 1
        right  = 6n + 1

    The scan stops when the RIGHT boundary would exceed MAX_NUMBER.

    This is the correct interpretation of "twin primes up to N":
    both primes in the pair must be no greater than N.

    The exceptional first pair (3, 5) is counted separately because
    its centre is 4 rather than a multiple of 6.
    """
    if MAX_NUMBER < 2:
        print("\nMAX_NUMBER is below the first prime.")
        return

    print("\nCROSSING CENTRES")
    print("2(3n) = 3(2n) = 6n")
    print(
        f"Counting twin-prime pairs whose right boundary "
        f"is <= {MAX_NUMBER:,}.\n"
    )

    prime_table = build_prime_table(MAX_NUMBER)

    examined_centres = 0
    twin_pairs = []
    twin_count = 0

    # The exceptional pair is not centred on 6n.
    if INCLUDE_EXCEPTIONAL_PAIR and MAX_NUMBER >= 5:
        twin_pairs.append((3, 4, 5))
        twin_count += 1

        if PRINT_EACH_TWIN_CENTRE:
            print(
                "exceptional centre=4 [TWIN CENTRE]\n"
                "    left:  3: OPEN (prime)\n"
                "    right: 5: OPEN (prime)"
            )

    n = 1

    try:
        while True:
            centre = 6 * n
            left = centre - 1
            right = centre + 1

            # Correct stopping rule:
            # do not test a pair whose upper prime exceeds MAX_NUMBER.
            if right > MAX_NUMBER:
                break

            examined_centres += 1

            left_prime = bool(prime_table[left])
            right_prime = bool(prime_table[right])
            twin = left_prime and right_prime

            if twin:
                twin_count += 1
                twin_pairs.append((left, centre, right))

                if PRINT_EACH_TWIN_CENTRE:
                    print(
                        f"n={n:<8} centre={centre:<10} [TWIN CENTRE]\n"
                        f"    2-system: 2 * {3*n} = {centre}\n"
                        f"    3-system: 3 * {2*n} = {centre}\n"
                        f"    left:  {left}: OPEN (prime)\n"
                        f"    right: {right}: OPEN (prime)"
                    )

            elif PRINT_BLOCKED_CENTRES:
                print(
                    f"n={n:<8} centre={centre:<10} [BLOCKED]\n"
                    f"    2-system: 2 * {3*n} = {centre}\n"
                    f"    3-system: 3 * {2*n} = {centre}\n"
                    f"    left:  {describe_boundary(left)}\n"
                    f"    right: {describe_boundary(right)}"
                )

            if (
                STOP_AFTER_TWIN_CENTRES is not None
                and twin_count >= STOP_AFTER_TWIN_CENTRES
            ):
                print("\nTwin-centre stopping condition reached.")
                break

            n += 1

    except KeyboardInterrupt:
        print("\nScan stopped by user.")

    print("\nSCAN SUMMARY")
    print("-" * 60)
    print(f"Maximum integer tested:        {MAX_NUMBER:,}")
    print(f"6n centres examined:           {examined_centres:,}")
    print(f"Twin-prime pairs found:        {twin_count:,}")

    if INCLUDE_EXCEPTIONAL_PAIR and MAX_NUMBER >= 5:
        print("Exceptional pair included:     (3, 5)")
        print(
            f"Pairs centred on 6n:           "
            f"{twin_count - 1:,}"
        )
    else:
        print("Exceptional pair included:     no")

    if twin_pairs:
        first_left, first_centre, first_right = twin_pairs[0]
        last_left, last_centre, last_right = twin_pairs[-1]

        print(
            f"First pair:                    "
            f"({first_left:,}, {first_right:,})"
        )
        print(
            f"Last pair in range:            "
            f"({last_left:,}, {last_right:,})"
        )

    if MAX_NUMBER == 1_000_000:
        expected = 8_169

        print(f"Known expected count:          {expected:,}")

        if twin_count == expected:
            print("Verification:                  PASS")
        else:
            print("Verification:                  FAIL")


# ============================================================
# MAIN
# ============================================================

def main():
    print("=" * 70)
    print("TWIN PRIME GEOMETRY — EXPLORATORY SIMULATOR")
    print("=" * 70)

    show_root_loop(2, ROOT_ITERATIONS)
    show_root_loop(3, ROOT_ITERATIONS)
    show_phi_loop(PHI_ITERATIONS)
    show_coupled_loop(COUPLED_ITERATIONS)
    show_repeated_root_loop(REPEATED_ROOT_ITERATIONS)

    show_completion_grid(
        MAX_A_COMPLETIONS,
        MAX_B_COMPLETIONS,
    )

    show_phi_tiers(MAX_PHI_TIER)
    scan_crossing_centres()


if __name__ == "__main__":
    main()
