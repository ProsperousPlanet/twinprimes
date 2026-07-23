#!/usr/bin/env python3
"""
RECURSIVE RATIO-LOOP EXPLORER

The ratio orders are not supplied as Gold/Silver/Bronze/etc.

They emerge from one recursive rule:

    R(seed, 0) = [seed]

    R(seed, depth) =
        R(seed, depth-1)
        followed by
        R(seed+1, depth-1)

Equivalent examples:

    depth 0:  1
    depth 1:  1,2
    depth 2:  1,2,2,3
    depth 3:  1,2,2,3,2,3,3,4
    depth 4:  ... ends at 5
    depth 6:  ... ends at 7
    depth 7:  ... ends at 8

So powers of two create cycles of cycles, while the unlimited indexed
ratio family appears automatically.

For a recursive period state (a,b,C), each emitted order m performs:

    next = a + m*b
    (a,b) = (b,next)
    C = C*next

At each depth, the final member of the 2^depth cycle is treated as the
lift marker.  The candidate centre is therefore produced from every
earlier member of that cycle.

Candidate generation never consults primality.

For experimental checking only, an exact deterministic 64-bit
Miller-Rabin audit is included. Larger candidates are generated but
left unaudited.
"""

from __future__ import annotations

from dataclasses import dataclass


# ============================================================
# CONFIGURATION
# ============================================================

MAX_DEPTH = 6

PRINT_CYCLES_THROUGH_DEPTH = 4

PRINT_FULL_CENTRE_THROUGH_DIGITS = 100


# ============================================================
# PURE RECURSIVE RATIO FAMILY
# ============================================================

def ratio_cycle(
    seed: int,
    depth: int,
) -> tuple[int, ...]:
    """
    Generate one complete nested ratio cycle.

    No metallic names or preselected ratio list are used.
    """
    if depth == 0:
        return (seed,)

    lower = ratio_cycle(
        seed,
        depth - 1,
    )

    upper = ratio_cycle(
        seed + 1,
        depth - 1,
    )

    return lower + upper


# ============================================================
# CENTRE RECURSION
# ============================================================

@dataclass(frozen=True, slots=True)
class State:
    previous: int
    current: int
    centre: int


def advance(
    state: State,
    order: int,
) -> State:
    next_period = (
        state.previous
        + order * state.current
    )

    return State(
        previous=state.current,
        current=next_period,
        centre=state.centre * next_period,
    )


def pre_lift_candidate(
    depth: int,
) -> tuple[State, tuple[int, ...]]:
    """
    Apply every recursively generated order except the final lift marker.
    """
    cycle = ratio_cycle(
        seed=1,
        depth=depth,
    )

    state = State(
        previous=2,
        current=3,
        centre=6,
    )

    for order in cycle[:-1]:
        state = advance(
            state,
            order,
        )

    return state, cycle


# ============================================================
# EXACT 64-BIT AUDIT ONLY
# ============================================================

UINT64_LIMIT = 1 << 64

_SMALL_PRIMES = (
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37
)

_MR_BASES_64 = (
    2,
    325,
    9375,
    28178,
    450775,
    9780504,
    1795265022,
)


def is_prime_64(number: int) -> bool:
    if number < 2:
        return False

    for prime in _SMALL_PRIMES:
        if number % prime == 0:
            return number == prime

    odd_part = number - 1
    power = 0

    while odd_part % 2 == 0:
        odd_part //= 2
        power += 1

    for base in _MR_BASES_64:
        if base % number == 0:
            continue

        value = pow(
            base,
            odd_part,
            number,
        )

        if value == 1 or value == number - 1:
            continue

        for _ in range(power - 1):
            value = pow(
                value,
                2,
                number,
            )

            if value == number - 1:
                break
        else:
            return False

    return True


def exact_audit(centre: int) -> str:
    if centre + 1 >= UINT64_LIMIT:
        return "ABOVE-64-BIT"

    if (
        is_prime_64(centre - 1)
        and is_prime_64(centre + 1)
    ):
        return "EXACT-TWIN"

    return "BLOCKED"


# ============================================================
# OUTPUT
# ============================================================

def digit_count(number: int) -> int:
    """
    Exact for the configured depths, which remain below Python's
    default integer-string safety limit.
    """
    return len(str(number))


def centre_preview(
    centre: int,
) -> str:
    text = str(centre)

    if len(text) <= PRINT_FULL_CENTRE_THROUGH_DIGITS:
        return f"{centre:,}"

    return (
        f"{text[:45]}...{text[-45:]}"
        f" [{len(text):,} digits]"
    )


def explore_depths(
    depth: int,
    maximum_depth: int,
) -> None:
    """
    Recursively examine deeper cycles.
    """
    state, cycle = pre_lift_candidate(
        depth
    )

    print("\n" + "=" * 80)
    print(
        f"DEPTH {depth}: "
        f"{len(cycle)}-STATE RECURSIVE CYCLE"
    )
    print("=" * 80)

    if depth <= PRINT_CYCLES_THROUGH_DEPTH:
        print(
            "complete cycle: "
            + ",".join(
                str(order)
                for order in cycle
            )
        )

    print(
        f"highest emergent ratio index: "
        f"{cycle[-1]}"
    )
    print(
        f"active operations before lift: "
        f"{len(cycle) - 1}"
    )
    print(
        f"terminal period pair: "
        f"({state.previous:,}, {state.current:,})"
    )
    print(
        f"candidate centre: "
        f"{centre_preview(state.centre)}"
    )
    print(
        f"candidate digits: "
        f"{digit_count(state.centre):,}"
    )
    print(
        f"internal 64-bit audit: "
        f"{exact_audit(state.centre)}"
    )

    if state.centre + 1 < UINT64_LIMIT:
        print(
            f"candidate pair: "
            f"{state.centre - 1:,} : "
            f"{state.centre:,} : "
            f"{state.centre + 1:,}"
        )

    if depth < maximum_depth:
        explore_depths(
            depth + 1,
            maximum_depth,
        )


def main() -> None:
    print("=" * 80)
    print("RECURSIVE RATIO-LOOP EXPLORER")
    print("=" * 80)
    print(
        "Only defining rule:"
    )
    print(
        "R(seed,d) = R(seed,d-1) followed by R(seed+1,d-1)"
    )
    print(
        "The ratio indices, powers-of-two cycle lengths, "
        "and lift values emerge from that recursion."
    )

    explore_depths(
        depth=1,
        maximum_depth=MAX_DEPTH,
    )

    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(
        "depth 3 reaches the eight-state cycle:"
    )
    print(
        "    1,2,2,3,2,3,3,4"
    )
    print(
        "depth 4 reaches ratio index 5."
    )
    print(
        "depth 6 reaches ratio index 7."
    )
    print(
        "depth 7 would reach ratio index 8."
    )
    print(
        "Nothing in the program names or injects those ratios."
    )
    print(
        "The remaining research problem is the exact centre-state "
        "reset applied when a complete cycle becomes one higher-level unit."
    )


if __name__ == "__main__":
    main()
