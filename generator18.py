#!/usr/bin/env python3
"""
RECURSIVE METALLIC RESET EXPLORER

This tests the reset suggested by the nested ratio cycles.

Nothing names Gold, Silver, Bronze, or a supplied correction sequence.

The ratio block is generated only by:

    R(seed, 0) = [seed]

    R(seed, depth) =
        R(seed, depth-1)
        followed by
        R(seed+1, depth-1)

At the completed eight-state edge:

    1,2,2,3,2,3,3,4

the seven active operations produce the exact twin centre

    714,564,840,927,600.

The terminal period pair is (835,2748).  Taking the integer seventh-root
scale, because seven operations formed the block, gives:

    floor(835^(1/7))  = 2
    floor(2748^(1/7)) = 3

The next reflected block begins with order 2, which is also obtained
from the recursion rather than inserted manually.

Therefore the first reset period is:

    2 + 2*3 = 8.

The same procedure is then repeated:
    1. complete the next four-state block;
    2. compress its terminal periods by the integer cube-root scale;
    3. take the first order of the next reflected block;
    4. apply that order once to the carried centre.

Candidate generation never consults primality.

Small factors are searched using the internally generated recursive
prime stream.  Values below 2^64 receive an exact deterministic audit.
SymPy, when installed, is used only as an independent audit for larger
candidates.
"""

from __future__ import annotations

from dataclasses import dataclass


# ============================================================
# CONFIGURATION
# ============================================================

CORRECTION_STAGES = 3
SMALL_FACTOR_LIMIT = 1_000_000
USE_SYMPY_AUDIT = True

UINT64_LIMIT = 1 << 64


# ============================================================
# PURE RECURSIVE RATIO BLOCK
# ============================================================

def ratio_block(
    seed: int,
    depth: int,
) -> tuple[int, ...]:
    if depth == 0:
        return (seed,)

    return (
        ratio_block(seed, depth - 1)
        + ratio_block(seed + 1, depth - 1)
    )


# ============================================================
# PERIOD AND CENTRE STATE
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


def apply_active_block(
    state: State,
    seed: int,
    depth: int,
) -> tuple[State, tuple[int, ...]]:
    block = ratio_block(seed, depth)

    for order in block[:-1]:
        state = advance(state, order)

    return state, block


# ============================================================
# INTEGER ROOT RESET
# ============================================================

def integer_nth_root(
    number: int,
    degree: int,
) -> int:
    """Return floor(number ** (1/degree)) exactly."""
    low = 0
    high = 1

    while high ** degree <= number:
        high *= 2

    while low + 1 < high:
        middle = (low + high) // 2

        if middle ** degree <= number:
            low = middle
        else:
            high = middle

    return low


def reset_pair(
    state: State,
    active_steps: int,
) -> tuple[int, int]:
    return (
        integer_nth_root(
            state.previous,
            active_steps,
        ),
        integer_nth_root(
            state.current,
            active_steps,
        ),
    )


def next_reflected_seed(
    seed: int,
    depth: int,
) -> int:
    """
    The first order after the lower half of the next larger block.
    """
    larger = ratio_block(seed, depth + 1)
    half = len(larger) // 2
    return larger[half]


# ============================================================
# INTERNAL RECURSIVE PRIME FACTORS
# ============================================================

def recursive_primes():
    yield 2

    events: dict[int, int] = {}
    candidate = 3

    while True:
        step = events.pop(candidate, None)

        if step is None:
            yield candidate
            events[candidate * candidate] = 2 * candidate
        else:
            next_completion = candidate + step

            while next_completion in events:
                next_completion += step

            events[next_completion] = step

        candidate += 2


def first_internal_factor(
    number: int,
) -> int | None:
    for prime in recursive_primes():
        if prime > SMALL_FACTOR_LIMIT:
            return None

        if prime * prime > number:
            return None

        if number % prime == 0:
            return prime

    return None


# ============================================================
# EXACT 64-BIT AUDIT
# ============================================================

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

        value = pow(base, odd_part, number)

        if value == 1 or value == number - 1:
            continue

        for _ in range(power - 1):
            value = pow(value, 2, number)

            if value == number - 1:
                break
        else:
            return False

    return True


try:
    from sympy import isprime as sympy_isprime
except ImportError:
    sympy_isprime = None


@dataclass(frozen=True, slots=True)
class Audit:
    status: str
    left_factor: int | None
    right_factor: int | None


def audit(
    centre: int,
) -> Audit:
    left = centre - 1
    right = centre + 1

    left_factor = first_internal_factor(left)
    right_factor = first_internal_factor(right)

    if left_factor is not None or right_factor is not None:
        return Audit(
            "BLOCKED",
            left_factor,
            right_factor,
        )

    if right < UINT64_LIMIT:
        return Audit(
            (
                "EXACT-TWIN"
                if is_prime_64(left) and is_prime_64(right)
                else "BLOCKED-BEYOND-SMALL-FACTOR-LIMIT"
            ),
            None,
            None,
        )

    if (
        USE_SYMPY_AUDIT
        and sympy_isprime is not None
    ):
        return Audit(
            (
                "INDEPENDENT-AUDIT-TWIN"
                if sympy_isprime(left) and sympy_isprime(right)
                else "INDEPENDENT-AUDIT-BLOCKED"
            ),
            None,
            None,
        )

    return Audit(
        "UNRESOLVED-BIGINT",
        None,
        None,
    )


# ============================================================
# RECURSIVE RESET EXPERIMENT
# ============================================================

def print_candidate(
    label: str,
    state: State,
) -> Audit:
    result = audit(state.centre)

    print(f"\n{label}")
    print(
        f"    periods: "
        f"({state.previous:,}, {state.current:,})"
    )
    print(
        f"    centre: {state.centre:,}"
    )
    print(
        f"    pair: "
        f"{state.centre - 1:,} : "
        f"{state.centre:,} : "
        f"{state.centre + 1:,}"
    )
    print(
        f"    status: {result.status}"
    )

    if result.left_factor is not None:
        print(
            f"    left blocked by internal cycle "
            f"{result.left_factor:,}"
        )

    if result.right_factor is not None:
        print(
            f"    right blocked by internal cycle "
            f"{result.right_factor:,}"
        )

    return result


def main() -> None:
    print("=" * 84)
    print("RECURSIVE METALLIC RESET EXPLORER")
    print("=" * 84)

    # Original eight-state edge.
    anchor, anchor_block = apply_active_block(
        State(2, 3, 6),
        seed=1,
        depth=3,
    )

    print_candidate(
        "EIGHT-STATE EDGE",
        anchor,
    )

    anchor_steps = len(anchor_block) - 1
    pair = reset_pair(
        anchor,
        anchor_steps,
    )

    seed = next_reflected_seed(
        seed=1,
        depth=3,
    )

    print("\nFIRST RESET")
    print(
        f"    active operations compressed: "
        f"{anchor_steps}"
    )
    print(
        f"    root-reset pair: {pair}"
    )
    print(
        f"    recursively emergent next seed: "
        f"{seed}"
    )

    first_reset = advance(
        State(
            pair[0],
            pair[1],
            anchor.centre,
        ),
        seed,
    )

    print(
        f"    emergent reset period: "
        f"{first_reset.current}"
    )

    print_candidate(
        "FIRST STEP AFTER RESET",
        first_reset,
    )

    # Each correction stage completes the four-state block for the
    # current seed, root-compresses its three active operations, and
    # applies the first order of the next reflected block.
    base_centre = anchor.centre
    current_pair = pair
    current_seed = seed

    for stage in range(1, CORRECTION_STAGES + 1):
        completed, block = apply_active_block(
            State(
                current_pair[0],
                current_pair[1],
                base_centre,
            ),
            seed=current_seed,
            depth=2,
        )

        print_candidate(
            f"STAGE {stage} COMPLETED FOUR-STATE BLOCK",
            completed,
        )

        active_steps = len(block) - 1
        new_pair = reset_pair(
            completed,
            active_steps,
        )
        new_seed = next_reflected_seed(
            seed=current_seed,
            depth=2,
        )

        corrected = advance(
            State(
                new_pair[0],
                new_pair[1],
                completed.centre,
            ),
            new_seed,
        )

        print(
            f"\nSTAGE {stage} RESET"
        )
        print(
            f"    compressed pair: {new_pair}"
        )
        print(
            f"    next reflected seed: {new_seed}"
        )
        print(
            f"    next period: {corrected.current}"
        )

        print_candidate(
            f"STAGE {stage} CORRECTED EDGE",
            corrected,
        )

        base_centre = completed.centre
        current_pair = new_pair
        current_seed = new_seed

    print("\n" + "=" * 84)
    print("INTERPRETATION")
    print("=" * 84)
    print(
        "The eight-state completion really does reset to the pair "
        "(2,3), and the reflected recursion supplies order 2."
    )
    print(
        "That creates period 8 and another exact twin centre."
    )
    print(
        "The same root-reset/reflection rule produces additional "
        "larger audited twin centres before eventually meeting another "
        "blocked stage."
    )
    print(
        "The next task is to determine which larger nested block must "
        "replace the four-state correction when that later blockage "
        "appears."
    )


if __name__ == "__main__":
    main()
