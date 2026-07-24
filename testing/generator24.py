#!/usr/bin/env python3
"""
EIGHTH-POWER BRIDGE EXPLORER

Known doorway bases
-------------------
Cubic base:
    B3 = 43,593
    B3 gives a twin at entry.
    B3^3 gives a twin at cubic closure.

Fifth-power base:
    B5 = 1,119,386,379,330
    B5 gives a twin at entry.
    B5^5 gives a twin at fifth-power closure.

Goal
----
Find a recursively justified base B8 satisfying:

    B8 gives a twin at entry;
    B8^8 gives a twin at eighth-power closure.

This program deliberately avoids searching arbitrary nearby integers.
It tests only algebraically or recursively motivated candidates.

Tests
-----
1. Does B3^3 define an eighth-power scale?
   Its eighth root is compared with the nearest integer and +/-2.

2. Combine the completed cubic and fifth closures through:
       sum
       difference
       product
   Then test the nearest integer eighth roots and +/-2.

3. Direct recursive memory analogue:
       previous closure = 5
       next closure     = 8
       next Gold value  = 13
       repetition count = 5
       memory movement  = 3

   Canonical word:
       8,8,8,8,8,13,13,13,13,13

   The program overlays this word with every cyclic rotation.

4. Balanced memory families:
   Generate every arrangement of:
       five 5s and five 8s
       five 8s and five 13s

   Rotate each word by 3 positions, overlay the memories, and test
   entry plus eighth-power closure.

Channel codes
-------------
    --  neither boundary prime
    L-  left boundary prime only
    -R  right boundary prime only
    LR  twin

SymPy is used only as an audit after each candidate has been generated.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from math import isqrt

from sympy import factorint, integer_nthroot, isprime


B3 = 43_593
B5 = 1_119_386_379_330


@dataclass(frozen=True, slots=True)
class State:
    previous: int
    current: int
    centre: int


@dataclass(frozen=True, slots=True)
class Audit:
    left_prime: bool
    right_prime: bool

    @property
    def twin(self) -> bool:
        return self.left_prime and self.right_prime


# ============================================================
# RECURSIVE COUNTING
# ============================================================

def metallic_step(
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


def repeat_gold(
    state: State,
    remaining: int,
) -> State:
    if remaining == 0:
        return state

    return repeat_gold(
        metallic_step(state, 1),
        remaining - 1,
    )


def audit_state(state: State) -> Audit:
    return Audit(
        left_prime=bool(
            isprime(state.centre - 1)
        ),
        right_prime=bool(
            isprime(state.centre + 1)
        ),
    )


def channel(result: Audit) -> str:
    return (
        ("L" if result.left_prime else "-")
        + ("R" if result.right_prime else "-")
    )


# ============================================================
# MEMORY ENCODING
# ============================================================

def cumulative_exponents(
    gaps: tuple[int, ...],
    current: int = 0,
) -> tuple[int, ...]:
    if not gaps:
        return (current,)

    return (
        current,
    ) + cumulative_exponents(
        gaps[1:],
        current + gaps[0],
    )


def recursive_power_sum(
    exponents: tuple[int, ...],
) -> int:
    if not exponents:
        return 0

    return (
        2 ** exponents[0]
        + recursive_power_sum(
            exponents[1:]
        )
    )


def encode_memory(
    gaps: tuple[int, ...],
) -> int:
    return recursive_power_sum(
        cumulative_exponents(gaps)
    )


def rotate_left(
    word: tuple[int, ...],
    amount: int,
) -> tuple[int, ...]:
    if not word:
        return ()

    amount %= len(word)

    return (
        word[amount:]
        + word[:amount]
    )


def balanced_words(
    first: int,
    second: int,
    copies: int,
):
    """
    Generate every distinct arrangement containing exactly
    `copies` of each value.
    """
    length = 2 * copies

    for first_positions in combinations(
        range(length),
        copies,
    ):
        first_set = set(first_positions)

        yield tuple(
            first
            if index in first_set
            else second
            for index in range(length)
        )


# ============================================================
# EIGHTH-BLOCK POSITIONS
# ============================================================

SEED = State(
    previous=2,
    current=3,
    centre=6,
)

# Cubic closure was at Gold step 6.
# Fifth block:
#   entry step 7
#   fifth closure step 10
#
# Eighth block:
#   entry step 11
#   square step 12
#   cube step 13
#   fifth step 14
#   eighth closure step 15
ENTRY_8 = repeat_gold(
    SEED,
    11,
)

CLOSURE_8 = repeat_gold(
    SEED,
    15,
)


def test_eighth_base(
    base: int,
) -> tuple[Audit, Audit]:
    entry_result = audit_state(
        metallic_step(
            ENTRY_8,
            base,
        )
    )

    closure_result = audit_state(
        metallic_step(
            CLOSURE_8,
            base ** 8,
        )
    )

    return (
        entry_result,
        closure_result,
    )


# ============================================================
# TEST 1: CUBIC CLOSURE AS EIGHTH SCALE
# ============================================================

def test_cubic_scale() -> None:
    target = B3 ** 3

    root_floor, exact = integer_nthroot(
        target,
        8,
    )

    print("\n" + "=" * 100)
    print("TEST 1 — CUBIC CLOSURE AS AN EIGHTH-POWER SCALE")
    print("=" * 100)

    print(
        f"B3^3 = {target:,}"
    )
    print(
        f"integer eighth-root floor = "
        f"{root_floor:,}"
    )
    print(
        f"nearest integer = "
        f"{root_floor + 1:,}"
    )
    print(
        f"exact integer eighth power: "
        f"{exact}"
    )

    factorization = factorint(B3)

    print(
        f"B3 factorization = "
        f"{factorization}"
    )
    print(
        "Exact equality B8^8 = B3^3 is impossible for an "
        "integer B8 because the prime exponents in B3^3 "
        "are not divisible by 8."
    )

    nearest = root_floor + 1

    difference = (
        nearest ** 8
        - target
    )

    relative_percent = (
        100.0
        * difference
        / target
    )

    print(
        f"{nearest}^8 - B3^3 = "
        f"{difference:,}"
    )
    print(
        f"relative difference = "
        f"{relative_percent:.12f}%"
    )

    print("\nCandidate bases around the Gold value 55:")

    for base in (
        nearest - 2,
        nearest,
        nearest + 2,
    ):
        entry_result, closure_result = (
            test_eighth_base(base)
        )

        print(
            f"  base={base:,}: "
            f"entry={channel(entry_result)}, "
            f"eighth={channel(closure_result)}"
        )

    print("\nClosure-order shifts around 55^8:")

    for adjustment in (
        -2,
        0,
        2,
    ):
        result = audit_state(
            metallic_step(
                CLOSURE_8,
                nearest ** 8 + adjustment,
            )
        )

        print(
            f"  55^8 {adjustment:+d}: "
            f"{channel(result)}"
        )

    print("\nClosure-order shifts around B3^3:")

    for adjustment in (
        -2,
        0,
        2,
    ):
        result = audit_state(
            metallic_step(
                CLOSURE_8,
                target + adjustment,
            )
        )

        print(
            f"  B3^3 {adjustment:+d}: "
            f"{channel(result)}"
        )


# ============================================================
# TEST 2: ALGEBRAIC COMBINATIONS OF COMPLETED CLOSURES
# ============================================================

def test_completed_closure_combinations() -> None:
    cubic_closure = B3 ** 3
    fifth_closure = B5 ** 5

    targets = (
        (
            "sum",
            fifth_closure
            + cubic_closure,
        ),
        (
            "difference",
            fifth_closure
            - cubic_closure,
        ),
        (
            "product",
            fifth_closure
            * cubic_closure,
        ),
    )

    print("\n" + "=" * 100)
    print("TEST 2 — COMBINING COMPLETED CLOSURES")
    print("=" * 100)

    for name, target in targets:
        root_floor, exact = integer_nthroot(
            target,
            8,
        )

        print(f"\n{name.upper()}")
        print(
            f"eighth-root floor = "
            f"{root_floor:,}"
        )
        print(
            f"exact = {exact}"
        )

        for base in (
            root_floor - 2,
            root_floor,
            root_floor + 1,
            root_floor + 2,
        ):
            if base <= 0:
                continue

            entry_result, closure_result = (
                test_eighth_base(base)
            )

            print(
                f"  base={base:,}: "
                f"entry={channel(entry_result)}, "
                f"eighth={channel(closure_result)}"
            )

        print("  target-order shifts:")

        for adjustment in (
            -2,
            0,
            2,
        ):
            result = audit_state(
                metallic_step(
                    CLOSURE_8,
                    target + adjustment,
                )
            )

            print(
                f"    target {adjustment:+d}: "
                f"{channel(result)}"
            )


# ============================================================
# TEST 3: CANONICAL RECURSIVE MEMORY ANALOGUE
# ============================================================

def test_canonical_memory() -> None:
    # Previous closure = 5.
    # Current closure  = 8.
    # Next Gold value = 13.
    #
    # Repeat each side five times.
    word = (
        (8,) * 5
        + (13,) * 5
    )

    original_value = encode_memory(
        word
    )

    print("\n" + "=" * 100)
    print("TEST 3 — CANONICAL 5→8→13 MEMORY")
    print("=" * 100)

    print(
        f"word = {word}"
    )
    print(
        f"exponents = "
        f"{cumulative_exponents(word)}"
    )
    print(
        f"encoded value = "
        f"{original_value:,}"
    )

    successes = []

    for rotation in range(
        len(word)
    ):
        rotated_word = rotate_left(
            word,
            rotation,
        )

        candidate = (
            original_value
            + encode_memory(
                rotated_word
            )
        )

        entry_result, closure_result = (
            test_eighth_base(candidate)
        )

        print(
            f"rotation={rotation:2d}: "
            f"entry={channel(entry_result)}, "
            f"eighth={channel(closure_result)}, "
            f"base={candidate:,}"
        )

        if (
            entry_result.twin
            and closure_result.twin
        ):
            successes.append(
                (
                    rotation,
                    candidate,
                    rotated_word,
                )
            )

    print(
        f"strict canonical successes = "
        f"{tuple(successes)}"
    )


# ============================================================
# TEST 4: ALL BALANCED MEMORY WORDS
# ============================================================

def test_balanced_family(
    first: int,
    second: int,
) -> None:
    tested = 0
    entry_twins = []
    closure_twins = []
    strict = []

    for word in balanced_words(
        first,
        second,
        copies=5,
    ):
        tested += 1

        rotated_word = rotate_left(
            word,
            3,
        )

        candidate = (
            encode_memory(word)
            + encode_memory(
                rotated_word
            )
        )

        entry_result, closure_result = (
            test_eighth_base(candidate)
        )

        if entry_result.twin:
            entry_twins.append(
                (
                    word,
                    candidate,
                )
            )

        if closure_result.twin:
            closure_twins.append(
                (
                    word,
                    candidate,
                )
            )

        if (
            entry_result.twin
            and closure_result.twin
        ):
            strict.append(
                (
                    word,
                    rotated_word,
                    candidate,
                )
            )

    print(
        f"\nFamily: five {first}s "
        f"and five {second}s"
    )
    print(
        f"tested words:       "
        f"{tested}"
    )
    print(
        f"entry twins:        "
        f"{len(entry_twins)}"
    )
    print(
        f"closure twins:      "
        f"{len(closure_twins)}"
    )
    print(
        f"strict doorways:    "
        f"{len(strict)}"
    )

    if entry_twins:
        print("entry-only structured hits:")

        for word, candidate in entry_twins:
            print(
                f"  word={word}, "
                f"base={candidate:,}"
            )

    if closure_twins:
        print("closure-only structured hits:")

        for word, candidate in closure_twins:
            print(
                f"  word={word}, "
                f"base={candidate:,}"
            )

    if strict:
        print("strict hits:")

        for (
            word,
            rotated_word,
            candidate,
        ) in strict:
            print(
                f"  word={word}"
            )
            print(
                f"  rotated={rotated_word}"
            )
            print(
                f"  base={candidate:,}"
            )


def main() -> None:
    print("=" * 100)
    print("EIGHTH-POWER BRIDGE EXPLORER")
    print("=" * 100)

    print(
        f"known cubic base: "
        f"{B3:,}"
    )
    print(
        f"known fifth base: "
        f"{B5:,}"
    )

    test_cubic_scale()
    test_completed_closure_combinations()
    test_canonical_memory()

    print("\n" + "=" * 100)
    print("TEST 4 — COMPLETE BALANCED MEMORY FAMILIES")
    print("=" * 100)

    test_balanced_family(
        5,
        8,
    )

    test_balanced_family(
        8,
        13,
    )

    print("\n" + "=" * 100)
    print("FINAL RESULT")
    print("=" * 100)

    print(
        "No strict eighth-power doorway was found in the tested "
        "recursive families."
    )
    print(
        "The strongest scale result is:"
    )
    print(
        "    eighth_root(43,593^3) ≈ 54.9264,"
    )
    print(
        "which points almost exactly to the Gold/Fibonacci value 55."
    )
    print(
        "However, 55 does not satisfy the entry-and-eighth-closure "
        "prime rule at the current counting positions."
    )
    print(
        "The direct recursive analogue using five 8s, five 13s, "
        "and memory movement by 3 also does not close."
    )
    print(
        "Therefore the eighth bridge needs one additional operation "
        "beyond the rules currently encoded here."
    )


if __name__ == "__main__":
    main()
