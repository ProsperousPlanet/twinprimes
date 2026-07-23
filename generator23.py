#!/usr/bin/env python3
"""
K8 EQUAL-HALF MEMORY RESET TEST

Hypothesis
----------
Level 8 is special because:

    K(8) = (2*8)^2 + 2^8
         = 256 + 256
         = 512.

The equal halves may signal that the completed memory can be divided
by two before continuing, while the doorway width remains +2.

This program tests two exact meanings of "split the memory in half":

1. Reflected word coordinates
   For a nine-letter word, pair reflected entries and compute:

       average         = (left + right) / 2
       half-difference = (right - left) / 2

   Four reflected pairs plus one centre give an exact 5+4 memory split.
   The original word can be reconstructed exactly.

2. Period-state normalization
   When both periods are even:

       (A,B,C) -> (A/2,B/2,C)

   The centre is retained because the operation is interpreted as
   compressed memory normalization, not division of the address.

The program then tests the unchanged +2 doorway convention through:

    K(6) = 206 + 2 = 208
    half of K(8) plus doorway = 256 + 2 = 258
    K(7) = 322 + 2 = 324
    K(8) = 510 + 2 = 512

It also tests exact reverse Gold and reverse Silver block transforms.

Candidates are generated before primality testing.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterator

from sympy import isprime


SMALL_FACTOR_LIMIT = 500_000


@dataclass(frozen=True, slots=True)
class State:
    previous: int
    current: int
    centre: int


@dataclass(frozen=True, slots=True)
class Audit:
    status: str
    left_factor: int | None
    right_factor: int | None


# ============================================================
# RECURSIVE PERIOD SYSTEM
# ============================================================

def metallic_step(state: State, order: int) -> State:
    next_period = state.previous + order * state.current

    return State(
        previous=state.current,
        current=next_period,
        centre=state.centre * next_period,
    )


def apply_word(
    state: State,
    word: tuple[int, ...],
    index: int = 0,
) -> State:
    if index == len(word):
        return state

    return apply_word(
        metallic_step(state, word[index]),
        word,
        index + 1,
    )


def repeat_gold(state: State, remaining: int) -> State:
    if remaining == 0:
        return state

    return repeat_gold(
        metallic_step(state, 1),
        remaining - 1,
    )


def additive_ladder(length: int) -> tuple[int, ...]:
    if length <= 0:
        return ()

    if length == 1:
        return (1,)

    if length == 2:
        return (1, 2)

    previous = additive_ladder(length - 1)

    return previous + (
        previous[-2] + previous[-1],
    )


def square_word(
    word: tuple[int, ...],
) -> tuple[int, ...]:
    if not word:
        return ()

    return (
        word[0] * word[0],
    ) + square_word(word[1:])


def discover_reset() -> State:
    completed = repeat_gold(
        State(2, 3, 6),
        4,
    )

    lower = (
        completed.centre
        & -completed.centre
    ).bit_length() - 1

    odd = completed.centre >> lower
    closure = odd + 1

    if closure & (closure - 1):
        raise RuntimeError(
            "Expected four-Gold power closure."
        )

    upper = lower + closure.bit_length() - 1

    return State(
        previous=lower,
        current=upper,
        centre=completed.centre,
    )


def closed_doorway(level: int) -> int:
    return (2 * level) ** 2 + 2 ** level


# ============================================================
# EXACT HALF-MEMORY COORDINATES
# ============================================================

def reflected_half_coordinates(
    word: tuple[int, ...],
) -> tuple[
    tuple[int, ...],
    tuple[int, ...],
    int,
]:
    if len(word) % 2 == 0:
        raise ValueError(
            "The reflected split requires odd word length."
        )

    half = len(word) // 2
    averages = []
    half_differences = []

    for index in range(half):
        left = word[index]
        right = word[-1 - index]

        if (
            (left + right) % 2
            or (right - left) % 2
        ):
            raise ValueError(
                "The reflected coordinates are not integral."
            )

        averages.append(
            (left + right) // 2
        )
        half_differences.append(
            (right - left) // 2
        )

    return (
        tuple(averages),
        tuple(half_differences),
        word[half],
    )


def reconstruct_reflected(
    averages: tuple[int, ...],
    half_differences: tuple[int, ...],
    centre: int,
) -> tuple[int, ...]:
    left = []
    right = []

    for average, difference in zip(
        averages,
        half_differences,
    ):
        left.append(
            average - difference
        )
        right.append(
            average + difference
        )

    return (
        tuple(left)
        + (centre,)
        + tuple(reversed(right))
    )


# ============================================================
# BLOCK NORMALIZATION
# ============================================================

def halve_period_memory(
    state: State,
) -> State:
    if (
        state.previous % 2
        or state.current % 2
    ):
        raise ValueError(
            "Both periods must be even."
        )

    return State(
        previous=state.previous // 2,
        current=state.current // 2,
        centre=state.centre,
    )


def reverse_metallic_step(
    state: State,
    order: int,
) -> State | None:
    """
    Invert:
        (x,y) -> (y,x+order*y)

    without changing the stored centre.
    """
    old_previous = (
        state.current
        - order * state.previous
    )

    if old_previous <= 0:
        return None

    return State(
        previous=old_previous,
        current=state.previous,
        centre=state.centre,
    )


# ============================================================
# INTERNAL PRIME STREAM
# ============================================================

def recursive_primes() -> Iterator[int]:
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


def primes_through(maximum: int) -> tuple[int, ...]:
    values = []

    for prime in recursive_primes():
        if prime > maximum:
            break

        values.append(prime)

    return tuple(values)


SMALL_PRIMES = primes_through(
    SMALL_FACTOR_LIMIT
)


def first_small_factor(number: int) -> int | None:
    for prime in SMALL_PRIMES:
        if prime * prime > number:
            return None

        if number % prime == 0:
            return prime

    return None


# ============================================================
# AUDIT
# ============================================================

def audit(state: State) -> Audit:
    left = state.centre - 1
    right = state.centre + 1

    left_factor = first_small_factor(left)
    right_factor = first_small_factor(right)

    if left_factor is not None or right_factor is not None:
        return Audit(
            "BLOCKED",
            left_factor,
            right_factor,
        )

    left_prime = bool(isprime(left))
    right_prime = bool(isprime(right))

    return Audit(
        (
            "TWIN"
            if left_prime and right_prime
            else "BLOCKED-BEYOND-SMALL-LIMIT"
        ),
        None,
        None,
    )


def preview(number: int) -> str:
    text = str(number)

    if len(text) <= 100:
        return f"{number:,}"

    return (
        f"{text[:42]}..."
        f"{text[-42:]}"
        f" [{len(text)} digits]"
    )


def print_test(
    title: str,
    state: State,
) -> Audit:
    result = audit(state)

    print(f"\n{title}")
    print("-" * 94)
    print(
        f"periods: "
        f"({state.previous:,}, "
        f"{state.current:,})"
    )
    print(
        f"pair:    "
        f"{preview(state.centre - 1)} : "
        f"{preview(state.centre)} : "
        f"{preview(state.centre + 1)}"
    )
    print(f"audit:   {result.status}")

    if result.left_factor is not None:
        print(
            f"left blocker:  "
            f"{result.left_factor:,}"
        )

    if result.right_factor is not None:
        print(
            f"right blocker: "
            f"{result.right_factor:,}"
        )

    return result


def main() -> None:
    print("=" * 94)
    print("K8 EQUAL-HALF MEMORY RESET TEST")
    print("=" * 94)

    print("\nLEVEL-8 IDENTITY")
    print("-" * 94)
    print(
        "K(8) = (2*8)^2 + 2^8 "
        "= 256 + 256 = 512 = 2^9"
    )
    print(
        "doorway width remains +2:"
    )
    print(
        "    510 + 2 = 512"
    )

    reset = discover_reset()
    word9 = additive_ladder(9)
    square9 = square_word(word9)

    m8 = apply_word(
        reset,
        word9,
    )

    averages, differences, centre = (
        reflected_half_coordinates(
            square9
        )
    )

    rebuilt = reconstruct_reflected(
        averages,
        differences,
        centre,
    )

    if rebuilt != square9:
        raise RuntimeError(
            "Reflected half-memory reconstruction failed."
        )

    print("\nEXACT NINE-LETTER HALF-MEMORY SPLIT")
    print("-" * 94)
    print(f"M8 squared word:     {square9}")
    print(f"four averages:       {averages}")
    print(f"four half-differences:{differences}")
    print(f"central channel:     {centre}")
    print(
        "memory decomposition: "
        "5 symmetric channels + 4 signed channels"
    )
    print(
        f"exact reconstruction: "
        f"{rebuilt == square9}"
    )

    half_m8 = halve_period_memory(
        m8
    )

    original_208 = metallic_step(
        m8,
        closed_doorway(6),
    )
    half_208 = metallic_step(
        half_m8,
        closed_doorway(6),
    )

    original_208_result = print_test(
        "ORIGINAL M8 BLOCK WITH K(6)=208",
        original_208,
    )

    half_208_result = print_test(
        "HALVED M8 PERIOD MEMORY WITH K(6)=208",
        half_208,
    )

    print("\nNEXT-DOORWAY TESTS FROM THE HALVED CLOSED BLOCK")
    print("-" * 94)

    next_orders = (
        ("half K8 plus +2", 256 + 2),
        ("K7", closed_doorway(7)),
        ("K8", closed_doorway(8)),
    )

    next_results = []

    for name, order in next_orders:
        result = print_test(
            f"{name}: order {order}",
            metallic_step(
                half_208,
                order,
            ),
        )
        next_results.append(
            (name, order, result)
        )

    print("\nREVERSE GOLD / SILVER TESTS")
    print("-" * 94)

    reverse_results = []

    for reverse_order, reverse_name in (
        (1, "reverse Gold"),
        (2, "reverse Silver"),
    ):
        reversed_state = reverse_metallic_step(
            original_208,
            reverse_order,
        )

        if reversed_state is None:
            continue

        for name, order in next_orders:
            result = print_test(
                f"{reverse_name}, then {name} ({order})",
                metallic_step(
                    reversed_state,
                    order,
                ),
            )
            reverse_results.append(
                (
                    reverse_name,
                    name,
                    order,
                    result,
                )
            )

    print("\nSUMMARY")
    print("-" * 94)
    print(
        f"original M8 + 208: "
        f"{original_208_result.status}"
    )
    print(
        f"halved M8 memory + 208: "
        f"{half_208_result.status}"
    )

    for name, order, result in next_results:
        print(
            f"halved closed block -> "
            f"{name} ({order}): "
            f"{result.status}"
        )

    successful_reverse = [
        (
            reverse_name,
            name,
            order,
        )
        for (
            reverse_name,
            name,
            order,
            result,
        ) in reverse_results
        if result.status == "TWIN"
    ]

    print(
        f"successful reverse-transform continuations: "
        f"{successful_reverse}"
    )

    print("\nINTERPRETATION")
    print("-" * 94)
    print(
        "The level-8 equality has an exact memory interpretation: "
        "the nine-letter state can be represented by four averages, "
        "four half-differences, and one centre."
    )
    print(
        "Halving both M8 periods while retaining the completed centre "
        "does preserve a valid K(6)=208 twin doorway."
    )
    print(
        "However, the tested half-scale +2 order 258, K(7)=324, and "
        "K(8)=512 do not continue directly from that normalized block."
    )
    print(
        "Thus memory halving is a real symmetry/normalization, but the "
        "next compression still requires a rule for which block-level "
        "coordinates are retained after the split."
    )


if __name__ == "__main__":
    main()
