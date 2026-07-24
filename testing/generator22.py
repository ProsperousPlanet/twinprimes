#!/usr/bin/env python3
"""
RECURSIVE SYMMETRIC-POWER TWIN ADDRESS GENERATOR

Generate one deterministic candidate-address path from the Gold and
symmetric-power memory deductions.

No correction masks are searched.
No prime result changes the generated path.

Rules
-----
1. Gold recursion:
       (a,b) -> (b,a+b)

2. Four Gold steps from (2,3), centre 6, produce:
       65,520 = 2^16 - 2^4

   so the reset period state is:
       (4,16).

3. Lifted leading coefficients are generated recursively:
       1,2,3,5,8,13,...

4. Degree d uses d+1 memory letters.

5. Squaring the represented power promotes:
       d -> 2d
       d+1 letters -> 2d+1 letters.

The tested path is:

    degree 4 leading-memory
    degree 4 component-square
    promote 4 -> 8
    degree 8 leading-memory
    degree 8 component-square
    promote 8 -> 16
    degree 16 leading-memory

Candidates are generated first. SymPy audits C-1 and C+1 afterward.
Blocked candidates are scanned for small factors using an internally
generated recursive prime stream.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterator

from sympy import isprime


START_DEGREE = 4
MEMORY_LEVELS = 3
SMALL_FACTOR_LIMIT = 100_000


@dataclass(frozen=True, slots=True)
class State:
    previous: int
    current: int
    centre: int


@dataclass(frozen=True, slots=True)
class Address:
    level: int
    degree: int
    projection: str
    word: tuple[int, ...]
    state: State


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


def discover_reset() -> State:
    completed = repeat_gold(
        State(2, 3, 6),
        remaining=4,
    )

    lower = (
        completed.centre
        & -completed.centre
    ).bit_length() - 1

    odd_part = completed.centre >> lower
    closure = odd_part + 1

    if closure & (closure - 1):
        raise RuntimeError(
            "The four-Gold completion did not close to a power of two."
        )

    upper = lower + closure.bit_length() - 1

    return State(
        previous=lower,
        current=upper,
        centre=completed.centre,
    )


# ============================================================
# RECURSIVE MEMORY SYSTEM
# ============================================================

def additive_ladder(length: int) -> tuple[int, ...]:
    """Generate 1,2,3,5,8,... recursively."""
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


def memory_degrees(
    degree: int,
    remaining: int,
) -> tuple[int, ...]:
    if remaining == 0:
        return ()

    return (
        degree,
    ) + memory_degrees(
        degree + degree,
        remaining - 1,
    )


def generate_addresses(
    reset: State,
) -> Iterator[Address]:
    """
    Generate the entire path before any primality audit.
    """
    for level, degree in enumerate(
        memory_degrees(
            START_DEGREE,
            MEMORY_LEVELS,
        ),
        start=1,
    ):
        word = additive_ladder(degree + 1)

        yield Address(
            level=level,
            degree=degree,
            projection="leading-memory",
            word=word,
            state=apply_word(reset, word),
        )

        if level < MEMORY_LEVELS:
            projected = square_word(word)

            yield Address(
                level=level,
                degree=degree,
                projection="component-square",
                word=projected,
                state=apply_word(reset, projected),
            )


# ============================================================
# INTERNAL SMALL-FACTOR CYCLES
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


def recursive_primes_through(
    maximum: int,
) -> tuple[int, ...]:
    values = []

    for prime in recursive_primes():
        if prime > maximum:
            break

        values.append(prime)

    return tuple(values)


SMALL_PRIMES = recursive_primes_through(
    SMALL_FACTOR_LIMIT
)


def first_small_factor(
    number: int,
) -> int | None:
    for prime in SMALL_PRIMES:
        if number % prime == 0:
            return prime

    return None


# ============================================================
# STANDARD AUDIT
# ============================================================

def audit(centre: int) -> Audit:
    left = centre - 1
    right = centre + 1

    left_prime = bool(isprime(left))
    right_prime = bool(isprime(right))

    return Audit(
        status=(
            "TWIN"
            if left_prime and right_prime
            else "BLOCKED"
        ),
        left_factor=(
            None
            if left_prime
            else first_small_factor(left)
        ),
        right_factor=(
            None
            if right_prime
            else first_small_factor(right)
        ),
    )


# ============================================================
# DISPLAY
# ============================================================

def preview(number: int) -> str:
    text = str(number)

    if len(text) <= 100:
        return f"{number:,}"

    return (
        f"{text[:42]}..."
        f"{text[-42:]}"
        f" [{len(text)} digits]"
    )


def word_preview(
    word: tuple[int, ...],
) -> str:
    if len(word) <= 12:
        return str(word)

    return (
        str(word[:6])[:-1]
        + ", ..., "
        + str(word[-6:])[1:]
    )


def print_address(
    address: Address,
) -> Audit:
    result = audit(address.state.centre)

    print(
        f"\nADDRESS "
        f"M{address.degree}:"
        f"{address.projection}"
    )
    print("-" * 92)
    print(f"memory level:  {address.level}")
    print(f"word length:   {len(address.word)}")
    print(f"word:          {word_preview(address.word)}")
    print(
        f"final periods: "
        f"({address.state.previous:,}, "
        f"{address.state.current:,})"
    )
    print(
        f"pair:          "
        f"{preview(address.state.centre - 1)}"
        f" : "
        f"{preview(address.state.centre)}"
        f" : "
        f"{preview(address.state.centre + 1)}"
    )
    print(f"audit:         {result.status}")

    if result.left_factor is not None:
        print(f"left blocker:  {result.left_factor:,}")

    if result.right_factor is not None:
        print(f"right blocker: {result.right_factor:,}")

    return result


def main() -> None:
    print("=" * 92)
    print("RECURSIVE SYMMETRIC-POWER TWIN ADDRESS GENERATOR")
    print("=" * 92)

    reset = discover_reset()

    print("\nRECURSIVELY DISCOVERED RESET")
    print("-" * 92)
    print(f"centre:       {reset.centre:,}")
    print(
        f"period state: "
        f"({reset.previous},{reset.current})"
    )
    print(
        f"identity:     "
        f"{reset.centre:,} "
        f"= 2^{reset.current} "
        f"- 2^{reset.previous}"
    )

    results = []

    for address in generate_addresses(reset):
        results.append(
            (
                address,
                print_address(address),
            )
        )

    print("\nPATH SUMMARY")
    print("-" * 92)

    for address, result in results:
        print(
            f"M{address.degree:<3} "
            f"{address.projection:<20} "
            f"{result.status}"
        )

    first_wall = next(
        (
            address
            for address, result in results
            if result.status == "BLOCKED"
        ),
        None,
    )

    print("\nINTERPRETATION")
    print("-" * 92)
    print(
        "Every address was generated before the prime audit."
    )
    print(
        "The current deterministic branch produces three twin "
        "addresses in sequence:"
    )
    print("    M4 leading-memory")
    print("    M4 component-square")
    print("    M8 leading-memory")

    if first_wall is not None:
        print(
            "The first wall is:"
        )
        print(
            f"    M{first_wall.degree}:"
            f"{first_wall.projection}"
        )
        print(
            "Therefore the degree-8 memory cannot simply be "
            "componentwise-squared and reused as an operation word."
        )

    print(
        "The degree, word length, reset, and leading ladder are now "
        "recursive and independent of primality. Only the next "
        "projection rule remains unresolved."
    )


if __name__ == "__main__":
    main()
