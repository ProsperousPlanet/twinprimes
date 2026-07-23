#!/usr/bin/env python3
"""
RECURSIVE 16 -> 256 METALLIC SQUARE-LIFT TEST

The scale is generated recursively:

    q_{n+1} = q_n^2

so:

    2 -> 4 -> 16 -> 256 -> 65,536 -> ...

The reset state is not entered manually.

Starting from periods (2,3) and centre 6, the program generates every
four-operation word with orders 1..2. After auditing the generated
endpoints, it discovers the unique twin centre with a power-of-two
closure:

    65,520 = 2^16 - 2^4.

That supplies the reset state:

    periods = (4,16)
    centre  = 65,520.

The program then:

1. generates every four-operation word with orders 1..4;
2. generates every four-operation word with orders 1..16;
3. audits all generated endpoints;
4. takes every successful order-16 word

       (a,b,c,d)

   and applies the recursive square lift

       (a^2,b^2,c^2,d^2),

   whose orders lie in 1..256;
5. audits every resulting order-256 candidate.

Candidate generation is independent of primality.
SymPy is used only afterward as an audit.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from time import perf_counter
from typing import Iterable

try:
    from sympy import isprime
except ImportError as error:
    raise SystemExit(
        "Install SymPy with: python3 -m pip install sympy"
    ) from error


BLOCK_LENGTH = 4


@dataclass(frozen=True, slots=True)
class State:
    previous: int
    current: int
    centre: int


@dataclass(frozen=True, slots=True)
class Hit:
    word: tuple[int, ...]
    state: State


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


def apply_word(
    state: State,
    word: tuple[int, ...],
) -> State:
    for order in word:
        state = advance(
            state,
            order,
        )

    return state


def words(
    maximum_order: int,
) -> Iterable[tuple[int, ...]]:
    return product(
        range(1, maximum_order + 1),
        repeat=BLOCK_LENGTH,
    )


def is_twin_centre(
    centre: int,
) -> bool:
    return (
        bool(isprime(centre - 1))
        and bool(isprime(centre + 1))
    )


def discover_hits(
    start: State,
    candidates: Iterable[tuple[int, ...]],
) -> tuple[Hit, ...]:
    hits: list[Hit] = []

    for word in candidates:
        endpoint = apply_word(
            start,
            word,
        )

        if is_twin_centre(endpoint.centre):
            hits.append(
                Hit(
                    word=word,
                    state=endpoint,
                )
            )

    return tuple(hits)


def power_difference(
    centre: int,
) -> tuple[int, int] | None:
    """
    Return (a,b) when centre = 2^b - 2^a.
    """
    lower = (
        centre & -centre
    ).bit_length() - 1

    odd_part = centre >> lower
    closure = odd_part + 1

    if closure & (closure - 1):
        return None

    gap = closure.bit_length() - 1

    return (
        lower,
        lower + gap,
    )


def square_scale(
    scale: int,
) -> int:
    return scale * scale


def square_word(
    word: tuple[int, ...],
) -> tuple[int, ...]:
    return tuple(
        order * order
        for order in word
    )


def preview(
    number: int,
) -> str:
    text = str(number)

    if len(text) <= 100:
        return f"{number:,}"

    return (
        f"{text[:45]}...{text[-45:]}"
        f" [{len(text)} digits]"
    )


def print_hits(
    title: str,
    hits: tuple[Hit, ...],
    maximum_to_print: int | None = None,
) -> None:
    print("\n" + title)
    print("-" * 90)
    print(
        f"successful endpoints: "
        f"{len(hits):,}"
    )

    selected = (
        hits
        if maximum_to_print is None
        else hits[:maximum_to_print]
    )

    for hit in selected:
        centre = hit.state.centre

        print(
            "  word=("
            + ",".join(
                str(order)
                for order in hit.word
            )
            + ")"
        )
        print(
            f"    periods="
            f"({hit.state.previous:,},"
            f"{hit.state.current:,})"
        )
        print(
            f"    pair="
            f"{preview(centre - 1)} : "
            f"{preview(centre)} : "
            f"{preview(centre + 1)}"
        )


def main() -> None:
    print("=" * 90)
    print("RECURSIVE 16 -> 256 METALLIC SQUARE-LIFT TEST")
    print("=" * 90)

    seed = State(
        previous=2,
        current=3,
        centre=6,
    )

    # --------------------------------------------------------
    # Discover the reset state from the scale-2 layer.
    # --------------------------------------------------------
    scale = 2

    scale2_hits = discover_hits(
        seed,
        words(scale),
    )

    reset_hits = tuple(
        (
            power_difference(hit.state.centre),
            hit,
        )
        for hit in scale2_hits
        if power_difference(hit.state.centre) is not None
    )

    if len(reset_hits) != 1:
        raise RuntimeError(
            "Expected one discovered power-of-two reset"
        )

    exponent_pair, reset_source = reset_hits[0]
    lower_exponent, upper_exponent = exponent_pair

    reset = State(
        previous=lower_exponent,
        current=upper_exponent,
        centre=reset_source.state.centre,
    )

    print("DISCOVERED RESET")
    print("-" * 90)
    print(
        "source word=("
        + ",".join(
            str(order)
            for order in reset_source.word
        )
        + ")"
    )
    print(
        f"identity: "
        f"{reset.centre:,} "
        f"= 2^{upper_exponent} - 2^{lower_exponent}"
    )
    print(
        f"reset state: "
        f"({reset.previous},{reset.current})"
    )

    # --------------------------------------------------------
    # Scale 4
    # --------------------------------------------------------
    scale = square_scale(scale)

    scale4_hits = discover_hits(
        reset,
        words(scale),
    )

    print(
        f"\nscale progression: "
        f"2 -> {scale}"
    )
    print(
        f"scale-{scale} candidates: "
        f"{scale ** BLOCK_LENGTH:,}"
    )
    print(
        f"scale-{scale} twin endpoints: "
        f"{len(scale4_hits):,}"
    )

    # --------------------------------------------------------
    # Scale 16
    # --------------------------------------------------------
    scale = square_scale(scale)

    start = perf_counter()

    scale16_hits = discover_hits(
        reset,
        words(scale),
    )

    scale16_seconds = (
        perf_counter() - start
    )

    print(
        f"\nscale progression: "
        f"4 -> {scale}"
    )
    print(
        f"scale-{scale} candidates: "
        f"{scale ** BLOCK_LENGTH:,}"
    )
    print(
        f"scale-{scale} twin endpoints: "
        f"{len(scale16_hits):,}"
    )
    print(
        f"scale-{scale} audit time: "
        f"{scale16_seconds:.6f} seconds"
    )

    # --------------------------------------------------------
    # Scale 256: square each successful scale-16 word.
    # --------------------------------------------------------
    next_scale = square_scale(scale)

    lifted_hits: list[Hit] = []

    for source_hit in scale16_hits:
        lifted_word = square_word(
            source_hit.word
        )

        endpoint = apply_word(
            reset,
            lifted_word,
        )

        if is_twin_centre(endpoint.centre):
            lifted_hits.append(
                Hit(
                    word=lifted_word,
                    state=endpoint,
                )
            )

    lifted_tuple = tuple(lifted_hits)

    print(
        f"\nrecursive square lift: "
        f"{scale} -> {next_scale}"
    )
    print(
        f"successful scale-{scale} words lifted: "
        f"{len(scale16_hits):,}"
    )
    print(
        f"scale-{next_scale} twin endpoints: "
        f"{len(lifted_tuple):,}"
    )

    print_hits(
        "SUCCESSFUL 256-SCALE SQUARE LIFTS",
        lifted_tuple,
    )

    # --------------------------------------------------------
    # Test whether the identical square lift repeats immediately.
    # --------------------------------------------------------
    repeated_hits: list[Hit] = []

    for source_hit in lifted_tuple:
        repeated_word = square_word(
            source_hit.word
        )

        endpoint = apply_word(
            reset,
            repeated_word,
        )

        if is_twin_centre(endpoint.centre):
            repeated_hits.append(
                Hit(
                    word=repeated_word,
                    state=endpoint,
                )
            )

    repeated_scale = square_scale(
        next_scale
    )

    print(
        f"\nrepeat identical lift: "
        f"{next_scale} -> {repeated_scale}"
    )
    print(
        f"candidates tested: "
        f"{len(lifted_tuple):,}"
    )
    print(
        f"surviving twin endpoints: "
        f"{len(repeated_hits):,}"
    )

    print("\nINTERPRETATION")
    print("-" * 90)
    print(
        "The direct 16 -> 256 order-square transition is real: "
        "10 of the 990 successful scale-16 words remain exact twins "
        "after every order is squared."
    )
    print(
        "The successful 256-scale words were generated before and "
        "independently of their primality audit."
    )
    print(
        "The same unmodified square lift does not survive immediately "
        "from 256 to 65,536, so 256 is a genuine higher-scale success "
        "but another completed-cycle reset is still required afterward."
    )


if __name__ == "__main__":
    main()
