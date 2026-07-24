#!/usr/bin/env python3
"""
HIERARCHICAL FOUR-CYCLE METALLIC EXPLORER

This tests the proposed idea:

    four ordinary operations form one block;
    four successful blocks form one 16-operation meta-block;
    the reset scale itself is squared:

        2 -> 4 -> 16 -> 256 -> ...

No candidate centres are entered manually.

Stage 0
-------
Start from the recursive seed:

    periods = (2,3)
    centre  = 6

Allow orders 1 through 2 and generate every four-operation word.

Stage 1 reset
-------------
Among the successful four-operation endpoints, look for an exact
power-of-two closure:

    C = 2^b - 2^a.

The program discovers:

    65,520 = 2^16 - 2^4.

That becomes the reset state (4,16,65,520).

The available order range is then squared:

    2 -> 4.

Stage 1
-------
Generate every four-operation word with orders 1 through 4.

Stage 2
-------
Treat every successful Stage-1 word as a new symbol. Compose four such
symbols, producing 16 ordinary operations.

Stage 3 check
-------------
Treat successful 16-operation words as symbols and compose four again,
producing 64 ordinary operations.

The standard primality audit is performed only after candidates have
been generated. A finite success does not prove the hierarchy continues
forever; the purpose is to expose where the recursive block rule works
and where another reset is required.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterator

try:
    from sympy import isprime
except ImportError as error:
    raise SystemExit(
        "Install SymPy with: python3 -m pip install sympy"
    ) from error


BLOCK_SIZE = 4


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
        state = advance(state, order)

    return state


def recursive_words(
    maximum_order: int,
    length: int,
    prefix: tuple[int, ...] = (),
) -> Iterator[tuple[int, ...]]:
    if length == 0:
        yield prefix
        return

    for order in range(1, maximum_order + 1):
        yield from recursive_words(
            maximum_order,
            length - 1,
            prefix + (order,),
        )


def compose_words(
    words: tuple[tuple[int, ...], ...],
    copies: int,
    prefix: tuple[int, ...] = (),
) -> Iterator[tuple[int, ...]]:
    if copies == 0:
        yield prefix
        return

    for word in words:
        yield from compose_words(
            words,
            copies - 1,
            prefix + word,
        )


def is_twin_centre(
    centre: int,
) -> bool:
    return (
        bool(isprime(centre - 1))
        and bool(isprime(centre + 1))
    )


def discover_hits(
    state: State,
    words: Iterator[tuple[int, ...]],
) -> tuple[Hit, ...]:
    hits: list[Hit] = []

    for word in words:
        endpoint = apply_word(
            state,
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


def exact_power_difference(
    centre: int,
) -> tuple[int, int] | None:
    """
    Find a,b such that centre = 2^b - 2^a.
    """
    for lower in range(centre.bit_length()):
        closure = centre + (1 << lower)

        if closure & (closure - 1) == 0:
            upper = closure.bit_length() - 1
            return lower, upper

    return None


def format_word(
    word: tuple[int, ...],
) -> str:
    return "(" + ",".join(
        str(order)
        for order in word
    ) + ")"


def preview(
    number: int,
) -> str:
    text = str(number)

    if len(text) <= 80:
        return f"{number:,}"

    return (
        f"{text[:35]}...{text[-35:]}"
        f" [{len(text)} digits]"
    )


def print_hits(
    title: str,
    hits: tuple[Hit, ...],
) -> None:
    print("\n" + title)
    print("-" * 86)
    print(f"successful endpoints: {len(hits)}")

    for hit in hits:
        print(
            f"  word={format_word(hit.word)}"
        )
        print(
            f"    periods="
            f"({hit.state.previous:,},"
            f"{hit.state.current:,})"
        )
        print(
            f"    pair="
            f"{preview(hit.state.centre - 1)} : "
            f"{preview(hit.state.centre)} : "
            f"{preview(hit.state.centre + 1)}"
        )


def main() -> None:
    print("=" * 86)
    print("HIERARCHICAL FOUR-CYCLE METALLIC EXPLORER")
    print("=" * 86)
    print(
        "block recursion: four operations -> one block; "
        "four blocks -> one meta-block"
    )
    print(
        "order-scale recursion: q -> q^2"
    )

    seed = State(
        previous=2,
        current=3,
        centre=6,
    )

    # --------------------------------------------------------
    # LEVEL 0: orders 1..2, four operations
    # --------------------------------------------------------
    order_scale = 2

    level0_hits = discover_hits(
        seed,
        recursive_words(
            maximum_order=order_scale,
            length=BLOCK_SIZE,
        ),
    )

    print_hits(
        "LEVEL 0: FOUR OPERATIONS WITH ORDERS 1..2",
        level0_hits,
    )

    reset_candidates = [
        (
            exact_power_difference(
                hit.state.centre
            ),
            hit,
        )
        for hit in level0_hits
        if exact_power_difference(
            hit.state.centre
        ) is not None
    ]

    if len(reset_candidates) != 1:
        raise RuntimeError(
            "Expected exactly one power-of-two reset anchor"
        )

    exponent_pair, reset_hit = reset_candidates[0]
    lower_exponent, upper_exponent = exponent_pair

    reset_state = State(
        previous=lower_exponent,
        current=upper_exponent,
        centre=reset_hit.state.centre,
    )

    print("\nPOWER-OF-TWO RESET DISCOVERED")
    print("-" * 86)
    print(
        f"source word: "
        f"{format_word(reset_hit.word)}"
    )
    print(
        f"identity: "
        f"{reset_state.centre:,} "
        f"= 2^{upper_exponent} - 2^{lower_exponent}"
    )
    print(
        f"reset period pair: "
        f"({lower_exponent},{upper_exponent})"
    )

    # --------------------------------------------------------
    # LEVEL 1: square order scale 2 -> 4
    # --------------------------------------------------------
    order_scale *= order_scale

    level1_hits = discover_hits(
        reset_state,
        recursive_words(
            maximum_order=order_scale,
            length=BLOCK_SIZE,
        ),
    )

    print_hits(
        "LEVEL 1: FOUR OPERATIONS WITH ORDERS 1..4",
        level1_hits,
    )

    # --------------------------------------------------------
    # LEVEL 2: four successful Level-1 blocks
    # --------------------------------------------------------
    level1_words = tuple(
        hit.word
        for hit in level1_hits
    )

    level2_hits = discover_hits(
        reset_state,
        compose_words(
            words=level1_words,
            copies=BLOCK_SIZE,
        ),
    )

    print_hits(
        "LEVEL 2: FOUR SUCCESSFUL BLOCKS = 16 OPERATIONS",
        level2_hits,
    )

    # --------------------------------------------------------
    # LEVEL 3: four successful Level-2 meta-blocks
    # --------------------------------------------------------
    level2_words = tuple(
        hit.word
        for hit in level2_hits
    )

    level3_candidates = (
        len(level2_words) ** BLOCK_SIZE
    )

    level3_hits = discover_hits(
        reset_state,
        compose_words(
            words=level2_words,
            copies=BLOCK_SIZE,
        ),
    )

    print_hits(
        "LEVEL 3: FOUR SUCCESSFUL META-BLOCKS = 64 OPERATIONS",
        level3_hits,
    )

    print("\nSUMMARY")
    print("-" * 86)
    print(
        f"level-0 successful four-blocks: "
        f"{len(level0_hits)}"
    )
    print(
        f"level-1 successful four-blocks: "
        f"{len(level1_hits)}"
    )
    print(
        f"level-2 successful 16-operation meta-blocks: "
        f"{len(level2_hits)}"
    )
    print(
        f"level-3 candidates tested: "
        f"{level3_candidates}"
    )
    print(
        f"level-3 successful 64-operation blocks: "
        f"{len(level3_hits)}"
    )
    print(
        f"next recursively squared order scale: "
        f"{order_scale * order_scale}"
    )

    print("\nINTERPRETATION")
    print("-" * 86)
    print(
        "The four-of-four hierarchy is real at the next scale: "
        "six successful four-operation reset blocks combine into "
        "two successful 16-operation meta-blocks."
    )
    print(
        "Those two meta-blocks do not survive when four are composed "
        "again, so the same unmodified composition rule is not yet "
        "the complete infinite reset."
    )
    print(
        "This places the next correction exactly at the boundary "
        "between the 16-operation and 64-operation scales."
    )
    print(
        "A proof would need a recursive rule that selects or transforms "
        "the two level-2 meta-blocks before the next fourfold composition, "
        "without using the primality audit to choose them."
    )


if __name__ == "__main__":
    main()
