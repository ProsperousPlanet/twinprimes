#!/usr/bin/env python3
"""
Metallic-Ratio Hierarchy Test

This program tests the hypothesis that the metallic orders themselves
repeat the original 2, 3 -> 5 recursive structure.

Metallic actions
----------------
For a counter state (a, b), define the metallic action of order m by

    next_period = a + m*b

The familiar names are

    m = 1  Gold
    m = 2  Silver
    m = 3  Bronze

The metallic orders 2 and 3 can themselves be combined by the golden
addition rule:

    2, 3, 5, 8, 13, 21, ...

This is a real self-similarity: the indices of the metallic recurrences
reproduce the same Fibonacci-type sequence as the original periods.

The program tests four questions:

1. Does applying the higher metallic orders directly from the seed
   produce twin-prime centres?

2. Does applying the metallic orders sequentially produce a singular
   always-successful path?

3. Is Bronze exactly equivalent to combining Silver and Gold?

4. Do successful G/S paths contain the exact Silver-then-Gold macro
   that reaches the same terminal period as Bronze?

Validation
----------
The recursive construction and validation are separated. Deterministic
Miller-Rabin is used only as an independent checker below 2^64.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from time import perf_counter


# ============================================================
# CONFIGURATION
# ============================================================

MAX_TREE_DEPTH = 10
METALLIC_TERMS = 10
UINT64_LIMIT = 1 << 64

PRINT_SUCCESSFUL_PATHS = True


# ============================================================
# EXACT 64-BIT PRIMALITY CHECK
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
    """Return an exact prime/composite result for number < 2^64."""
    if number < 2:
        return False

    for prime in _SMALL_PRIMES:
        if number % prime == 0:
            return number == prime

    odd_part = number - 1
    power_of_two = 0

    while odd_part % 2 == 0:
        odd_part //= 2
        power_of_two += 1

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

        for _ in range(power_of_two - 1):
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


def twin_status(centre: int) -> str:
    """
    Return TWIN, BLOCKED, or ABOVE-64-BIT.

    The generator itself does not depend on this function.
    """
    if centre + 1 >= UINT64_LIMIT:
        return "ABOVE-64-BIT"

    if (
        is_prime_64(centre - 1)
        and is_prime_64(centre + 1)
    ):
        return "TWIN"

    return "BLOCKED"


# ============================================================
# RECURSIVE CENTRE STATE
# ============================================================

@dataclass(frozen=True, slots=True)
class State:
    previous: int
    current: int
    centre: int


def metallic_step(
    state: State,
    order: int,
) -> State:
    """Apply one metallic recurrence of integer order m."""
    next_period = (
        state.previous
        + order * state.current
    )

    return State(
        previous=state.current,
        current=next_period,
        centre=state.centre * next_period,
    )


def apply_gs_word(word: str) -> State:
    """Apply a word using G=1 and S=2."""
    state = State(
        previous=2,
        current=3,
        centre=6,
    )

    for symbol in word:
        order = 1 if symbol == "G" else 2
        state = metallic_step(
            state,
            order,
        )

    return state


# ============================================================
# METALLIC ORDER SEQUENCE
# ============================================================

def metallic_orders(count: int) -> list[int]:
    """
    Produce

        1, 2, 3, 5, 8, 13, ...

    The first term is Gold. Silver and Bronze then seed the repeated
    golden addition rule 2 + 3 = 5.
    """
    if count <= 0:
        return []

    sequence = [1]

    if count == 1:
        return sequence

    sequence.extend([2, 3])

    while len(sequence) < count:
        sequence.append(
            sequence[-2] + sequence[-1]
        )

    return sequence[:count]


def metallic_name(order: int) -> str:
    return {
        1: "Gold",
        2: "Silver",
        3: "Bronze",
    }.get(
        order,
        f"Metallic-{order}",
    )


# ============================================================
# BRONZE AS A COMPRESSED ENDPOINT
# ============================================================

def bronze_comparison() -> None:
    """
    Show the exact relation between one Bronze action and the word SG.

    Starting from (a,b):

        Bronze:
            (b, a+3b)

        Silver then Gold:
            (a+2b, a+3b)

    They share the same final current period, but not the same previous
    period or centre product.
    """
    root = State(
        previous=2,
        current=3,
        centre=6,
    )

    bronze = metallic_step(
        root,
        3,
    )

    silver = metallic_step(
        root,
        2,
    )
    silver_gold = metallic_step(
        silver,
        1,
    )

    print("\n" + "=" * 78)
    print("BRONZE VERSUS THE EXACT SILVER-GOLD MACRO")
    print("=" * 78)

    print(
        "One Bronze step: "
        f"state=({bronze.previous}, {bronze.current}), "
        f"centre={bronze.centre:,}, "
        f"status={twin_status(bronze.centre)}"
    )

    print(
        "Silver then Gold: "
        f"state=({silver_gold.previous}, "
        f"{silver_gold.current}), "
        f"centre={silver_gold.centre:,}, "
        f"status={twin_status(silver_gold.centre)}"
    )

    print(
        "\nBoth finish with current period "
        f"{bronze.current}, because 3 = 2 + 1."
    )
    print(
        "They are not the same full construction: SG retains the "
        "intermediate period and multiplies it into the centre."
    )


# ============================================================
# HIGHER METALLIC ORDER TESTS
# ============================================================

def direct_from_root_test(
    orders: list[int],
) -> None:
    """
    Apply each metallic order independently to the original seed.
    """
    root = State(
        previous=2,
        current=3,
        centre=6,
    )

    print("\n" + "=" * 78)
    print("EACH METALLIC ORDER APPLIED DIRECTLY TO THE SEED")
    print("=" * 78)
    print(
        "order | name          | next period | centre | result"
    )

    for order in orders:
        state = metallic_step(
            root,
            order,
        )

        print(
            f"{order:>5} | "
            f"{metallic_name(order):<13} | "
            f"{state.current:>11,} | "
            f"{state.centre:>6,} | "
            f"{twin_status(state.centre)}"
        )


def sequential_metallic_test(
    orders: list[int],
) -> None:
    """
    Apply 1,2,3,5,8,... as one singular path.
    """
    state = State(
        previous=2,
        current=3,
        centre=6,
    )

    print("\n" + "=" * 78)
    print("SINGULAR PATH USING METALLIC ORDERS 1,2,3,5,8,...")
    print("=" * 78)
    print(
        "step | order | next period | centre | result"
    )

    for step_number, order in enumerate(
        orders,
        start=1,
    ):
        state = metallic_step(
            state,
            order,
        )

        status = twin_status(
            state.centre
        )

        print(
            f"{step_number:>4} | "
            f"{order:>5} | "
            f"{state.current:>11,} | "
            f"{state.centre:>22,} | "
            f"{status}"
        )

        if status == "ABOVE-64-BIT":
            break


# ============================================================
# EXACT MACRO-WORD HIERARCHY
# ============================================================

def fibonacci_macro_words(
    count: int,
) -> list[tuple[int, str]]:
    """
    Treat Silver as the order-2 word S and exact Bronze as SG.

    Then combine complete words by the same index rule:

        W_5 = W_2 W_3
        W_8 = W_3 W_5
        ...

    This retains every underlying G/S action.
    """
    if count <= 0:
        return []

    indexed_words = [
        (2, "S"),
        (3, "SG"),
    ]

    while len(indexed_words) < count:
        previous_index, previous_word = indexed_words[-2]
        current_index, current_word = indexed_words[-1]

        indexed_words.append(
            (
                previous_index + current_index,
                previous_word + current_word,
            )
        )

    return indexed_words[:count]


def macro_word_test() -> None:
    words = fibonacci_macro_words(8)

    print("\n" + "=" * 78)
    print("EXACT METALLIC MACRO WORDS")
    print("=" * 78)
    print(
        "index | expanded G/S word               | centre | result"
    )

    for index, word in words:
        state = apply_gs_word(
            word
        )

        shown_word = (
            word
            if len(word) <= 30
            else word[:27] + "..."
        )

        print(
            f"{index:>5} | "
            f"{shown_word:<31} | "
            f"{state.centre:>16,} | "
            f"{twin_status(state.centre)}"
        )


# ============================================================
# BRONZE-EVENT ANALYSIS OF THE ORIGINAL G/S TREE
# ============================================================

@dataclass(slots=True)
class DepthStats:
    tested: int = 0
    twin_hits: int = 0
    hits_with_sg: int = 0
    hits_without_sg: int = 0
    by_sg_count: dict[int, int] | None = None


def count_sg_macros(path: str) -> int:
    """
    Count overlapping SG transitions.

    SG is the exact two-step path that reaches the same terminal current
    period as one Bronze step.
    """
    return sum(
        1
        for index in range(len(path) - 1)
        if path[index:index + 2] == "SG"
    )


def compress_sg_as_bronze(path: str) -> str:
    """
    Read every non-overlapping SG as B*.

    B* means the exact SG macro, not the lossy one-step Bronze action.
    """
    output: list[str] = []
    index = 0

    while index < len(path):
        if path.startswith(
            "SG",
            index,
        ):
            output.append("B")
            index += 2
        else:
            output.append(
                path[index]
            )
            index += 1

    return "".join(output)


def analyse_original_tree() -> None:
    print("\n" + "=" * 78)
    print("BRONZE-LIKE SG EVENTS IN THE ORIGINAL G/S TREE")
    print("=" * 78)
    print(
        "depth | exact candidates | twin hits | "
        "hits containing SG | hits without SG"
    )

    all_later_hits_have_sg = True
    successful_paths: list[
        tuple[int, str, str, int]
    ] = []

    for depth in range(
        MAX_TREE_DEPTH + 1
    ):
        stats = DepthStats(
            by_sg_count=defaultdict(int)
        )

        for symbols in product(
            "GS",
            repeat=depth,
        ):
            path = "".join(symbols)
            state = apply_gs_word(
                path
            )

            if state.centre + 1 >= UINT64_LIMIT:
                continue

            stats.tested += 1

            if twin_status(
                state.centre
            ) != "TWIN":
                continue

            stats.twin_hits += 1
            sg_count = count_sg_macros(
                path
            )
            stats.by_sg_count[sg_count] += 1

            if sg_count:
                stats.hits_with_sg += 1
            else:
                stats.hits_without_sg += 1

            if depth > 4 and sg_count == 0:
                all_later_hits_have_sg = False

            successful_paths.append(
                (
                    depth,
                    path or "ROOT",
                    compress_sg_as_bronze(path) or "ROOT",
                    state.centre,
                )
            )

        print(
            f"{depth:>5} | "
            f"{stats.tested:>16,} | "
            f"{stats.twin_hits:>9,} | "
            f"{stats.hits_with_sg:>18,} | "
            f"{stats.hits_without_sg:>15,}"
        )

        if stats.twin_hits:
            distribution = ", ".join(
                f"{count} SG -> {hits}"
                for count, hits in sorted(
                    stats.by_sg_count.items()
                )
            )
            print(
                f"      SG-count distribution: "
                f"{distribution}"
            )

    print()
    print(
        "All exact twin hits after depth 4 contained at least "
        f"one SG event: {all_later_hits_have_sg}"
    )

    if PRINT_SUCCESSFUL_PATHS:
        print(
            "\nSuccessful paths rewritten with exact SG macros:"
        )

        for (
            depth,
            path,
            compressed,
            centre,
        ) in successful_paths:
            if depth <= 4:
                continue

            print(
                f"  depth={depth:>2} "
                f"path={path:<12} "
                f"macro={compressed:<10} "
                f"centre={centre:,}"
            )


# ============================================================
# MAIN
# ============================================================

def main() -> None:
    start = perf_counter()

    orders = metallic_orders(
        METALLIC_TERMS
    )

    print("=" * 78)
    print("METALLIC-RATIO HIERARCHY TEST")
    print("=" * 78)
    print(
        "Metallic orders: "
        + ", ".join(
            str(order)
            for order in orders
        )
    )
    print(
        "The sequence begins 1,2,3,5,8,... because "
        "Silver 2 and Bronze 3 restart the golden addition rule."
    )

    bronze_comparison()
    direct_from_root_test(
        orders
    )
    sequential_metallic_test(
        orders
    )
    macro_word_test()
    analyse_original_tree()

    elapsed = perf_counter() - start

    print(
        f"\nTotal runtime: "
        f"{elapsed:.6f} seconds"
    )


if __name__ == "__main__":
    main()
