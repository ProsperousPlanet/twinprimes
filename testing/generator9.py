#!/usr/bin/env python3
"""
Reflected Golden-Silver Centre Constructor

This file implements one concrete interpretation of the observation

    reflection round 6 -> 2^6 = 64 symbols

together with the idea that Golden and Silver are complementary
reflections of the same recursive process.

Reflection rule
---------------

    G -> GS
    S -> SG

Starting from G:

    round 0: G
    round 1: GS
    round 2: GSSG
    round 3: GSSGSGGS
    ...

After r reflection rounds, the deterministic path has 2^r symbols.

The reflected companion path swaps every G and S:

    G <-> S

Centre construction
-------------------

The counter state begins with:

    previous = 2
    current  = 3
    centre   = 6

For each path symbol:

    G: next_period = previous + current
    S: next_period = previous + 2 * current

Then:

    centre = centre * next_period

No primality test is used.
No blocked addresses are stored.
No left/right boundary state is stored.
No binary branch tree is searched.

The program constructs one deterministic reflected path and, optionally,
its complementary reflected path.

Important
---------
This is an experimental centre constructor. Until the reflection rule is
proved to preserve twin primality, its outputs must be called generated
or candidate centres rather than automatically proven twin-prime centres.
Independent validation can be performed separately.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from time import perf_counter


# Allow printing integers with more than Python's default digit limit.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


# ============================================================
# CONFIGURATION
# ============================================================

# Six rounds produce one path containing 2^6 = 64 symbols.
REFLECTION_ROUNDS = 6

# "G" gives the primary reflected path.
# "S" gives its exact G/S complement.
START_SYMBOL = "G"

# Generate both the primary path and its reflected companion.
GENERATE_COMPANION = True

# Print the complete G/S path.
PRINT_PATH = True

# Print complete centres only while they remain reasonably readable.
# Larger values are summarized by their first and last digits.
FULL_NUMBER_DIGIT_LIMIT = 1_000

# Number of leading and trailing digits shown for very large centres.
NUMBER_PREVIEW_DIGITS = 60


# ============================================================
# DATA
# ============================================================

@dataclass(slots=True)
class ConstructionResult:
    label: str
    path_length: int
    golden_steps: int
    silver_steps: int
    previous_period: int
    current_period: int
    centre: int
    elapsed: float
    checkpoints: list[tuple[int, int, int, int]]


# ============================================================
# REFLECTION PATH
# ============================================================

def reflected_symbol(
    index: int,
    start_symbol: str,
) -> str:
    """
    Return the symbol at zero-based position `index`.

    The parity of the number of 1-bits in `index` generates the same
    infinite word as repeatedly applying:

        G -> GS
        S -> SG

    Even bit parity keeps the starting symbol.
    Odd bit parity reflects it.
    """
    reflected = index.bit_count() & 1

    if start_symbol == "G":
        return "S" if reflected else "G"

    return "G" if reflected else "S"


def reflected_path(
    rounds: int,
    start_symbol: str,
) -> str:
    """Build the visible path for printing or inspection."""
    length = 1 << rounds

    return "".join(
        reflected_symbol(
            index,
            start_symbol,
        )
        for index in range(length)
    )


# ============================================================
# CENTRE CONSTRUCTION
# ============================================================

def construct_centre(
    rounds: int,
    start_symbol: str,
    label: str,
) -> ConstructionResult:
    """
    Follow one deterministic reflected path.

    Only the current counter pair and centre are retained.
    """
    total_steps = 1 << rounds

    previous = 2
    current = 3
    centre = 6

    golden_steps = 0
    silver_steps = 0
    checkpoints: list[tuple[int, int, int, int]] = []

    next_checkpoint = 1

    start = perf_counter()

    for index in range(total_steps):
        symbol = reflected_symbol(
            index,
            start_symbol,
        )

        if symbol == "G":
            next_period = previous + current
            golden_steps += 1
        else:
            next_period = previous + 2 * current
            silver_steps += 1

        previous, current = current, next_period
        centre *= next_period

        completed_steps = index + 1

        # Powers of two are completed reflection levels.
        if completed_steps == next_checkpoint:
            checkpoints.append(
                (
                    completed_steps,
                    previous,
                    current,
                    len(str(centre)),
                )
            )
            next_checkpoint <<= 1

    elapsed = perf_counter() - start

    return ConstructionResult(
        label=label,
        path_length=total_steps,
        golden_steps=golden_steps,
        silver_steps=silver_steps,
        previous_period=previous,
        current_period=current,
        centre=centre,
        elapsed=elapsed,
        checkpoints=checkpoints,
    )


# ============================================================
# OUTPUT HELPERS
# ============================================================

def number_preview(
    number: int,
) -> str:
    text = str(number)
    digits = len(text)

    if digits <= FULL_NUMBER_DIGIT_LIMIT:
        return f"{number:,}"

    width = NUMBER_PREVIEW_DIGITS

    return (
        f"{text[:width]} ... {text[-width:]}"
        f"  [{digits:,} digits]"
    )


def print_result(
    result: ConstructionResult,
    path: str,
) -> None:
    print("\n" + "=" * 80)
    print(result.label)
    print("=" * 80)

    print(
        f"Path length:       "
        f"{result.path_length:,}"
    )
    print(
        f"Golden steps:      "
        f"{result.golden_steps:,}"
    )
    print(
        f"Silver steps:      "
        f"{result.silver_steps:,}"
    )

    if PRINT_PATH:
        print(f"Path:              {path}")

    print("\nCompleted reflection checkpoints:")
    print("  steps | previous period | current period | centre digits")

    for (
        steps,
        previous,
        current,
        centre_digits,
    ) in result.checkpoints:
        print(
            f"  {steps:>5,} | "
            f"{previous:>15,} | "
            f"{current:>14,} | "
            f"{centre_digits:>13,}"
        )

    print(
        f"\nFinal previous period: "
        f"{result.previous_period:,}"
    )
    print(
        f"Final current period:  "
        f"{result.current_period:,}"
    )
    print(
        f"Final centre digits:   "
        f"{len(str(result.centre)):,}"
    )
    print(
        f"Generated centre:      "
        f"{number_preview(result.centre)}"
    )
    print(
        f"Generated structure:   "
        f"{number_preview(result.centre - 1)}"
    )
    print(
        f"                       "
        f"{number_preview(result.centre)}"
    )
    print(
        f"                       "
        f"{number_preview(result.centre + 1)}"
    )
    print(
        f"Construction time:     "
        f"{result.elapsed:.6f} seconds"
    )


# ============================================================
# MAIN
# ============================================================

def main() -> None:
    if REFLECTION_ROUNDS < 0:
        raise ValueError(
            "REFLECTION_ROUNDS must be non-negative"
        )

    if START_SYMBOL not in {"G", "S"}:
        raise ValueError(
            'START_SYMBOL must be "G" or "S"'
        )

    path_length = 1 << REFLECTION_ROUNDS

    print("=" * 80)
    print("REFLECTED GOLDEN-SILVER CENTRE CONSTRUCTOR")
    print("=" * 80)
    print(
        f"Reflection rounds: "
        f"{REFLECTION_ROUNDS}"
    )
    print(
        f"Path length:       "
        f"2^{REFLECTION_ROUNDS} = {path_length:,}"
    )
    print(
        "Rule:              "
        "G -> GS, S -> SG"
    )
    print(
        "Prime validation:  "
        "none"
    )
    print(
        "Branch search:      "
        "none"
    )

    primary_path = reflected_path(
        REFLECTION_ROUNDS,
        START_SYMBOL,
    )

    primary = construct_centre(
        REFLECTION_ROUNDS,
        START_SYMBOL,
        "PRIMARY REFLECTION PATH",
    )

    print_result(
        primary,
        primary_path,
    )

    if GENERATE_COMPANION:
        companion_start = (
            "S"
            if START_SYMBOL == "G"
            else "G"
        )

        companion_path = reflected_path(
            REFLECTION_ROUNDS,
            companion_start,
        )

        companion = construct_centre(
            REFLECTION_ROUNDS,
            companion_start,
            "COMPLEMENTARY REFLECTION PATH",
        )

        print_result(
            companion,
            companion_path,
        )

        print("\n" + "=" * 80)
        print("REFLECTION SUMMARY")
        print("=" * 80)
        print(
            "The two paths have identical lengths and exchange "
            "G with S at every position."
        )
        print(
            f"Primary centre digits:   "
            f"{len(str(primary.centre)):,}"
        )
        print(
            f"Companion centre digits: "
            f"{len(str(companion.centre)):,}"
        )

    print(
        "\nThese are recursively generated candidate centres. "
        "The file intentionally makes no primality claim."
    )


if __name__ == "__main__":
    main()
