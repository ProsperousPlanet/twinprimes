#!/usr/bin/env python3
"""
Recursive Crossover Prime and Twin-Prime Generator
===================================================

This program implements the construction described in the companion paper.

It does not call a primality-testing function and it does not begin with a
stored list of primes.

Prime generation
----------------
Each generated prime p opens an additive crossover row

    2p, 3p, 4p, ...

Only the next landing of each open row is stored. When a row lands on x, x is
closed as composite and that row schedules its next landing at x + p. If no
open row lands on x, then x is prime and opens a new row beginning at 2x.

Twin-prime generation
---------------------
Apart from the initial pair (3, 5), possible twin-prime pairs have a centre 6m
and boundaries

    6m - 1, 6m + 1.

The program therefore does not search for consecutive primes whose difference
is two. It follows the two-sided centre construction directly:

1. At a left boundary 6m - 1, remember whether the position remained open.
2. At the matching right boundary 6m + 1, certify the centre only when both
   boundaries remained open.

Recursion in Python
-------------------
The mathematical state is recursive: the completed state at x becomes the
input state at x + 1. CPython does not optimize tail recursion, so a direct
call for every integer would normally fail near the interpreter's recursion
limit. This program uses a trampoline: count() returns the next recursive
state, and the trampoline feeds that state back into count() without adding a
Python call-stack frame. The arithmetic rule remains recursive while the
practical range is limited only by available time and memory.

Suggested first runs
--------------------
    python3 recursive_twin_primes.py 100000 --trace 40
    python3 recursive_twin_primes.py 1000000
    python3 recursive_twin_primes.py 10000000 --no-blocks

The clarity-first version is usually comfortable through 1,000,000 on an
ordinary modern computer. Ten million is feasible on many systems but may
take tens of seconds. There is no programmed upper cap.
"""

from __future__ import annotations

import argparse
from bisect import bisect_left
from dataclasses import dataclass
from decimal import Decimal, localcontext
from time import perf_counter
from typing import Final


DEFAULT_STOP: Final[int] = 1_000_000
DEFAULT_BLOCK_START: Final[int] = 256


@dataclass(slots=True)
class RecursiveState:
    """Complete state passed from one integer position to the next."""

    x: int
    stop: int
    crossovers: dict[int, list[int]]
    primes: list[int]
    twin_pairs: list[tuple[int, int]]
    twin_centres: list[int]
    pending_left_boundary: int | None
    three_is_prime: bool
    trace_until: int


@dataclass(slots=True)
class Continue:
    """A tail-recursive continuation for the trampoline."""

    state: RecursiveState


@dataclass(frozen=True, slots=True)
class GenerationResult:
    stop: int
    primes: tuple[int, ...]
    twin_pairs: tuple[tuple[int, int], ...]
    twin_centres: tuple[int, ...]
    elapsed_seconds: float


def schedule_next_crossing(
    crossovers: dict[int, list[int]],
    prime: int,
    next_position: int,
    stop: int,
) -> None:
    """Schedule one prime row's next additive landing."""

    if next_position <= stop:
        crossovers.setdefault(next_position, []).append(prime)


def trace_position(
    x: int,
    is_prime: bool,
    landing_rows: list[int] | None,
    opened_row: int | None,
    new_twin: tuple[int, int] | None,
) -> None:
    """Print one readable step of the recursive construction."""

    if x == 1:
        print("1 : starting unit")
        return

    if is_prime:
        print(f"{x} : open row {opened_row}; first crossover at {2 * x}")
    else:
        rows = ", ".join(str(prime) for prime in (landing_rows or []))
        print(f"{x} : crossed by row(s) {rows}")

    if new_twin is not None:
        left, right = new_twin
        print(
            f"    centre {left + 1} : "
            f"{left} and {right} both remain open -> twin pair"
        )


def count(state: RecursiveState) -> RecursiveState | Continue:
    """
    Classify one integer and return the next recursive state.

    The function never asks whether x is prime by using an outside test.
    A position is prime exactly when no previously opened crossover row lands
    on it.
    """

    x = state.x

    if x > state.stop:
        return state

    if x == 1:
        if x <= state.trace_until:
            trace_position(
                x=x,
                is_prime=False,
                landing_rows=None,
                opened_row=None,
                new_twin=None,
            )

        state.x = 2
        return Continue(state)

    landing_rows = state.crossovers.pop(x, None)
    is_prime = landing_rows is None
    opened_row: int | None = None

    if landing_rows is not None:
        for prime in landing_rows:
            schedule_next_crossing(
                crossovers=state.crossovers,
                prime=prime,
                next_position=x + prime,
                stop=state.stop,
            )
    else:
        opened_row = x
        state.primes.append(x)

        schedule_next_crossing(
            crossovers=state.crossovers,
            prime=x,
            next_position=2 * x,
            stop=state.stop,
        )

    new_twin: tuple[int, int] | None = None

    if x == 3:
        state.three_is_prime = is_prime

    elif x == 5 and is_prime and state.three_is_prime:
        new_twin = (3, 5)
        state.twin_pairs.append(new_twin)
        state.twin_centres.append(4)

    if x >= 5 and x % 6 == 5:
        state.pending_left_boundary = x if is_prime else None

    elif x >= 7 and x % 6 == 1:
        if (
            is_prime
            and state.pending_left_boundary is not None
            and state.pending_left_boundary == x - 2
        ):
            new_twin = (x - 2, x)
            state.twin_pairs.append(new_twin)
            state.twin_centres.append(x - 1)

        state.pending_left_boundary = None

    if x <= state.trace_until:
        trace_position(
            x=x,
            is_prime=is_prime,
            landing_rows=landing_rows,
            opened_row=opened_row,
            new_twin=new_twin,
        )

    state.x = x + 1
    return Continue(state)


def run_recursive_generator(stop: int, trace_until: int = 0) -> GenerationResult:
    """Run the recursive state transition through an arbitrary finite stop."""

    if stop < 1:
        raise ValueError("stop must be at least 1")

    if trace_until < 0:
        raise ValueError("trace_until cannot be negative")

    state = RecursiveState(
        x=1,
        stop=stop,
        crossovers={},
        primes=[],
        twin_pairs=[],
        twin_centres=[],
        pending_left_boundary=None,
        three_is_prime=False,
        trace_until=min(trace_until, stop),
    )

    started = perf_counter()

    action: RecursiveState | Continue = count(state)
    while isinstance(action, Continue):
        action = count(action.state)

    elapsed = perf_counter() - started

    return GenerationResult(
        stop=stop,
        primes=tuple(action.primes),
        twin_pairs=tuple(action.twin_pairs),
        twin_centres=tuple(action.twin_centres),
        elapsed_seconds=elapsed,
    )


def count_sorted_values(values: tuple[int, ...], low: int, high: int) -> int:
    """Count values in the half-open interval [low, high)."""

    if high <= low:
        return 0

    return bisect_left(values, high) - bisect_left(values, low)


def gold_floor(value: int) -> int:
    """
    Return floor(phi * value) with precision scaled to the size of value.

    Since phi is irrational, no integer lies exactly on phi * value.
    """

    with localcontext() as context:
        context.prec = max(50, len(str(abs(value))) + 30)
        phi = (Decimal(1) + Decimal(5).sqrt()) / Decimal(2)
        return int(phi * Decimal(value))


def ratio_text(numerator: int, denominator: int) -> str:
    if denominator == 0:
        return "-"
    return f"{numerator / denominator:.6f}"


def print_summary(result: GenerationResult) -> None:
    """Print the principal generated counts."""

    print("\nRECURSIVE CROSSOVER SUMMARY")
    print("=" * 72)
    print(f"Completed number line : 1 through {result.stop:,}")
    print(f"Generated primes      : {len(result.primes):,}")
    print(f"Generated twin pairs  : {len(result.twin_pairs):,}")
    print(f"Elapsed time          : {result.elapsed_seconds:.3f} seconds")

    if result.primes:
        print(f"Last generated prime  : {result.primes[-1]:,}")

    if result.twin_pairs:
        left, right = result.twin_pairs[-1]
        print(f"Last twin pair        : ({left:,}, {right:,})")
        print(f"Last twin centre      : {left + 1:,}")

    print(
        "\nEvery prime above was opened because no earlier additive row "
        "landed on it."
    )
    print(
        "Every twin pair above was certified at a centre 6m whose two "
        "boundaries remained open."
    )


def print_block_growth_table(
    result: GenerationResult,
    block_start: int,
) -> None:
    """Print counts in consecutive doubled blocks [B, 2B)."""

    if block_start < 1:
        raise ValueError("block_start must be at least 1")

    rows: list[tuple[int, int, int, int, str]] = []
    block = block_start
    previous_twins: int | None = None

    while 2 * block <= result.stop:
        upper = 2 * block
        prime_count = count_sorted_values(result.primes, block, upper)
        twin_count = count_sorted_values(result.twin_centres, block, upper)

        growth = (
            "-"
            if previous_twins in (None, 0)
            else f"{twin_count / previous_twins:.6f}"
        )

        rows.append((block, upper, prime_count, twin_count, growth))
        previous_twins = twin_count
        block *= 2

    if not rows:
        print(
            "\nNo complete doubled block can be printed. "
            "Use a smaller --block-start or a larger stop."
        )
        return

    print("\nSUCCESSIVE DOUBLED BLOCKS")
    print("=" * 72)
    print(
        f"{'B':>14}  {'2B':>14}  {'primes':>12}  "
        f"{'twin pairs':>12}  {'twin growth':>12}"
    )
    print("-" * 72)

    for block, upper, primes, twins, growth in rows:
        print(
            f"{block:>14,}  {upper:>14,}  {primes:>12,}  "
            f"{twins:>12,}  {growth:>12}"
        )


def print_gold_table(
    result: GenerationResult,
    block_start: int,
) -> None:
    """Print prime and twin-centre counts across B < phi B < 2B."""

    rows: list[tuple[int, int, int, str, int, int, str]] = []
    block = block_start

    while 2 * block <= result.stop:
        upper = 2 * block
        first_upper_integer = gold_floor(block) + 1

        lower_primes = count_sorted_values(
            result.primes,
            block,
            first_upper_integer,
        )
        upper_primes = count_sorted_values(
            result.primes,
            first_upper_integer,
            upper,
        )
        lower_twins = count_sorted_values(
            result.twin_centres,
            block,
            first_upper_integer,
        )
        upper_twins = count_sorted_values(
            result.twin_centres,
            first_upper_integer,
            upper,
        )

        rows.append(
            (
                block,
                lower_primes,
                upper_primes,
                ratio_text(lower_primes, upper_primes),
                lower_twins,
                upper_twins,
                ratio_text(lower_twins, upper_twins),
            )
        )

        block *= 2

    if not rows:
        return

    print("\nGOLD DIVISION OF EACH BLOCK")
    print("=" * 106)
    print(
        f"{'B':>14}  {'lower primes':>12}  {'upper primes':>12}  "
        f"{'prime ratio':>11}  {'lower twins':>12}  "
        f"{'upper twins':>12}  {'twin ratio':>11}"
    )
    print("-" * 106)

    for (
        block,
        lower_primes,
        upper_primes,
        prime_ratio,
        lower_twins,
        upper_twins,
        twin_ratio,
    ) in rows:
        print(
            f"{block:>14,}  {lower_primes:>12,}  {upper_primes:>12,}  "
            f"{prime_ratio:>11}  {lower_twins:>12,}  "
            f"{upper_twins:>12,}  {twin_ratio:>11}"
        )

    print("-" * 106)
    print("Gold comparison value: phi = 1.618033988749894...")


def print_requested_lists(
    result: GenerationResult,
    show_primes: bool,
    show_twins: bool,
) -> None:
    if show_primes:
        print("\nGENERATED PRIMES")
        print(result.primes)

    if show_twins:
        print("\nGENERATED TWIN-PRIME PAIRS")
        print(result.twin_pairs)


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate primes and twin primes from recursive additive "
            "crossover rows, without an external primality test."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    parser.add_argument(
        "stop",
        nargs="?",
        type=int,
        default=DEFAULT_STOP,
        help="classify every integer from 1 through this value",
    )
    parser.add_argument(
        "--trace",
        type=int,
        default=0,
        metavar="N",
        help="print every recursive action from 1 through N",
    )
    parser.add_argument(
        "--block-start",
        type=int,
        default=DEFAULT_BLOCK_START,
        metavar="B",
        help="first lower boundary used for doubled-block and Gold tables",
    )
    parser.add_argument(
        "--no-blocks",
        action="store_true",
        help="do not print doubled-block or Gold tables",
    )
    parser.add_argument(
        "--show-primes",
        action="store_true",
        help="print the complete generated prime list",
    )
    parser.add_argument(
        "--show-twins",
        action="store_true",
        help="print the complete generated twin-prime list",
    )

    return parser.parse_args()


def main() -> None:
    args = parse_arguments()

    if args.stop < 1:
        raise SystemExit("Error: stop must be at least 1.")

    if args.trace < 0:
        raise SystemExit("Error: --trace cannot be negative.")

    if args.block_start < 1:
        raise SystemExit("Error: --block-start must be at least 1.")

    result = run_recursive_generator(
        stop=args.stop,
        trace_until=args.trace,
    )

    print_summary(result)

    if not args.no_blocks:
        print_block_growth_table(result, args.block_start)
        print_gold_table(result, args.block_start)

    print_requested_lists(
        result=result,
        show_primes=args.show_primes,
        show_twins=args.show_twins,
    )


if __name__ == "__main__":
    main()
