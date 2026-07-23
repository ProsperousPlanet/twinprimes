#!/usr/bin/env python3
"""
Three-Bit Metallic Lift Experiment

Interpret one mod-6 completion as carrying a three-bit dyadic state.

The eight states split by Hamming weight as:

    000                     weight 0 -> Gold
    001, 010, 100           weight 1 -> Silver
    011, 101, 110           weight 2 -> Bronze
    111                     weight 3 -> LIFT / return to Gold

The layer sizes are 1,3,3,1, Pascal row 3.

The seven active states before the lift therefore give:

    G S S B S B B

with metallic recurrences:

    G: next = a + b
    S: next = a + 2b
    B: next = a + 3b

and:

    centre = centre * next

The recursive construction itself uses no primality test.  Validation
below 2^64 is performed separately only to test the hypothesis.
"""

from __future__ import annotations

from dataclasses import dataclass
from time import perf_counter

ACTIVE_BLOCK = "GSSBSBB"
ORDER = {"G": 1, "S": 2, "B": 3}
ROTATE = {"G": "S", "S": "B", "B": "G"}

BLOCKS_TO_TEST = 6
GLOBAL_PHASE_STEPS = 64

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


def boundary_status(centre: int) -> str:
    if centre + 1 >= UINT64_LIMIT:
        return "ABOVE-64-BIT"

    if is_prime_64(centre - 1) and is_prime_64(centre + 1):
        return "EXACT-TWIN"

    return "BLOCKED"


@dataclass(frozen=True, slots=True)
class State:
    previous: int
    current: int
    centre: int


def metallic_step(state: State, symbol: str) -> State:
    next_period = state.previous + ORDER[symbol] * state.current

    return State(
        previous=state.current,
        current=next_period,
        centre=state.centre * next_period,
    )


def apply_block(state: State, block: str) -> State:
    for symbol in block:
        state = metallic_step(state, symbol)
    return state


def rotate_block(block: str, rotations: int) -> str:
    result = block
    for _ in range(rotations % 3):
        result = "".join(ROTATE[symbol] for symbol in result)
    return result


def print_cube_table() -> None:
    print("=" * 80)
    print("THREE-BIT METALLIC CUBE")
    print("=" * 80)
    print("state | weight | action")

    for value in range(8):
        bits = format(value, "03b")
        weight = bits.count("1")

        action = {
            0: "G",
            1: "S",
            2: "B",
            3: "LIFT -> G",
        }[weight]

        print(f" {bits}  |   {weight}    | {action}")

    print(f"\nActive block: {ACTIVE_BLOCK}")
    print("Lift state:   111")


def first_block_test() -> State:
    state = State(2, 3, 6)

    print("\n" + "=" * 80)
    print("FIRST SEVEN ACTIVE STATES")
    print("=" * 80)
    print("step | state | action | period | centre | result")

    for index, symbol in enumerate(ACTIVE_BLOCK, start=1):
        cube_state = format(index - 1, "03b")
        state = metallic_step(state, symbol)

        print(
            f"{index:>4} | {cube_state} |   {symbol}    | "
            f"{state.current:>6,} | {state.centre:>18,} | "
            f"{boundary_status(state.centre)}"
        )

    print(f"\nCentre at the lift boundary: {state.centre:,}")
    print(
        f"Structure: {state.centre - 1:,} : "
        f"{state.centre:,} : {state.centre + 1:,}"
    )

    return state


def ordinary_eighth_step_test(state: State) -> None:
    ordinary = metallic_step(state, "G")

    print("\n" + "=" * 80)
    print("TREATING 111 AS AN ORDINARY GOLD STEP")
    print("=" * 80)
    print(f"After ordinary eighth operation: {ordinary.centre:,}")
    print(f"Status: {boundary_status(ordinary.centre)}")


def continuation_test(
    title: str,
    rotate: bool,
    reseed: bool,
) -> None:
    state = State(2, 3, 6)

    print("\n" + "=" * 80)
    print(title)
    print("=" * 80)
    print("block | word    | digits | result")

    for block_number in range(1, BLOCKS_TO_TEST + 1):
        block = rotate_block(
            ACTIVE_BLOCK,
            block_number - 1 if rotate else 0,
        )

        state = apply_block(state, block)

        print(
            f"{block_number:>5} | {block:<7} | "
            f"{len(str(state.centre)):>6} | "
            f"{boundary_status(state.centre)}"
        )

        if reseed:
            state = State(2, 3, state.centre)


def global_symbol(index: int) -> str:
    """
    Recursive 8-adic lift:
    every group of three binary digits contributes a phase.
    """
    return ("G", "S", "B")[index.bit_count() % 3]


def global_phase_test() -> None:
    state = State(2, 3, 6)
    hits = []

    print("\n" + "=" * 80)
    print("RECURSIVELY LIFTED 8-ADIC PHASE")
    print("=" * 80)

    for step_number in range(1, GLOBAL_PHASE_STEPS + 1):
        index = step_number - 1
        symbol = global_symbol(index)
        state = metallic_step(state, symbol)
        status = boundary_status(state.centre)

        if status == "EXACT-TWIN":
            hits.append((step_number, symbol, state.centre))

        if step_number in (1, 2, 4, 7, 8, 16, 32, 64):
            print(
                f"step={step_number:>2} index={index:>2} "
                f"symbol={symbol} digits={len(str(state.centre)):>4} "
                f"status={status}"
            )

    print("\nExact twin hits on the singular lifted path:")
    for step_number, symbol, centre in hits:
        print(
            f"  step={step_number:>2} symbol={symbol} "
            f"{centre - 1:,} : {centre:,} : {centre + 1:,}"
        )


def main() -> None:
    start = perf_counter()

    print_cube_table()
    first_lift = first_block_test()
    ordinary_eighth_step_test(first_lift)

    continuation_test(
        "REPEAT THE SAME SEVEN-STATE BLOCK",
        rotate=False,
        reseed=False,
    )

    continuation_test(
        "ROTATE G -> S -> B -> G AFTER EACH LIFT",
        rotate=True,
        reseed=False,
    )

    continuation_test(
        "ROTATE AFTER EACH LIFT AND RESEED PERIODS",
        rotate=True,
        reseed=True,
    )

    global_phase_test()

    print("\n" + "=" * 80)
    print("CONCLUSION")
    print("=" * 80)
    print(
        "The 1:3:3:1 binary layering gives a precise meaning "
        "to G -> S -> B -> lift."
    )
    print(
        "The first seven-state block ends at an exact twin centre."
    )
    print(
        "The ordinary eighth multiplication destroys that result."
    )
    print(
        "The simple continuation rules tested here do not preserve "
        "twin status, so the lift still needs a new state transform."
    )
    print(f"\nRuntime: {perf_counter() - start:.6f} seconds")


if __name__ == "__main__":
    main()
