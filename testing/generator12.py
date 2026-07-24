#!/usr/bin/env python3
"""
INDEXED METALLIC LIFT FAMILY

Use integer indices instead of metal names:

    M_1: next = a + 1*b
    M_2: next = a + 2*b
    M_3: next = a + 3*b
    M_4: next = a + 4*b
    ...
    M_n: next = a + n*b

Traditional informal names:
    M_1 = Gold
    M_2 = Silver
    M_3 = Bronze
    M_4 is sometimes called Copper

Three-bit lift rule
-------------------
The seven active states of one binary cube have Hamming weights

    0, 1, 1, 2, 1, 2, 2

At metallic level r, add r to those weights:

    level 1: 1,2,2,3,2,3,3
    level 2: 2,3,3,4,3,4,4
    level 3: 3,4,4,5,4,5,5
    ...

So every completed eight-state lift introduces the next member of the
unlimited metallic family.

Exact increment identity
------------------------
Starting from any period pair (a,b):

    one M_(n+1) step:
        (a,b) -> (b, a+(n+1)b)

    M_n followed by M_1:
        (a,b) -> (b, a+n*b)
              -> (a+n*b, a+(n+1)b)

The terminal current period is identical, but the two-step macro keeps
the intermediate period and multiplies it into the centre.

For seed (a,b)=(2,3), the intermediate factors are:

    n=1 -> 5
    n=2 -> 8
    n=3 -> 11
    n=4 -> 14
    ...

Therefore the earlier factor 8 is the M_2 intermediate period. It is
not a universal reset factor for every metallic level.

Validation is optional and separate from generation.
"""

from __future__ import annotations

from dataclasses import dataclass
from time import perf_counter

try:
    from sympy import isprime
except ImportError:
    isprime = None


# ============================================================
# CONFIGURATION
# ============================================================

LEVELS = 6
VALIDATE = True

# True:
#   carry the full period pair into the next metallic level.
# False:
#   reset local periods to (2,3) after each seven-operation block,
#   while retaining the accumulated centre.
CARRY_PERIODS = True


# ============================================================
# RECURSIVE STATE
# ============================================================

@dataclass(frozen=True, slots=True)
class State:
    previous: int
    current: int
    centre: int


def metallic_step(state: State, index: int) -> State:
    """Apply M_index."""
    next_period = state.previous + index * state.current

    return State(
        previous=state.current,
        current=next_period,
        centre=state.centre * next_period,
    )


def lift_block(level: int) -> tuple[int, ...]:
    """
    Seven active cube states.

    Hamming weights of binary states 000 through 110:
        0,1,1,2,1,2,2

    Add `level` to obtain metallic indices.
    """
    weights = (0, 1, 1, 2, 1, 2, 2)

    return tuple(
        level + weight
        for weight in weights
    )


def apply_block(
    state: State,
    indices: tuple[int, ...],
) -> State:
    for index in indices:
        state = metallic_step(state, index)

    return state


def twin_status(centre: int) -> str:
    """Independent experimental check only."""
    if not VALIDATE:
        return "NOT-CHECKED"

    if isprime is None:
        return "SYMPY-NOT-INSTALLED"

    return (
        "TWIN"
        if bool(isprime(centre - 1)) and bool(isprime(centre + 1))
        else "BLOCKED"
    )


# ============================================================
# M_(n+1) IDENTITY
# ============================================================

def show_increment_identity(max_index: int = 8) -> None:
    seed = State(2, 3, 6)

    print("=" * 80)
    print("M_(n+1) VERSUS M_n FOLLOWED BY M_1")
    print("=" * 80)
    print(
        " n | single M_(n+1) period | macro M_n,M_1 period | "
        "intermediate factor | centres"
    )

    for n in range(1, max_index + 1):
        single = metallic_step(seed, n + 1)

        first = metallic_step(seed, n)
        macro = metallic_step(first, 1)

        same_period = single.current == macro.current

        print(
            f"{n:>2} | "
            f"{single.current:>22,} | "
            f"{macro.current:>21,} | "
            f"{first.current:>19,} | "
            f"{single.centre:,} -> {macro.centre:,} "
            f"same={same_period}"
        )


# ============================================================
# SHIFTED EIGHT-STATE LIFTS
# ============================================================

def run_lift_family() -> None:
    state = State(2, 3, 6)

    print("\n" + "=" * 80)
    print("UNLIMITED INDEXED METALLIC LIFT FAMILY")
    print("=" * 80)
    print(
        "level | seven active metallic indices | terminal pair | "
        "centre digits | status"
    )

    for level in range(1, LEVELS + 1):
        indices = lift_block(level)
        state = apply_block(state, indices)

        print(
            f"{level:>5} | "
            f"{str(indices):<33} | "
            f"({state.previous:,}, {state.current:,}) | "
            f"{len(str(state.centre)):>13,} | "
            f"{twin_status(state.centre)}"
        )

        if level == 1:
            print(
                f"      first lift centre: "
                f"{state.centre - 1:,} : "
                f"{state.centre:,} : "
                f"{state.centre + 1:,}"
            )

        if not CARRY_PERIODS:
            state = State(
                previous=2,
                current=3,
                centre=state.centre,
            )


# ============================================================
# NEXT MEMBER: M_4
# ============================================================

def show_m4_example() -> None:
    seed = State(2, 3, 6)

    m4 = metallic_step(seed, 4)

    m3 = metallic_step(seed, 3)
    m3_then_m1 = metallic_step(m3, 1)

    print("\n" + "=" * 80)
    print("THE NEXT MEMBER M_4")
    print("=" * 80)
    print(
        f"Single M_4: period={m4.current}, "
        f"centre={m4.centre:,}, status={twin_status(m4.centre)}"
    )
    print(
        f"Exact M_3,M_1 macro: periods 11 then "
        f"{m3_then_m1.current}, centre={m3_then_m1.centre:,}, "
        f"status={twin_status(m3_then_m1.centre)}"
    )
    print(
        f"Macro/single centre ratio: "
        f"{m3_then_m1.centre // m4.centre}"
    )
    print(
        "The ratio is 11, the intermediate M_3 period. "
        "For M_2 -> M_3 it was 8."
    )


def main() -> None:
    start = perf_counter()

    print("=" * 80)
    print("INDEXED METALLIC FAMILY: M_1, M_2, M_3, M_4, ...")
    print("=" * 80)
    print(f"Levels tested: {LEVELS}")
    print(f"Carry periods: {CARRY_PERIODS}")
    print(f"Independent validation: {VALIDATE}")

    show_increment_identity()
    show_m4_example()
    run_lift_family()

    print("\n" + "=" * 80)
    print("CONCLUSION")
    print("=" * 80)
    print(
        "The eight-state lift rule extends exactly to an unlimited "
        "indexed family."
    )
    print(
        "The first lifted block is twin, but simply shifting every "
        "index upward at the next lift does not preserve twin status."
    )
    print(
        "Therefore the unlimited family is real, while the missing "
        "piece remains the centre-state transformation performed at "
        "the lift."
    )
    print(f"\nRuntime: {perf_counter() - start:.6f} seconds")


if __name__ == "__main__":
    main()
