#!/usr/bin/env python3
"""
EUCLIDEAN METALLIC TWIN-STATE GEOMETRY

This program formalizes the self-similar split of one eight-state
binary cube into two reflected four-state halves.

Three-bit states
----------------
Use the eight states i = 0,...,7:

    000 001 010 011 | 100 101 110 111

The upper half is the bitwise reflection of the lower half:

    i* = 7 - i

and the Hamming weights satisfy:

    weight(i*) = 3 - weight(i)

Indexed metallic family
-----------------------
At lift level r, assign metallic index

    m_r(i) = r + weight(i)

Therefore reflected states obey

    m_r(i) + m_r(7-i) = 2r + 3.

Every reflected pair has the same midpoint:

    midpoint = r + 3/2.

The unique outer pair is:

    (r, r+3)

and the three interior reflected pairs are all:

    (r+1, r+2).

Thus one complete eight-state cube contains:

    one outer bounding interval,
    three copies of one adjacent inner interval.

The inner interval is the compressed metallic "twin state":

    low  = r + 1
    high = r + 2
    gap  = 1
    midpoint = r + 3/2

For the first lift r=1, this is exactly:

    (2,3).

Affine period space
-------------------
For any recursive period pair (a,b), metallic index m maps to

    P(m) = a + m*b.

So the outer and inner intervals become:

    outer = [a+r*b,       a+(r+3)*b]
    inner = [a+(r+1)*b,   a+(r+2)*b]

They have the same midpoint:

    a + (r+3/2)*b

and radii:

    outer radius = 3b/2
    inner radius = b/2.

This is an exact 3:1 self-similar nesting.

Important
---------
This geometry compresses the metallic location of a candidate twin
state. It does not by itself prove that the corresponding arithmetic
boundaries are prime. A modular survival state must still be attached
to the geometric state.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from time import perf_counter


# ============================================================
# CONFIGURATION
# ============================================================

LEVELS = 13

# Example recursive period pairs to demonstrate affine invariance.
PERIOD_PAIRS = (
    (2, 3),
    (3, 5),
    (8, 11),
    (835, 2748),
)


# ============================================================
# BASIC GEOMETRY
# ============================================================

def weight(index: int) -> int:
    if not 0 <= index <= 7:
        raise ValueError("index must be between 0 and 7")
    return index.bit_count()


def reflected_index(index: int) -> int:
    return 7 - index


def metallic_index(level: int, index: int) -> int:
    return level + weight(index)


@dataclass(frozen=True, slots=True)
class EuclideanCell:
    level: int
    outer_low: int
    inner_low: int
    inner_high: int
    outer_high: int
    midpoint: Fraction
    inner_radius: Fraction
    outer_radius: Fraction

    @classmethod
    def from_level(cls, level: int) -> "EuclideanCell":
        return cls(
            level=level,
            outer_low=level,
            inner_low=level + 1,
            inner_high=level + 2,
            outer_high=level + 3,
            midpoint=Fraction(2 * level + 3, 2),
            inner_radius=Fraction(1, 2),
            outer_radius=Fraction(3, 2),
        )


@dataclass(frozen=True, slots=True)
class AffineCell:
    previous: int
    current: int
    level: int
    outer_low: int
    inner_low: int
    inner_high: int
    outer_high: int
    midpoint: Fraction
    inner_radius: Fraction
    outer_radius: Fraction


def affine_cell(
    previous: int,
    current: int,
    level: int,
) -> AffineCell:
    def period(index: int) -> int:
        return previous + index * current

    return AffineCell(
        previous=previous,
        current=current,
        level=level,
        outer_low=period(level),
        inner_low=period(level + 1),
        inner_high=period(level + 2),
        outer_high=period(level + 3),
        midpoint=Fraction(
            2 * previous + (2 * level + 3) * current,
            2,
        ),
        inner_radius=Fraction(current, 2),
        outer_radius=Fraction(3 * current, 2),
    )


# ============================================================
# VERIFICATION
# ============================================================

def verify_cube(level: int) -> None:
    """
    Verify all reflection and midpoint identities exactly.
    """
    cell = EuclideanCell.from_level(level)

    assert cell.outer_low + cell.outer_high == 2 * cell.midpoint
    assert cell.inner_low + cell.inner_high == 2 * cell.midpoint
    assert cell.outer_radius == 3 * cell.inner_radius

    interior_pairs = 0
    outer_pairs = 0

    for index in range(4):
        reflected = reflected_index(index)

        low_index = metallic_index(level, index)
        high_index = metallic_index(level, reflected)

        assert low_index + high_index == 2 * level + 3

        ordered = tuple(sorted((low_index, high_index)))

        if ordered == (level, level + 3):
            outer_pairs += 1
        elif ordered == (level + 1, level + 2):
            interior_pairs += 1
        else:
            raise AssertionError(
                f"unexpected reflected pair {ordered}"
            )

    assert outer_pairs == 1
    assert interior_pairs == 3


# ============================================================
# OUTPUT
# ============================================================

def show_cube(level: int) -> None:
    print("=" * 88)
    print(f"EIGHT-STATE REFLECTION AT METALLIC LEVEL r={level}")
    print("=" * 88)
    print(
        "lower state | weight | M-index || upper reflection | "
        "weight | M-index | sum"
    )

    for lower in range(4):
        upper = reflected_index(lower)

        lower_weight = weight(lower)
        upper_weight = weight(upper)

        lower_m = metallic_index(level, lower)
        upper_m = metallic_index(level, upper)

        print(
            f"{lower:03b}         | "
            f"{lower_weight:^6} | "
            f"{lower_m:^7} || "
            f"{upper:03b}              | "
            f"{upper_weight:^6} | "
            f"{upper_m:^7} | "
            f"{lower_m + upper_m}"
        )

    cell = EuclideanCell.from_level(level)

    print()
    print(
        f"Outer bounds:   ({cell.outer_low}, {cell.outer_high})"
    )
    print(
        f"Inner twin state: ({cell.inner_low}, {cell.inner_high})"
    )
    print(
        f"Shared midpoint: {cell.midpoint}"
    )
    print(
        f"Outer radius:   {cell.outer_radius}"
    )
    print(
        f"Inner radius:   {cell.inner_radius}"
    )
    print(
        "Radius ratio:   3 : 1"
    )


def show_level_chain() -> None:
    print("\n" + "=" * 88)
    print("SELF-SIMILAR TWIN-STATE CHAIN")
    print("=" * 88)
    print(
        "level | outer bounds | inner adjacent pair | "
        "doubled midpoint | gap"
    )

    previous_high = None

    for level in range(1, LEVELS + 1):
        cell = EuclideanCell.from_level(level)

        if previous_high is not None:
            assert cell.inner_low == previous_high

        print(
            f"{level:>5} | "
            f"({cell.outer_low:>2},{cell.outer_high:<2})      | "
            f"({cell.inner_low:>2},{cell.inner_high:<2})             | "
            f"{2 * cell.midpoint:>16} | "
            f"{cell.inner_high - cell.inner_low}"
        )

        previous_high = cell.inner_high

    print()
    print(
        "Each lift advances:"
    )
    print(
        "    (r+1, r+2) -> (r+2, r+3)"
    )
    print(
        "so the upper member of one twin state becomes the lower "
        "member of the next."
    )


def show_affine_examples() -> None:
    print("\n" + "=" * 88)
    print("THE SAME GEOMETRY INSIDE ACTUAL PERIOD PAIRS")
    print("=" * 88)
    print(
        "(a,b) | level | outer periods | inner periods | "
        "shared midpoint | radii"
    )

    for previous, current in PERIOD_PAIRS:
        for level in (1, 2):
            cell = affine_cell(
                previous,
                current,
                level,
            )

            assert (
                cell.outer_low + cell.outer_high
                == 2 * cell.midpoint
            )
            assert (
                cell.inner_low + cell.inner_high
                == 2 * cell.midpoint
            )
            assert (
                cell.outer_radius
                == 3 * cell.inner_radius
            )

            print(
                f"({previous:>3},{current:<4}) | "
                f"{level:^5} | "
                f"({cell.outer_low:,}, {cell.outer_high:,}) | "
                f"({cell.inner_low:,}, {cell.inner_high:,}) | "
                f"{cell.midpoint} | "
                f"{cell.inner_radius}:{cell.outer_radius}"
            )


def main() -> None:
    start = perf_counter()

    for level in range(1, LEVELS + 1):
        verify_cube(level)

    show_cube(level=1)
    show_cube(level=2)
    show_level_chain()
    show_affine_examples()

    print("\n" + "=" * 88)
    print("CONCLUSION")
    print("=" * 88)
    print(
        "The 0-to-8 cube contains one outer reflected interval and "
        "three copies of one inner adjacent interval."
    )
    print(
        "At level 1 the inner interval is exactly (2,3)."
    )
    print(
        "The compressed Euclidean twin state is therefore:"
    )
    print(
        "    (level r, midpoint 2r+3 in doubled coordinates, "
        "inner radius 1)"
    )
    print(
        "This tracks location and separation without storing all "
        "eight states."
    )
    print(
        "To become a twin-prime generator, the state still needs a "
        "modular survival signature saying whether either arithmetic "
        "boundary has been blocked."
    )

    print(
        f"\nRuntime: "
        f"{perf_counter() - start:.6f} seconds"
    )


if __name__ == "__main__":
    main()
