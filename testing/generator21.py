#!/usr/bin/env python3
"""
SYMMETRIC-POWER METALLIC MEMORY TEST

This tests the idea that a longer word stores the extra information
created when a Gold recurrence is lifted to higher powers.

Base Gold recurrence
--------------------
    x[n+2] = x[n+1] + x[n]

A two-letter state stores:
    (a, b)

To update the squared system exactly, two letters are insufficient,
because:

    (a+b)^2 = a^2 + 2ab + b^2.

The square therefore needs three memory letters:
    (a^2, ab, b^2).

The coefficient 2 is an opening/cross-term coefficient. It is not a
correction that must be added repeatedly afterward.

More generally, power d uses d+1 monomial memory letters:

    (a^d, a^(d-1)b, ..., ab^(d-1), b^d).

The lifted Gold transition is generated recursively from Pascal
coefficients.

The program also derives the scalar recurrence obeyed by x[n]^d and
shows that its leading coefficients are:

    1, 2, 3, 5, 8, 13, ...

This explains why the five-letter word (1,2,3,5,8) appeared naturally.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb
from typing import Iterable

from sympy import Matrix, Rational, isprime


MAX_POWER = 6
SEQUENCE_TERMS = 30


# ============================================================
# BASIC GOLD SEQUENCE
# ============================================================

def gold_sequence(
    first: int,
    second: int,
    count: int,
) -> tuple[int, ...]:
    if count <= 0:
        return ()

    if count == 1:
        return (first,)

    values = [first, second]

    while len(values) < count:
        values.append(
            values[-2] + values[-1]
        )

    return tuple(values)


# ============================================================
# SYMMETRIC-POWER MEMORY
# ============================================================

def monomial_state(
    a: int,
    b: int,
    degree: int,
) -> tuple[int, ...]:
    """
    (a^degree, a^(degree-1)b, ..., b^degree)
    """
    return tuple(
        a ** (degree - j) * b ** j
        for j in range(degree + 1)
    )


def lifted_gold_matrix(
    degree: int,
) -> tuple[tuple[int, ...], ...]:
    """
    Matrix for:
        (a,b) -> (b,a+b)

    in the degree-d monomial basis:
        a^d, a^(d-1)b, ..., b^d.
    """
    size = degree + 1
    rows = []

    for j in range(size):
        # New coordinate:
        #   b^(degree-j) * (a+b)^j
        row = [0] * size

        for k in range(j + 1):
            # a^k b^(degree-k) is basis index degree-k.
            column = degree - k
            row[column] += comb(j, k)

        rows.append(tuple(row))

    return tuple(rows)


def matrix_vector(
    matrix: tuple[tuple[int, ...], ...],
    vector: tuple[int, ...],
) -> tuple[int, ...]:
    return tuple(
        sum(
            coefficient * value
            for coefficient, value in zip(row, vector)
        )
        for row in matrix
    )


def verify_lift(
    a: int,
    b: int,
    degree: int,
) -> bool:
    state = monomial_state(
        a,
        b,
        degree,
    )

    transformed = matrix_vector(
        lifted_gold_matrix(degree),
        state,
    )

    expected = monomial_state(
        b,
        a + b,
        degree,
    )

    return transformed == expected


# ============================================================
# EXACT SCALAR RECURRENCES FOR POWERS
# ============================================================

def recurrence_coefficients(
    sequence: tuple[int, ...],
    order: int,
) -> tuple[int, ...]:
    """
    Solve exactly for:
        y[n] = c0*y[n-1] + ... + c[order-1]*y[n-order].
    """
    rows = []
    targets = []

    for n in range(order, 2 * order):
        rows.append([
            Rational(sequence[n - 1 - j])
            for j in range(order)
        ])
        targets.append(
            Rational(sequence[n])
        )

    solution = Matrix(rows).LUsolve(
        Matrix(targets)
    )

    coefficients = tuple(
        int(value)
        for value in solution
    )

    # Verify beyond the equations used to derive it.
    for n in range(order, len(sequence)):
        predicted = sum(
            coefficients[j] * sequence[n - 1 - j]
            for j in range(order)
        )

        if predicted != sequence[n]:
            raise RuntimeError(
                f"recurrence verification failed at n={n}"
            )

    return coefficients


def signed_formula(
    symbol: str,
    coefficients: tuple[int, ...],
) -> str:
    order = len(coefficients)
    pieces = []

    for j, coefficient in enumerate(coefficients):
        index = order - 1 - j
        term = (
            f"{symbol}[n-{j + 1}]"
            if j + 1 > 1
            else f"{symbol}[n-1]"
        )

        magnitude = abs(coefficient)

        if magnitude != 1:
            term = f"{magnitude}*{term}"

        if not pieces:
            pieces.append(
                f"-{term}"
                if coefficient < 0
                else term
            )
        else:
            pieces.append(
                (" - " if coefficient < 0 else " + ")
                + term
            )

    return "".join(pieces)


# ============================================================
# PRIOR TWIN-PATH CONNECTION
# ============================================================

@dataclass(frozen=True, slots=True)
class CentreState:
    previous: int
    current: int
    centre: int


def metallic_step(
    state: CentreState,
    order: int,
) -> CentreState:
    next_period = (
        state.previous
        + order * state.current
    )

    return CentreState(
        previous=state.current,
        current=next_period,
        centre=state.centre * next_period,
    )


def apply_word(
    state: CentreState,
    word: Iterable[int],
) -> CentreState:
    for order in word:
        state = metallic_step(
            state,
            order,
        )

    return state


def twin_centre(
    centre: int,
) -> bool:
    return bool(
        isprime(centre - 1)
        and isprime(centre + 1)
    )


# ============================================================
# MAIN
# ============================================================

def main() -> None:
    print("=" * 92)
    print("SYMMETRIC-POWER METALLIC MEMORY TEST")
    print("=" * 92)

    base = gold_sequence(
        first=1,
        second=2,
        count=SEQUENCE_TERMS,
    )

    print("\nEXACT MEMORY GROWTH")
    print("-" * 92)
    print(
        "power | memory letters | lifted final row | "
        "scalar recurrence coefficients"
    )

    leading_ladder = []

    for degree in range(1, MAX_POWER + 1):
        memory_size = degree + 1
        matrix = lifted_gold_matrix(degree)
        final_row = matrix[-1]

        powered = tuple(
            value ** degree
            for value in base
        )

        coefficients = recurrence_coefficients(
            powered,
            order=memory_size,
        )

        leading_ladder.append(
            coefficients[0]
        )

        if not verify_lift(
            a=1,
            b=2,
            degree=degree,
        ):
            raise RuntimeError(
                f"lift failed for degree {degree}"
            )

        print(
            f"{degree:>5} | "
            f"{memory_size:>14} | "
            f"{str(final_row):>22} | "
            f"{coefficients}"
        )

    print("\nLEADING-COEFFICIENT LADDER")
    print("-" * 92)
    print(
        tuple(leading_ladder)
    )
    print(
        "This is the additive/metallic sequence:"
    )
    print(
        "1, 2, 3, 5, 8, 13"
    )

    print("\nTHE FIRST THREE LEVELS")
    print("-" * 92)

    square_coefficients = recurrence_coefficients(
        tuple(value ** 2 for value in base),
        order=3,
    )
    cube_coefficients = recurrence_coefficients(
        tuple(value ** 3 for value in base),
        order=4,
    )
    fourth_coefficients = recurrence_coefficients(
        tuple(value ** 4 for value in base),
        order=5,
    )

    print(
        "Gold / first power, 2 letters:"
    )
    print(
        "x[n] = x[n-1] + x[n-2]"
    )

    print(
        "\nSquare, 3 letters:"
    )
    print(
        f"s[n] = {signed_formula('s', square_coefficients)}"
    )
    print(
        "The new letter stores ab, and the coefficient 2 comes from:"
    )
    print(
        "(a+b)^2 = a^2 + 2ab + b^2"
    )

    print(
        "\nCube, 4 letters:"
    )
    print(
        f"c[n] = {signed_formula('c', cube_coefficients)}"
    )

    print(
        "\nFourth power, 5 letters:"
    )
    print(
        f"q[n] = {signed_formula('q', fourth_coefficients)}"
    )

    print("\nSQUARING VERSUS ADDING ONE MEMORY LETTER")
    print("-" * 92)
    print(
        "Raise power by one:"
    )
    print(
        "power 1 -> 2 -> 3 -> 4"
    )
    print(
        "memory 2 -> 3 -> 4 -> 5"
    )

    print(
        "\nSquare the entire current power:"
    )
    print(
        "power 1 -> 2 -> 4 -> 8"
    )
    print(
        "memory 2 -> 3 -> 5 -> 9"
    )

    print(
        "\nTherefore a 2 -> 3 -> 4 -> 5 word-length ladder "
        "corresponds to increasing the represented power one level "
        "at a time, not repeatedly squaring the entire lifted state."
    )

    print("\nCONNECTION TO THE FIVE-LETTER TWIN WORD")
    print("-" * 92)

    five_word = tuple(
        leading_ladder[:5]
    )
    five_word_squared = tuple(
        value * value
        for value in five_word
    )

    reset = CentreState(
        previous=4,
        current=16,
        centre=65_520,
    )

    first_state = apply_word(
        reset,
        five_word,
    )
    squared_state = apply_word(
        reset,
        five_word_squared,
    )

    print(
        f"five-letter ladder: "
        f"{five_word}"
    )
    print(
        f"componentwise square: "
        f"{five_word_squared}"
    )
    print(
        f"first doorway twin: "
        f"{twin_centre(first_state.centre)}"
    )
    print(
        f"squared doorway twin: "
        f"{twin_centre(squared_state.centre)}"
    )

    print("\nINTERPRETATION")
    print("-" * 92)
    print(
        "The +2 is not a correction to repeat at every later stage. "
        "It is the deterministic cross-term coefficient that first "
        "appears when the two-letter Gold state is lifted to squares."
    )
    print(
        "Once the extra cross-term memory letter exists, the lifted "
        "system evolves by its own fixed recurrence."
    )
    print(
        "At the next power, one additional monomial memory letter is "
        "opened and the leading coefficient becomes 3; then 5; then 8."
    )
    print(
        "This supplies a recursive reason for the word "
        "(1,2,3,5,8), independent of the primality audit."
    )
    print(
        "Prime validation is still needed to establish that a generated "
        "centre has prime boundaries, but it is no longer needed to "
        "choose the memory-length or the opening coefficient."
    )


if __name__ == "__main__":
    main()
