#!/usr/bin/env python3

from itertools import combinations
from functools import cache


PRIME_STAGES = (
    5, 7, 11, 13, 17, 19, 23, 29,
    31
)

SIMPLEX_ORDERS = (2, 3)


def cross(step, a, b):
    return (step * a) % b == (step * b) % a


@cache
def firstCrossStep(a, b):
    if a > b:
        a, b = b, a

    if a == b:
        return 1

    step = 1

    while not cross(step, a, b):
        step += 1

    return step


@cache
def simplexCross(state):
    if len(state) == 1:
        return state[0]

    left = simplexCross(state[:-1])
    right = simplexCross(state[1:])

    return left if left == right else firstCrossStep(left, right)


def clocksFromState(state):
    clocks = {
        simplexCross(group)
        for order in SIMPLEX_ORDERS
        for group in combinations(state, order)
    }

    return tuple(sorted(p for p in clocks if p >= 5))


def blocked(center, p):
    return (
        (center % p == 1 or center % p == p - 1)
        and center - 1 != p
        and center + 1 != p
    )


def clockOK(center, clocks):
    return all(not blocked(center, p) for p in clocks)


def buildLevel(start, clocks, p):
    centers = []
    center = start

    while len(centers) < p:
        if clockOK(center, clocks):
            centers.append(center)

        center += 6

    return tuple(centers)


def nextState(state, p):
    clocks = clocksFromState(state)

    return buildLevel(
        state[-1],
        clocks,
        p
    )


def run():
    state = buildLevel(6, (5,), 5)
    print(5, state)

    state = buildLevel(state[-1], (5, 7), 7)
    print(7, state)

    for p in PRIME_STAGES[2:]:
        state = nextState(state, p)
        print(p, state)


if __name__ == "__main__":
    run()
