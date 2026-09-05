#!/usr/bin/env python3

from math import gcd, isqrt
import sys


# --------------------------------------------------
# PRIME LOADER
# --------------------------------------------------

def primes_up_to(n):

    if n < 2:
        return []

    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"

    for p in range(2, isqrt(n) + 1):

        if sieve[p]:

            sieve[p * p:n + 1:p] = (
                b"\x00"
                * (((n - p * p) // p) + 1)
            )

    return [
        p
        for p in range(2, n + 1)
        if sieve[p]
    ]


# --------------------------------------------------
# DIRECT CARRY
# --------------------------------------------------

def carry(c, M, p, limit):

    assert gcd(M, p) == 1

    inverse = pow(M, -1, p)

    plus = ((1 - c) * inverse) % p
    minus = ((-1 - c) * inverse) % p

    max_k = min(
        p - 1,
        (limit - c) // M
    )

    return [
        c + k * M
        for k in range(max_k + 1)
        if k not in (plus, minus)
    ]


# --------------------------------------------------
# BUILD OPEN STATES
# --------------------------------------------------

def build_states(limit):

    M = 6
    states = [0]

    for p in primes_up_to(
        isqrt(limit + 1)
    ):

        if p <= 3:
            continue

        new_states = []

        for c in states:

            new_states.extend(
                carry(
                    c,
                    M,
                    p,
                    limit
                )
            )

        states = new_states
        M *= p


    if M <= limit:

        expanded = []

        for c in states:

            k = 0

            while c + k * M <= limit:

                expanded.append(
                    c + k * M
                )

                k += 1

        states = expanded


    return sorted(states)


# --------------------------------------------------
# GENERATE ONE PRIME LEVEL
# --------------------------------------------------

def next_level(start, amount):

    needed = amount - 1

    # Begin close to the inherited center.
    # Expand only if more carried states are required.

    limit = start + 6 * amount


    while True:

        candidates = [
            value
            for value in build_states(limit)
            if value > start
        ]


        if len(candidates) >= needed:

            return (
                [start]
                + candidates[:needed]
            )


        limit *= 2


# --------------------------------------------------
# GENERATE ALL PRIME LEVELS
# --------------------------------------------------

def generate_levels(max_stage):

    prime_stages = [
        p
        for p in primes_up_to(max_stage)
        if p >= 5
    ]


    if not prime_stages:
        return []


    levels = []

    # The only seed:
    #
    # 2 and 3 first complete at 6.

    start = 6


    for p in prime_stages:

        current_level = next_level(
            start,
            p
        )

        levels.append(
            (
                p,
                current_level
            )
        )


        print(
            "LEVEL",
            p
        )

        print(
            current_level,
            flush=True
        )

        print()


        start = current_level[-1]


    return levels


# --------------------------------------------------
# RUN
# --------------------------------------------------

def main():

    if len(sys.argv) > 1:

        max_stage = int(
            sys.argv[1]
        )

    else:

        max_stage = int(
            input(
                "Generate prime levels through: "
            )
        )


    if max_stage < 5:

        print(
            "Enter a value of at least 5."
        )

        return


    print()

    generate_levels(
        max_stage
    )


if __name__ == "__main__":
    main()
