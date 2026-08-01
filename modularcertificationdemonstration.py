from math import isqrt


def primes_up_to(limit: int) -> list[int]:
    """Return all primes up to and including limit."""
    sieve = [True] * (limit + 1)
    sieve[0:2] = [False, False]

    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            for multiple in range(p * p, limit + 1, p):
                sieve[multiple] = False

    return [n for n, prime in enumerate(sieve) if prime]


def recursive_twin_test(N: int) -> tuple[list[tuple[int, int]], list[tuple[int, int]]]:
    """
    Follow the recursive prime-cycle closures through N
    and certify twin primes through N^2.
    """
    upper_bound = N * N
    maximum_m = (upper_bound - 1) // 6

    # Every later twin prime has the form 6m-1, 6m+1.
    surviving_centres = list(range(1, maximum_m + 1))

    # Mod 2 and mod 3 are already built into 6m±1.
    active_cycles = [p for p in primes_up_to(N) if p >= 5]

    history = [(0, len(surviving_centres))]

    for p in active_cycles:
        next_centres = []

        for m in surviving_centres:
            left = 6 * m - 1
            right = 6 * m + 1

            # A zero closes the address only when it is a later return.
            # left == p or right == p is the first winding of that cycle.
            left_closed = left % p == 0 and left > p
            right_closed = right % p == 0 and right > p

            if not left_closed and not right_closed:
                next_centres.append(m)

        surviving_centres = next_centres
        history.append((p, len(surviving_centres)))

    pairs = [(6 * m - 1, 6 * m + 1) for m in surviving_centres]

    # The exceptional pair (3,5) is not centred on a multiple of 6.
    if upper_bound >= 5:
        pairs.insert(0, (3, 5))

    return pairs, history


def ordinary_verification(limit: int) -> list[tuple[int, int]]:
    """Independent sieve used only to compare the final result."""
    sieve = [True] * (limit + 1)
    sieve[0:2] = [False, False]

    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            for multiple in range(p * p, limit + 1, p):
                sieve[multiple] = False

    return [
        (p, p + 2)
        for p in range(2, limit - 1)
        if sieve[p] and sieve[p + 2]
    ]


N = 100
pairs, history = recursive_twin_test(N)
verification = ordinary_verification(N * N)

print("Surviving centre counts:")
for cycle, count in history:
    label = "start" if cycle == 0 else f"mod {cycle}"
    print(f"{label:>7}: {count}")

print()
print("Pairs produced by recursive cycles:", len(pairs))
print("Pairs found by independent check:  ", len(verification))
print("Exact match:", pairs == verification)

print()
print("First ten pairs:")
print(pairs[:10])

print()
print("Last ten pairs:")
print(pairs[-10:])
