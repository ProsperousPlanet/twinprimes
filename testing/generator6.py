#!/usr/bin/env python3
"""
Recursive Golden-Silver Twin-Centre Explorer

Purpose
-------
Generate a sparse tree of possible twin-prime centres directly from the
two recursive counter rules:

    Golden step: next = previous + current
    Silver step: next = previous + 2 * current

The seed counter periods are 2 and 3, whose first full completion is:

    centre = 2 * 3 = 6

Each new counter sits above the completed stack beneath it, so a child
centre is:

    child_centre = parent_centre * next_period

Examples along the all-golden branch:

    6
    6 * 5   = 30
    30 * 8  = 240
    240 * 13 = 3120
    3120 * 21 = 65520

The explorer uses a recursive depth-first walk. A path is stored as bits:

    0 = golden step
    1 = silver step

It does NOT:
    - construct a Sieve of Eratosthenes,
    - store every integer,
    - store blocked addresses,
    - generate a list of all primes,
    - or scan every 6n centre.

It tests only the two boundaries of each recursively generated centre.
For exact checking, the included Miller-Rabin test is deterministic for
all unsigned 64-bit integers.

Important mathematical limitation
---------------------------------
This experiment generates a sparse subset of twin-prime centres. It does
not currently generate every twin-prime centre and does not prove that
infinitely many branches survive. Its purpose is to test the proposed
golden-silver centre recursion using very little memory.
"""

from __future__ import annotations

from dataclasses import dataclass
from time import perf_counter


# ============================================================
# CONFIGURATION
# ============================================================

# Number of golden/silver branch decisions below the seed centre 6.
MAX_DEPTH = 10

# The primality test is exact up to this limit.
MAX_CENTER = (1 << 64) - 1

# Show every candidate centre, including blocked ones.
PRINT_ALL_CANDIDATES = False

# Show each twin-prime centre when it is found.
PRINT_TWIN_CENTRES = True

# Retain only successful twin centres so they can be summarized later.
# Blocked centres are never retained.
KEEP_TWIN_CENTRES = True


# ============================================================
# EXACT 64-BIT PRIMALITY CHECK
# ============================================================

_SMALL_PRIMES = (
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37
)

# These bases make Miller-Rabin deterministic for n < 2^64.
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
    """
    Return True exactly when an unsigned 64-bit integer is prime.

    This is used only to validate the two boundaries of a sparse,
    recursively generated centre. It is not a sieve.
    """
    if number < 2:
        return False

    for prime in _SMALL_PRIMES:
        if number % prime == 0:
            return number == prime

    # Write number - 1 as d * 2^s with d odd.
    d = number - 1
    s = 0

    while d % 2 == 0:
        d //= 2
        s += 1

    for base in _MR_BASES_64:
        if base % number == 0:
            continue

        value = pow(base, d, number)

        if value == 1 or value == number - 1:
            continue

        for _ in range(s - 1):
            value = pow(value, 2, number)

            if value == number - 1:
                break
        else:
            return False

    return True


def is_twin_centre(centre: int) -> bool:
    """Return True when centre - 1 and centre + 1 are both prime."""
    return (
        is_prime_64(centre - 1)
        and is_prime_64(centre + 1)
    )


# ============================================================
# RECURSIVE BRANCH MODEL
# ============================================================

@dataclass(slots=True)
class SearchStats:
    """Small counters only; blocked addresses are not stored."""

    candidates_tested: int = 0
    branches_pruned: int = 0
    twin_hits: int = 0


@dataclass(frozen=True, slots=True)
class TwinHit:
    """One successful sparse twin-centre result."""

    centre: int
    depth: int
    path_bits: int
    previous_period: int
    current_period: int


class GoldenSilverExplorer:
    """
    Recursively explore both counter rules using depth-first search.

    Only the current branch state is held during recursion, so working
    memory grows with depth rather than with the size of the number line.
    """

    def __init__(
        self,
        max_depth: int,
        max_center: int,
    ) -> None:
        if max_depth < 0:
            raise ValueError("MAX_DEPTH must be non-negative")

        if max_center < 6:
            raise ValueError("MAX_CENTER must be at least 6")

        if max_center >= 1 << 64:
            raise ValueError(
                "MAX_CENTER must be below 2^64 for exact validation"
            )

        self.max_depth = max_depth
        self.max_center = max_center
        self.stats = SearchStats()

        # Only successful centres are optionally retained.
        self.hits: list[TwinHit] = []
        self.seen_hit_centres: set[int] = set()

        self.first_hit: TwinHit | None = None
        self.last_hit: TwinHit | None = None

        self.candidates_by_depth = [0] * (max_depth + 1)
        self.hits_by_depth = [0] * (max_depth + 1)

    @staticmethod
    def path_string(
        path_bits: int,
        depth: int,
    ) -> str:
        """Convert bit decisions into a G/S path."""
        if depth == 0:
            return "ROOT"

        binary = format(
            path_bits,
            f"0{depth}b",
        )

        return binary.translate(
            str.maketrans({
                "0": "G",
                "1": "S",
            })
        )

    def record_candidate(
        self,
        previous: int,
        current: int,
        centre: int,
        depth: int,
        path_bits: int,
    ) -> None:
        """Test one generated centre without retaining failures."""
        self.stats.candidates_tested += 1
        self.candidates_by_depth[depth] += 1

        twin = is_twin_centre(centre)
        path = self.path_string(path_bits, depth)

        if PRINT_ALL_CANDIDATES:
            status = "TWIN" if twin else "blocked"
            print(
                f"depth={depth:>2} "
                f"path={path:<12} "
                f"periods=({previous}, {current}) "
                f"centre={centre:,} "
                f"{status}"
            )

        if not twin:
            return

        # Different paths can theoretically reach the same centre.
        # Count and store each successful centre only once.
        if centre in self.seen_hit_centres:
            return

        self.seen_hit_centres.add(centre)
        self.stats.twin_hits += 1
        self.hits_by_depth[depth] += 1

        hit = TwinHit(
            centre=centre,
            depth=depth,
            path_bits=path_bits,
            previous_period=previous,
            current_period=current,
        )

        if self.first_hit is None:
            self.first_hit = hit

        self.last_hit = hit

        if KEEP_TWIN_CENTRES:
            self.hits.append(hit)

        if PRINT_TWIN_CENTRES:
            print(
                f"TWIN  depth={depth:>2} "
                f"path={path:<12} "
                f"centre={centre:,}  "
                f"pair=({centre - 1:,}, {centre + 1:,})"
            )

    def explore(
        self,
        previous: int,
        current: int,
        centre: int,
        depth: int = 0,
        path_bits: int = 0,
    ) -> None:
        """
        Recursively visit one branch state and then its G/S children.

        Failed centres are not stored, but their branches are still
        explored because a later completion can become a twin centre.
        """
        self.record_candidate(
            previous,
            current,
            centre,
            depth,
            path_bits,
        )

        if depth >= self.max_depth:
            return

        # Bit 0: golden step.
        golden_period = previous + current
        golden_centre = centre * golden_period

        if golden_centre <= self.max_center:
            self.explore(
                previous=current,
                current=golden_period,
                centre=golden_centre,
                depth=depth + 1,
                path_bits=path_bits << 1,
            )
        else:
            self.stats.branches_pruned += 1

        # Bit 1: silver step.
        silver_period = previous + 2 * current
        silver_centre = centre * silver_period

        if silver_centre <= self.max_center:
            self.explore(
                previous=current,
                current=silver_period,
                centre=silver_centre,
                depth=depth + 1,
                path_bits=(path_bits << 1) | 1,
            )
        else:
            self.stats.branches_pruned += 1

    def run(self) -> None:
        """Begin with periods 2 and 3 at the completed centre 6."""
        self.explore(
            previous=2,
            current=3,
            centre=6,
        )


# ============================================================
# OUTPUT
# ============================================================

def main() -> None:
    print("=" * 76)
    print("RECURSIVE GOLDEN-SILVER TWIN-CENTRE EXPLORER")
    print("=" * 76)
    print("Seed periods:     2, 3")
    print("Seed centre:      6")
    print("Golden bit:       0  -> previous + current")
    print("Silver bit:       1  -> previous + 2 * current")
    print(f"Maximum depth:    {MAX_DEPTH}")
    print(f"Maximum centre:   {MAX_CENTER:,}")
    print()

    start = perf_counter()

    explorer = GoldenSilverExplorer(
        max_depth=MAX_DEPTH,
        max_center=MAX_CENTER,
    )
    explorer.run()

    elapsed = perf_counter() - start

    print("\n" + "=" * 76)
    print("SUMMARY")
    print("=" * 76)
    print(
        f"Candidate centres tested:  "
        f"{explorer.stats.candidates_tested:,}"
    )
    print(
        f"Branches pruned by bound:  "
        f"{explorer.stats.branches_pruned:,}"
    )
    print(
        f"Unique twin centres found: "
        f"{explorer.stats.twin_hits:,}"
    )
    print(
        f"Elapsed time:              "
        f"{elapsed:.6f} seconds"
    )

    print("\nHits by depth:")
    for depth, count in enumerate(explorer.hits_by_depth):
        if count:
            print(f"  depth {depth:>2}: {count:,}")

    if KEEP_TWIN_CENTRES and explorer.hits:
        print("\nTwin centres in numerical order:")

        for hit in sorted(
            explorer.hits,
            key=lambda item: item.centre,
        ):
            path = explorer.path_string(
                hit.path_bits,
                hit.depth,
            )

            print(
                f"  {hit.centre - 1:,} : "
                f"{hit.centre:,} : "
                f"{hit.centre + 1:,}  "
                f"path={path}"
            )

    print(
        "\nNote: this is a sparse branch experiment, "
        "not a generator of every twin-prime pair."
    )


if __name__ == "__main__":
    main()
