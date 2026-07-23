#!/usr/bin/env python3
"""
Large-Integer Recursive Golden-Silver Twin-Centre Explorer

Generator
---------
The centre generator uses only the recursive counter rules

    Golden: next = previous + current
    Silver: next = previous + 2 * current

with

    child centre = parent centre * next period.

The seed state is

    previous = 2
    current  = 3
    centre   = 6.

There is no maximum centre. Python integers grow automatically.

Verification
------------
The generator and validator are deliberately separate.

When VERIFY_CENTRES is True, SymPy checks centre - 1 and centre + 1.
Below 2^64 SymPy's result is deterministic. Above 2^64 SymPy uses a
Baillie-PSW probable-prime test; no counterexample is known, but this
is not a proof certificate.

When VERIFY_CENTRES is False, the program performs pure recursive
generation and reports candidate centres without calling them primes.

Memory
------
The search is depth-first. It does not store blocked centres or the
integer line. By default it retains only summary counters and the
largest successful centre.

Scaling
-------
A complete binary search through depth d visits

    2^(d + 1) - 1

states. The number of branches, not the size of the integers, becomes
the main cost.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from time import perf_counter

try:
    from sympy import isprime, primerange
except ImportError as exc:
    raise SystemExit(
        "This file needs SymPy for optional boundary verification.\n"
        "Install it with:\n"
        "    python3 -m pip install sympy"
    ) from exc


# ============================================================
# CONFIGURATION
# ============================================================

# Increase gradually:
#   14 -> 32,767 generated states
#   16 -> 131,071 generated states
#   18 -> 524,287 generated states
#   20 -> 2,097,151 generated states
MAX_DEPTH = 16

# True:
#   test the two boundaries of each generated centre.
# False:
#   generate centres only, with no primality claim.
VERIFY_CENTRES = True

# Reject obvious failures using small prime residues before calling
# the larger primality test. This stores no blocked addresses and
# does not record which side failed.
USE_SMALL_BLOCK_FILTER = True
SMALL_BLOCK_FILTER_LIMIT = 200

# Search promising branches first. This does not remove either branch.
# A period that contributes a new factor coprime to the parent centre
# is explored before a period containing only already-present factors.
PRIORITIZE_NEW_FACTORS = True

# Printing can dominate runtime. Record mode prints only a newly largest
# verified twin centre.
PRINT_RECORD_TWINS = True
PRINT_ALL_TWINS = False

# False uses essentially constant result-storage memory.
KEEP_ALL_HITS = False


# ============================================================
# CONSTANTS
# ============================================================

UINT64_LIMIT = 1 << 64

SMALL_FILTER_PRIMES = tuple(
    primerange(
        5,
        SMALL_BLOCK_FILTER_LIMIT + 1,
    )
)


# ============================================================
# DATA
# ============================================================

@dataclass(slots=True)
class SearchStats:
    states_generated: int = 0
    small_filter_rejections: int = 0
    boundary_checks: int = 0
    twin_hits: int = 0
    exact_64bit_hits: int = 0
    probable_bigint_hits: int = 0


@dataclass(frozen=True, slots=True)
class TwinHit:
    centre: int
    depth: int
    path_bits: int
    previous_period: int
    current_period: int


@dataclass(frozen=True, slots=True)
class ChildState:
    previous: int
    current: int
    centre: int
    depth: int
    path_bits: int
    new_factor_part: int


# ============================================================
# VALIDATION HELPERS
# ============================================================

def blocked_by_small_prime(centre: int) -> bool:
    """
    Return only a boolean: at least one boundary has a small factor.

    The program deliberately does not retain which side was blocked.
    """
    left = centre - 1
    right = centre + 1

    for prime in SMALL_FILTER_PRIMES:
        if left != prime and left % prime == 0:
            return True

        if right != prime and right % prime == 0:
            return True

    return False


def is_verified_twin_centre(
    centre: int,
    stats: SearchStats,
) -> bool:
    """Validate one sparse centre, short-circuiting on failure."""
    if USE_SMALL_BLOCK_FILTER and blocked_by_small_prime(centre):
        stats.small_filter_rejections += 1
        return False

    stats.boundary_checks += 1

    # Python's `and` short-circuits: the right side is checked only
    # when the left side passes.
    return (
        bool(isprime(centre - 1))
        and bool(isprime(centre + 1))
    )


def coprime_new_part(
    period: int,
    centre: int,
) -> int:
    """
    Remove every factor from `period` that is already present in `centre`.

    A result of 1 means the new period contributes no new distinct
    prime divisor to the completed centre. This is used only to order
    the search, never to discard a branch.
    """
    remaining = period

    while True:
        common = gcd(
            remaining,
            centre,
        )

        if common == 1:
            return remaining

        remaining //= common


# ============================================================
# RECURSIVE EXPLORER
# ============================================================

class GoldenSilverBigIntExplorer:

    def __init__(self, max_depth: int) -> None:
        if max_depth < 0:
            raise ValueError("MAX_DEPTH must be non-negative")

        self.max_depth = max_depth
        self.stats = SearchStats()

        self.largest_hit: TwinHit | None = None
        self.first_hit: TwinHit | None = None

        self.hits: list[TwinHit] = []
        self.seen_hit_centres: set[int] = set()

    @staticmethod
    def path_string(
        path_bits: int,
        depth: int,
    ) -> str:
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
        self.stats.states_generated += 1

        if not VERIFY_CENTRES:
            return

        if not is_verified_twin_centre(
            centre,
            self.stats,
        ):
            return

        if centre in self.seen_hit_centres:
            return

        self.seen_hit_centres.add(centre)
        self.stats.twin_hits += 1

        if centre + 1 < UINT64_LIMIT:
            self.stats.exact_64bit_hits += 1
        else:
            self.stats.probable_bigint_hits += 1

        hit = TwinHit(
            centre=centre,
            depth=depth,
            path_bits=path_bits,
            previous_period=previous,
            current_period=current,
        )

        if self.first_hit is None:
            self.first_hit = hit

        is_new_record = (
            self.largest_hit is None
            or centre > self.largest_hit.centre
        )

        if is_new_record:
            self.largest_hit = hit

        if KEEP_ALL_HITS:
            self.hits.append(hit)

        if PRINT_ALL_TWINS or (
            PRINT_RECORD_TWINS
            and is_new_record
        ):
            path = self.path_string(
                path_bits,
                depth,
            )

            guarantee = (
                "exact-under-2^64"
                if centre + 1 < UINT64_LIMIT
                else "probable-bigint"
            )

            print(
                f"{centre - 1:,} : "
                f"{centre:,} : "
                f"{centre + 1:,}  "
                f"path={path}  "
                f"depth={depth}  "
                f"[{guarantee}]"
            )

    def make_children(
        self,
        previous: int,
        current: int,
        centre: int,
        depth: int,
        path_bits: int,
    ) -> tuple[ChildState, ChildState]:
        golden_period = previous + current
        silver_period = previous + 2 * current

        golden = ChildState(
            previous=current,
            current=golden_period,
            centre=centre * golden_period,
            depth=depth + 1,
            path_bits=path_bits << 1,
            new_factor_part=coprime_new_part(
                golden_period,
                centre,
            ),
        )

        silver = ChildState(
            previous=current,
            current=silver_period,
            centre=centre * silver_period,
            depth=depth + 1,
            path_bits=(path_bits << 1) | 1,
            new_factor_part=coprime_new_part(
                silver_period,
                centre,
            ),
        )

        return golden, silver

    def explore(
        self,
        previous: int,
        current: int,
        centre: int,
        depth: int = 0,
        path_bits: int = 0,
    ) -> None:
        """Recursive depth-first exploration of the G/S tree."""
        self.record_candidate(
            previous,
            current,
            centre,
            depth,
            path_bits,
        )

        if depth >= self.max_depth:
            return

        golden, silver = self.make_children(
            previous,
            current,
            centre,
            depth,
            path_bits,
        )

        if PRIORITIZE_NEW_FACTORS:
            children = sorted(
                (golden, silver),
                key=lambda child: (
                    child.new_factor_part != 1,
                    child.new_factor_part,
                ),
                reverse=True,
            )
        else:
            children = (
                golden,
                silver,
            )

        for child in children:
            self.explore(
                previous=child.previous,
                current=child.current,
                centre=child.centre,
                depth=child.depth,
                path_bits=child.path_bits,
            )

    def run(self) -> None:
        self.explore(
            previous=2,
            current=3,
            centre=6,
        )


# ============================================================
# OUTPUT
# ============================================================

def main() -> None:
    expected_states = (
        1 << (MAX_DEPTH + 1)
    ) - 1

    print("=" * 80)
    print("LARGE-INTEGER RECURSIVE GOLDEN-SILVER TWIN-CENTRE EXPLORER")
    print("=" * 80)
    print(f"Maximum depth:            {MAX_DEPTH}")
    print(f"Expected generated states:{expected_states:>20,}")
    print(f"Verify boundaries:        {VERIFY_CENTRES}")
    print(f"Small boolean filter:     {USE_SMALL_BLOCK_FILTER}")
    print(f"Retain all hits:          {KEEP_ALL_HITS}")
    print("Maximum centre:           none (Python arbitrary integers)")
    print()

    start = perf_counter()

    explorer = GoldenSilverBigIntExplorer(
        MAX_DEPTH
    )
    explorer.run()

    elapsed = perf_counter() - start

    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(
        f"States generated:          "
        f"{explorer.stats.states_generated:,}"
    )
    print(
        f"Small-filter rejections:   "
        f"{explorer.stats.small_filter_rejections:,}"
    )
    print(
        f"Boundary validation calls: "
        f"{explorer.stats.boundary_checks:,}"
    )
    print(
        f"Unique twin hits:          "
        f"{explorer.stats.twin_hits:,}"
    )
    print(
        f"Exact hits below 2^64:     "
        f"{explorer.stats.exact_64bit_hits:,}"
    )
    print(
        f"Probable hits above 2^64:  "
        f"{explorer.stats.probable_bigint_hits:,}"
    )

    if explorer.largest_hit is not None:
        hit = explorer.largest_hit
        path = explorer.path_string(
            hit.path_bits,
            hit.depth,
        )

        print(
            f"Largest centre digits:     "
            f"{len(str(hit.centre)):,}"
        )
        print(
            f"Largest twin structure:    "
            f"{hit.centre - 1:,} : "
            f"{hit.centre:,} : "
            f"{hit.centre + 1:,}"
        )
        print(
            f"Largest path:              "
            f"{path}"
        )

    print(
        f"Elapsed time:               "
        f"{elapsed:.6f} seconds"
    )

    if explorer.stats.probable_bigint_hits:
        print(
            "\nWarning: results above 2^64 are strong probable-prime "
            "results, not primality certificates."
        )


if __name__ == "__main__":
    main()
