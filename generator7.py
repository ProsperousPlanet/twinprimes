#!/usr/bin/env python3
"""
Recursive Twin-Centre Mod-Cycle Generator

This program works directly on the possible twin-prime centres

    centre = 6n
    left   = 6n - 1
    right  = 6n + 1

It does not count every integer and it does not keep a table of all
blocked addresses.

Recursive rule
--------------
1. Begin with the first 6-centre. Its boundaries are 5 and 7.
2. An open boundary is prime and opens a new mod cycle.
3. Each opened prime cycle creates two repeating streams in centre space:
       - positions where it blocks a left boundary,
       - positions where it blocks a right boundary.
4. At each centre, recursively process every cycle completing there.
5. If neither side is blocked, the centre is a twin-prime centre.
6. If only one side is open, that prime still opens its future cycles,
   because singleton primes can block later twin-prime centres.

This is equivalent in result to sieving the two residue classes 6n-1
and 6n+1, but it is implemented as recursively propagated mod counters.
Only the next completion of each active side-cycle is retained.

Small-number finding
--------------------
The first failure at centre 24 is caused by

    24 + 1 = 25 = 5^2.

However, the next mod-5 failure is already

    36 - 1 = 35 = 5 * 7,

before 5^3 appears. Therefore prime powers are visible landmarks, but
they are not the complete branching rule: every repeated multiple of
an opened prime cycle must be propagated.

Powers of 5 alternate sides:

    5^2 = 25   -> right boundary of centre 24
    5^3 = 125  -> left boundary of centre 126
    5^4 = 625  -> right boundary of centre 624

but mixed products occur between them.

No primality-testing function, trial division, fixed prime list, or
full integer sieve array is used.
"""

from __future__ import annotations

from dataclasses import dataclass
from sys import setrecursionlimit
from time import perf_counter


# ============================================================
# CONFIGURATION
# ============================================================

# Both numbers in a twin-prime pair must be <= MAX_NUMBER.
MAX_NUMBER = 100_000_000

PRINT_EACH_TWIN = False
PRINT_EACH_OPEN_BOUNDARY = False
SHOW_SMALL_PATTERN = True

# Recursion depth is only the number of simultaneous cycle events
# at one centre, not the number of primes or centres.
setrecursionlimit(100_000)


# ============================================================
# BIT FLAGS
# ============================================================

LEFT = 0b01
RIGHT = 0b10


# ============================================================
# CYCLE EVENT
# ============================================================

@dataclass(slots=True)
class CycleEvent:
    """
    One side of one prime's repeating centre-space mod cycle.

    Every time the event occurs, it is moved forward by `period`
    centre positions.
    """

    period: int
    side: int


# ============================================================
# RECURSIVE CENTRE SYSTEM
# ============================================================

class RecursiveTwinCentres:
    """
    Generate all prime openings on the two 6n boundaries.

    The event dictionary retains only future cycle completions.
    Blocked centre addresses are removed as soon as they are processed.
    """

    def __init__(self, max_number: int) -> None:
        if max_number < 5:
            raise ValueError("MAX_NUMBER must be at least 5")

        self.max_number = max_number

        # Largest n for which 6n+1 <= MAX_NUMBER.
        self.max_centre_index = (max_number - 1) // 6

        # centre_index -> list of cycles completing there
        self.events: dict[int, list[CycleEvent]] = {}

        # 2 and 3 are outside the two 6n boundary streams.
        self.prime_count = 2

        # Exceptional pair (3,5), centred on 4.
        self.twin_count = 1
        self.first_twin = (3, 4, 5)
        self.last_twin = (3, 4, 5)

        self.left_openings = 0
        self.right_openings = 0
        self.active_prime_cycles = 0
        self.processed_cycle_events = 0

        self.first_blocked_centre: tuple[int, int] | None = None

    def schedule(
        self,
        centre_index: int,
        period: int,
        side: int,
    ) -> None:
        """Schedule one future left/right blocking completion."""
        if centre_index > self.max_centre_index:
            return

        self.events.setdefault(
            centre_index,
            [],
        ).append(
            CycleEvent(
                period=period,
                side=side,
            )
        )

    def open_boundary_cycle(
        self,
        prime: int,
        side: int,
        centre_index: int,
    ) -> None:
        """
        Open the two centre-space event streams created by one prime.

        Suppose p opens on one boundary at centre index n.

        The same boundary is reached again after p centre steps.

        The opposite boundary's first residue occurs at p-n.
        Both streams then repeat every p centre positions.
        """
        self.prime_count += 1

        if side == LEFT:
            self.left_openings += 1
        else:
            self.right_openings += 1

        if PRINT_EACH_OPEN_BOUNDARY:
            side_name = "left" if side == LEFT else "right"
            print(
                f"prime {prime:,} opened on the {side_name} "
                f"of centre {6 * centre_index:,}"
            )

        # For a finite run, a prime larger than sqrt(MAX_NUMBER)
        # cannot be the smallest factor of a later composite.
        if prime * prime > self.max_number:
            return

        self.active_prime_cycles += 1

        same_side_first = centre_index + prime
        opposite_side_first = prime - centre_index
        opposite_side = RIGHT if side == LEFT else LEFT

        self.schedule(
            same_side_first,
            prime,
            side,
        )
        self.schedule(
            opposite_side_first,
            prime,
            opposite_side,
        )

    def process_events_recursively(
        self,
        event_list: list[CycleEvent],
        index: int,
        centre_index: int,
        blocked_mask: int = 0,
    ) -> int:
        """
        Recursively process all cycle completions at one centre.

        The returned two-bit mask records which boundaries are blocked:
            00 -> neither
            01 -> left
            10 -> right
            11 -> both
        """
        if index >= len(event_list):
            return blocked_mask

        event = event_list[index]
        self.processed_cycle_events += 1

        blocked_mask |= event.side

        # Continue this side-cycle to its next completion.
        self.schedule(
            centre_index + event.period,
            event.period,
            event.side,
        )

        return self.process_events_recursively(
            event_list,
            index + 1,
            centre_index,
            blocked_mask,
        )

    def count_centre(self, centre_index: int) -> None:
        """Process one generated centre 6n."""
        centre = 6 * centre_index
        left = centre - 1
        right = centre + 1

        event_list = self.events.pop(
            centre_index,
            None,
        )

        if event_list is None:
            blocked_mask = 0
        else:
            blocked_mask = self.process_events_recursively(
                event_list,
                0,
                centre_index,
            )

        left_open = not (blocked_mask & LEFT)
        right_open = not (blocked_mask & RIGHT)

        # Every open boundary is prime and must create its future cycles,
        # even when the opposite boundary is blocked.
        if left_open:
            self.open_boundary_cycle(
                left,
                LEFT,
                centre_index,
            )

        if right_open and right <= self.max_number:
            self.open_boundary_cycle(
                right,
                RIGHT,
                centre_index,
            )

        if (
            left_open
            and right_open
            and right <= self.max_number
        ):
            self.twin_count += 1
            self.last_twin = (
                left,
                centre,
                right,
            )

            if PRINT_EACH_TWIN:
                print(
                    f"{left:,} : {centre:,} : {right:,}"
                )

        elif (
            self.first_blocked_centre is None
            and centre_index > 1
        ):
            self.first_blocked_centre = (
                centre,
                blocked_mask,
            )

    def run(self) -> None:
        """Continue the recursive centre count to MAX_NUMBER."""
        for centre_index in range(
            1,
            self.max_centre_index + 1,
        ):
            self.count_centre(centre_index)


# ============================================================
# SMALL-PATTERN DIAGNOSTIC
# ============================================================

def show_small_pattern() -> None:
    """
    Show why prime powers alone cannot control the recursion.
    """
    print("\nSMALL MOD-5 PATTERN")
    print("-" * 72)
    print("24 + 1 = 25  = 5^2       first mod-5 square blockage")
    print("36 - 1 = 35  = 5 * 7     next blockage, before 5^3")
    print("54 + 1 = 55  = 5 * 11")
    print("66 - 1 = 65  = 5 * 13")
    print("84 + 1 = 85  = 5 * 17")
    print("96 - 1 = 95  = 5 * 19")
    print("126 - 1 = 125 = 5^3       odd power returns on the left")
    print("624 + 1 = 625 = 5^4       even power returns on the right")
    print()
    print(
        "Conclusion: squares and cubes mark self-completions, "
        "but the full mod cycle blocks two repeating centre residues."
    )


# ============================================================
# OUTPUT
# ============================================================

def blocked_description(mask: int) -> str:
    if mask == LEFT:
        return "left boundary"
    if mask == RIGHT:
        return "right boundary"
    if mask == LEFT | RIGHT:
        return "both boundaries"
    return "neither boundary"


def main() -> None:
    print("=" * 72)
    print("RECURSIVE TWIN-CENTRE MOD-CYCLE GENERATOR")
    print("=" * 72)
    print(f"Maximum integer: {MAX_NUMBER:,}")
    print("Centre unit:     6n")
    print("Boundary bits:   LEFT=01, RIGHT=10")

    if SHOW_SMALL_PATTERN:
        show_small_pattern()

    start = perf_counter()

    system = RecursiveTwinCentres(
        MAX_NUMBER
    )
    system.run()

    elapsed = perf_counter() - start

    print("\nSUMMARY")
    print("-" * 72)
    print(
        f"6n centres processed:       "
        f"{system.max_centre_index:,}"
    )
    print(
        f"Prime boundary openings:    "
        f"{system.prime_count:,}"
    )
    print(
        f"Twin-prime pairs:           "
        f"{system.twin_count:,}"
    )
    print(
        f"First twin structure:       "
        f"{system.first_twin[0]:,} : "
        f"{system.first_twin[1]:,} : "
        f"{system.first_twin[2]:,}"
    )
    print(
        f"Last twin structure:        "
        f"{system.last_twin[0]:,} : "
        f"{system.last_twin[1]:,} : "
        f"{system.last_twin[2]:,}"
    )
    print(
        f"Active small-prime cycles:  "
        f"{system.active_prime_cycles:,}"
    )
    print(
        f"Cycle events processed:     "
        f"{system.processed_cycle_events:,}"
    )

    if system.first_blocked_centre is not None:
        centre, mask = system.first_blocked_centre
        print(
            f"First blocked 6n centre:    "
            f"{centre:,} "
            f"({blocked_description(mask)})"
        )

    print(
        f"Pending event addresses:    "
        f"{len(system.events):,}"
    )
    print(
        f"Elapsed time:               "
        f"{elapsed:.6f} seconds"
    )


if __name__ == "__main__":
    main()
