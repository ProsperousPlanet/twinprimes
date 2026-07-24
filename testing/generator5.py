#!/usr/bin/env python3
"""
Recursive Mod-Cycle Prime and Twin-Prime Generator

Construction:
    1. Begin with the unit 1 and the first completed cycle at 2.
    2. Every opened prime cycle has a next modular completion.
    3. A position reached by one or more existing cycles is composite.
    4. An untouched position opens a new cycle and is prime.
    5. Two consecutive prime openings separated by 2 form a twin-prime pair.
    6. When a prime cycle reaches p^2, it records a full self-cycle.
       For the higher 6n system, these begin at 5^2, then 7^2, and so on.
    7. Each full self-cycle can also advance the optional silver recurrence:
           next = previous + 2 * current

This program does not use:
    - a precomputed sieve table,
    - trial division,
    - an is_prime() function,
    - or one recursive call per active prime at every integer.

Instead, each cycle stores only its next completion. When several cycles
complete at the same integer, those completions are processed recursively.

Important:
    The silver recurrence is recorded as a parallel structural diagnostic.
    Prime/composite classification comes entirely from mod-cycle completions.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import sqrt
from sys import setrecursionlimit
from time import perf_counter


# ============================================================
# CONFIGURATION
# ============================================================

# Start with 1,000,000 for a quick test.
# Larger values such as 10,000,000 or 100,000,000 may take
# considerably longer because this version follows explicit cycle events.
MAX_INTEGER = 1_000_000

PRINT_EACH_PRIME = False
PRINT_EACH_TWIN = False
PRINT_PERFECT_CYCLES = False
PRINT_SILVER_STEPS = False

# Only affects unusually large groups of cycles completing together.
setrecursionlimit(100_000)


# ============================================================
# MOD-CYCLE MODEL
# ============================================================

@dataclass(slots=True)
class ModCycle:
    """One recursively opened modular cycle."""

    period: int
    next_completion: int
    multiple: int = 2


@dataclass(slots=True)
class SilverBalance:
    """
    Optional silver recurrence advanced at each full prime self-cycle.

        next = previous + 2 * current
    """

    previous: int = 1
    current: int = 1
    steps: int = 0

    def advance(self) -> tuple[int, int, float]:
        """Advance one silver-recurrence step."""
        new_value = self.previous + 2 * self.current
        self.previous, self.current = self.current, new_value
        self.steps += 1

        ratio = self.current / self.previous
        return self.previous, self.current, ratio


# ============================================================
# RECURSIVE MOD-CYCLE ENGINE
# ============================================================

class RecursiveModCycleGenerator:
    """
    Generate primes and twin primes from recursive mod-cycle completions.

    The integer loop is iterative so the bound can be large.
    Simultaneous cycle completions are propagated recursively.
    """

    def __init__(self, limit: int) -> None:
        if limit < 2:
            raise ValueError("MAX_INTEGER must be at least 2")

        self.limit = limit

        # One future event is stored for each active cycle.
        self.events: dict[int, list[ModCycle]] = {}

        self.prime_count = 0
        self.twin_count = 0
        self.previous_prime: int | None = None

        self.first_twin: tuple[int, int, int] | None = None
        self.last_twin: tuple[int, int, int] | None = None

        self.first_prime: int | None = None
        self.last_prime: int | None = None

        self.full_self_cycles = 0
        self.first_full_self_cycle: tuple[int, int] | None = None
        self.last_full_self_cycle: tuple[int, int] | None = None

        self.silver = SilverBalance()

    def schedule_cycle(self, cycle: ModCycle) -> None:
        """
        Store the next completion of one cycle.

        Only cycles with p^2 <= limit need to remain active for a finite
        run, because every composite <= limit has a prime factor <= sqrt(limit).
        """
        if cycle.next_completion <= self.limit:
            self.events.setdefault(
                cycle.next_completion,
                [],
            ).append(cycle)

    def open_prime_cycle(self, prime: int) -> None:
        """
        Record an untouched position as prime and open its mod cycle.

        A cycle larger than sqrt(limit) cannot be the smallest factor
        of any later composite within this finite run, so it is recorded
        as prime but does not need a scheduled completion.
        """
        self.prime_count += 1
        self.last_prime = prime

        if self.first_prime is None:
            self.first_prime = prime

        if PRINT_EACH_PRIME:
            print(f"{prime:,}: OPEN (prime cycle)")

        if (
            self.previous_prime is not None
            and prime - self.previous_prime == 2
        ):
            centre = self.previous_prime + 1
            twin = (
                self.previous_prime,
                centre,
                prime,
            )

            self.twin_count += 1
            self.last_twin = twin

            if self.first_twin is None:
                self.first_twin = twin

            if PRINT_EACH_TWIN:
                print(
                    f"TWIN: {twin[0]:,} : "
                    f"{twin[1]:,} : {twin[2]:,}"
                )

        self.previous_prime = prime

        # Only active cycles capable of being the smallest factor
        # of a later composite need to be scheduled.
        if prime * prime <= self.limit:
            self.schedule_cycle(
                ModCycle(
                    period=prime,
                    next_completion=2 * prime,
                    multiple=2,
                )
            )

    def record_full_self_cycle(
        self,
        cycle: ModCycle,
        integer: int,
    ) -> None:
        """
        Record the full self-cycle p^2.

        The higher twin-prime structure begins after 2 and 3, so the
        displayed perfect-cycle sequence begins at 5^2, then 7^2, etc.
        """
        if cycle.period < 5:
            return

        self.full_self_cycles += 1
        event = (cycle.period, integer)
        self.last_full_self_cycle = event

        if self.first_full_self_cycle is None:
            self.first_full_self_cycle = event

        if PRINT_PERFECT_CYCLES:
            print(
                f"FULL SELF-CYCLE: "
                f"{cycle.period:,}^2 = {integer:,}"
            )

        previous, current, ratio = self.silver.advance()

        if PRINT_SILVER_STEPS:
            print(
                f"  silver step {self.silver.steps}: "
                f"{previous:,}, {current:,}; "
                f"ratio={ratio:.12f}; "
                f"target={1 + sqrt(2):.12f}"
            )

    def process_completions_recursively(
        self,
        cycles: list[ModCycle],
        index: int,
        integer: int,
    ) -> None:
        """
        Recursively process every cycle completing at this integer.

        The recursion depth is only the number of simultaneous cycle
        completions at one position, rather than the total number of primes.
        """
        if index >= len(cycles):
            return

        cycle = cycles[index]

        # The p-th multiple of p is the full self-cycle p^2.
        if cycle.multiple == cycle.period:
            self.record_full_self_cycle(
                cycle,
                integer,
            )

        cycle.multiple += 1
        cycle.next_completion += cycle.period
        self.schedule_cycle(cycle)

        self.process_completions_recursively(
            cycles,
            index + 1,
            integer,
        )

    def run(self) -> None:
        """
        Count through the integer line.

        No completion event:
            the position is untouched and opens a prime cycle.

        One or more completion events:
            the position is composite.
        """
        for integer in range(2, self.limit + 1):
            completing_cycles = self.events.pop(
                integer,
                None,
            )

            if completing_cycles:
                self.process_completions_recursively(
                    completing_cycles,
                    0,
                    integer,
                )
                continue

            self.open_prime_cycle(integer)


# ============================================================
# OUTPUT
# ============================================================

def format_twin(
    twin: tuple[int, int, int] | None,
) -> str:
    if twin is None:
        return "none"

    left, centre, right = twin
    return f"{left:,} : {centre:,} : {right:,}"


def format_self_cycle(
    event: tuple[int, int] | None,
) -> str:
    if event is None:
        return "none"

    prime, square = event
    return f"{prime:,}^2 = {square:,}"


def main() -> None:
    print("=" * 72)
    print("RECURSIVE MOD-CYCLE PRIME AND TWIN-PRIME GENERATOR")
    print("=" * 72)
    print(f"Maximum integer: {MAX_INTEGER:,}")
    print()

    start = perf_counter()

    generator = RecursiveModCycleGenerator(
        MAX_INTEGER
    )
    generator.run()

    elapsed = perf_counter() - start

    print("\nSUMMARY")
    print("-" * 72)
    print(
        f"Maximum integer counted:    "
        f"{MAX_INTEGER:,}"
    )
    print(
        f"Prime cycles opened:        "
        f"{generator.prime_count:,}"
    )
    print(
        f"Twin-prime pairs:           "
        f"{generator.twin_count:,}"
    )
    print(
        f"First twin structure:       "
        f"{format_twin(generator.first_twin)}"
    )
    print(
        f"Last twin structure:        "
        f"{format_twin(generator.last_twin)}"
    )
    print(
        f"Full self-cycles from 5^2:  "
        f"{generator.full_self_cycles:,}"
    )
    print(
        f"First full self-cycle:      "
        f"{format_self_cycle(generator.first_full_self_cycle)}"
    )
    print(
        f"Last full self-cycle:       "
        f"{format_self_cycle(generator.last_full_self_cycle)}"
    )
    print(
        f"Silver recurrence steps:    "
        f"{generator.silver.steps:,}"
    )
    print(
        f"Elapsed time:               "
        f"{elapsed:.6f} seconds"
    )


if __name__ == "__main__":
    main()
