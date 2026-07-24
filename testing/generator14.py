#!/usr/bin/env python3
"""
RECURSIVE PRIME CYCLES WITH METALLIC TWIN ADDRESSES

Goal
----
Generate every prime up to N through recursively advancing composite
cycles, detect every twin-prime pair from consecutive prime openings,
and assign each twin centre a compact three-bit metallic address.

This program does NOT:
    - allocate a Boolean array of length N,
    - test each integer by trial division,
    - test both sides of every 6n centre,
    - retain every blocked address,
    - or search a G/S/B branch tree.

Prime generation
----------------
When an odd number p is reached by no active cycle, it is a new prime.

That prime opens one future composite cycle:

    first completion = p^2
    cycle step       = 2p

Only the next completion of each active prime cycle is retained.
When a completion is reached, that cycle recursively advances to its
next unoccupied completion.

This is mathematically sieve-equivalent, but it is an incremental
event system rather than a full stored sieve.

Twin generation
---------------
Primes emerge in increasing order. A twin pair occurs whenever two
consecutive prime openings differ by 2:

    previous_prime, current_prime
    current_prime - previous_prime = 2

The centre is their midpoint. No separate left/right centre test is
needed.

Metallic address
----------------
For every ordinary twin pair p,p+2 with centre C divisible by 6, define

    centre index n = C / 6.

Write n in base 8. Each base-8 digit is exactly one three-bit state:

    000,001,...,111.

At positional lift level r=1,2,3,... from the least-significant
three-bit block outward, assign

    metallic index = r + popcount(three_bit_state).

The complete address retains:
    - the exact three bits, so the centre can be reconstructed;
    - the local layer G/S/B/L from bit weight 0/1/2/3;
    - the unlimited indexed metallic coordinate M_k.

The address is an exact coordinate description. It is not yet assumed
to be the cause of primality. The purpose of this file is to generate
the complete data needed to discover whether successful twin addresses
obey a simpler recursive rule.

Memory
------
Prime-cycle memory grows with the number of active prime cycles, roughly
with the number of primes up to sqrt(N), rather than with N itself.

Twin pairs can be counted without retaining them. Set WRITE_TWINS_CSV
to True to stream them to disk instead of keeping them in memory.
"""

from __future__ import annotations

import csv
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from time import perf_counter


# ============================================================
# CONFIGURATION
# ============================================================

MAX_NUMBER = 10_000_000

# Print the first and last few twin pairs with addresses.
PRINT_SAMPLE_TWINS = True
SAMPLE_SIZE = 12

# Stream every twin pair to CSV without retaining all pairs in RAM.
WRITE_TWINS_CSV = False
CSV_PATH = Path("twin_metallic_addresses.csv")

# Track compact address statistics.
TRACK_ADDRESS_STATS = True


# ============================================================
# METALLIC ADDRESS
# ============================================================

LOCAL_LAYER = {
    0: "G",  # weight 0
    1: "S",  # weight 1
    2: "B",  # weight 2
    3: "L",  # completed/lift state
}


@dataclass(frozen=True, slots=True)
class AddressToken:
    """
    One exact three-bit positional state.

    level:
        1 for the least-significant octal digit, then 2,3,...

    bits:
        exact three-bit state, preserving orientation.

    weight:
        number of active bits.

    layer:
        G, S, B, or L.

    metallic_index:
        M_(level + weight).
    """

    level: int
    bits: str
    weight: int
    layer: str
    metallic_index: int


@dataclass(frozen=True, slots=True)
class MetallicAddress:
    centre_index: int
    tokens_low_to_high: tuple[AddressToken, ...]

    @property
    def bit_string(self) -> str:
        """Exact binary address, most-significant block first."""
        return "|".join(
            token.bits
            for token in reversed(self.tokens_low_to_high)
        )

    @property
    def metallic_string(self) -> str:
        """Indexed metallic coordinates, high block to low block."""
        return "|".join(
            f"{token.layer}:M{token.metallic_index}"
            for token in reversed(self.tokens_low_to_high)
        )

    @property
    def depth(self) -> int:
        return len(self.tokens_low_to_high)

    def decode(self) -> int:
        """Recover the exact centre index from the three-bit blocks."""
        value = 0

        for token in reversed(self.tokens_low_to_high):
            value = value * 8 + int(token.bits, 2)

        return value


def metallic_address(centre_index: int) -> MetallicAddress:
    if centre_index < 0:
        raise ValueError("centre_index must be non-negative")

    if centre_index == 0:
        digits = [0]
    else:
        digits: list[int] = []
        remaining = centre_index

        while remaining:
            digits.append(remaining & 0b111)
            remaining >>= 3

    tokens: list[AddressToken] = []

    for level, digit in enumerate(digits, start=1):
        bits = format(digit, "03b")
        weight = digit.bit_count()

        tokens.append(
            AddressToken(
                level=level,
                bits=bits,
                weight=weight,
                layer=LOCAL_LAYER[weight],
                metallic_index=level + weight,
            )
        )

    address = MetallicAddress(
        centre_index=centre_index,
        tokens_low_to_high=tuple(tokens),
    )

    assert address.decode() == centre_index

    return address


# ============================================================
# RECURSIVE PRIME-CYCLE SYSTEM
# ============================================================

@dataclass(slots=True)
class PrimeCycleStats:
    odd_positions_visited: int = 0
    prime_openings: int = 0
    cycle_openings: int = 0
    cycle_completions: int = 0
    collision_advances: int = 0
    maximum_active_events: int = 0


class RecursivePrimeCycles:
    """
    Incremental postponed composite cycles.

    events maps:
        next composite completion -> cycle step

    Only one future completion is retained per active cycle.
    """

    def __init__(self, maximum: int) -> None:
        if maximum < 2:
            raise ValueError("maximum must be at least 2")

        self.maximum = maximum
        self.events: dict[int, int] = {}
        self.stats = PrimeCycleStats()

    def advance_cycle(
        self,
        completion: int,
        step: int,
    ) -> None:
        """
        Recursively advance one cycle to its next unoccupied event.

        A loop is used instead of Python call recursion so ranges can
        be large without recursion-depth limits.
        """
        next_completion = completion + step

        while next_completion in self.events:
            next_completion += step
            self.stats.collision_advances += 1

        if next_completion <= self.maximum:
            self.events[next_completion] = step

            if len(self.events) > self.stats.maximum_active_events:
                self.stats.maximum_active_events = len(self.events)

    def primes(self):
        """Yield every prime in increasing order through maximum."""
        yield 2
        self.stats.prime_openings = 1

        candidate = 3

        while candidate <= self.maximum:
            self.stats.odd_positions_visited += 1

            step = self.events.pop(
                candidate,
                None,
            )

            if step is None:
                # Untouched odd position: a new prime opening.
                self.stats.prime_openings += 1
                yield candidate

                # No later composite <= maximum can have candidate as
                # its smallest factor unless candidate^2 <= maximum.
                square = candidate * candidate

                if square <= self.maximum:
                    cycle_step = candidate << 1

                    # square cannot already be occupied by a smaller
                    # prime cycle when candidate itself is prime.
                    self.events[square] = cycle_step
                    self.stats.cycle_openings += 1

                    if len(self.events) > self.stats.maximum_active_events:
                        self.stats.maximum_active_events = len(self.events)
            else:
                # A recursive composite-cycle completion.
                self.stats.cycle_completions += 1
                self.advance_cycle(
                    candidate,
                    step,
                )

            candidate += 2


# ============================================================
# TWIN STREAM
# ============================================================

@dataclass(frozen=True, slots=True)
class TwinRecord:
    lower: int
    centre: int
    upper: int
    centre_index: int | None
    address: MetallicAddress | None


@dataclass(slots=True)
class TwinStats:
    count: int = 0
    address_depths: Counter | None = None
    terminal_layers: Counter | None = None
    terminal_indices: Counter | None = None

    def __post_init__(self) -> None:
        if self.address_depths is None:
            self.address_depths = Counter()

        if self.terminal_layers is None:
            self.terminal_layers = Counter()

        if self.terminal_indices is None:
            self.terminal_indices = Counter()


class SampleBuffer:
    """Retain only the first and last k records."""

    def __init__(self, size: int) -> None:
        self.size = size
        self.first: list[TwinRecord] = []
        self.last: list[TwinRecord] = []

    def add(self, record: TwinRecord) -> None:
        if len(self.first) < self.size:
            self.first.append(record)

        self.last.append(record)

        if len(self.last) > self.size:
            self.last.pop(0)


def make_twin_record(
    lower: int,
    upper: int,
) -> TwinRecord:
    centre = (lower + upper) // 2

    # The exceptional pair (3,5) has centre 4, not a 6n centre.
    if centre % 6 != 0:
        return TwinRecord(
            lower=lower,
            centre=centre,
            upper=upper,
            centre_index=None,
            address=None,
        )

    centre_index = centre // 6
    address = metallic_address(
        centre_index
    )

    return TwinRecord(
        lower=lower,
        centre=centre,
        upper=upper,
        centre_index=centre_index,
        address=address,
    )


def update_address_stats(
    stats: TwinStats,
    record: TwinRecord,
) -> None:
    if not TRACK_ADDRESS_STATS:
        return

    if record.address is None:
        return

    address = record.address
    stats.address_depths[address.depth] += 1

    terminal = address.tokens_low_to_high[0]
    stats.terminal_layers[terminal.layer] += 1
    stats.terminal_indices[terminal.metallic_index] += 1


def csv_row(record: TwinRecord) -> list[str | int]:
    if record.address is None:
        return [
            record.lower,
            record.centre,
            record.upper,
            "",
            "exceptional",
            "",
        ]

    return [
        record.lower,
        record.centre,
        record.upper,
        record.centre_index,
        record.address.bit_string,
        record.address.metallic_string,
    ]


# ============================================================
# OUTPUT
# ============================================================

def print_record(record: TwinRecord) -> None:
    print(
        f"{record.lower:,} : "
        f"{record.centre:,} : "
        f"{record.upper:,}"
    )

    if record.address is None:
        print(
            "    address: exceptional pair outside ordinary 6n centres"
        )
        return

    print(
        f"    centre index: {record.centre_index:,}"
    )
    print(
        f"    three-bit address: {record.address.bit_string}"
    )
    print(
        f"    metallic address:  {record.address.metallic_string}"
    )


def print_counter(
    title: str,
    counter: Counter,
) -> None:
    print(f"\n{title}:")

    for key, value in sorted(counter.items()):
        print(
            f"  {key}: {value:,}"
        )


def main() -> None:
    print("=" * 82)
    print("RECURSIVE PRIME CYCLES WITH METALLIC TWIN ADDRESSES")
    print("=" * 82)
    print(f"Maximum number:        {MAX_NUMBER:,}")
    print("Full Boolean sieve:    none")
    print("Trial primality tests: none")
    print("Twin side tests:       none")
    print(
        "Twin rule:             consecutive generated primes differ by 2"
    )
    print(
        "Address rule:          exact base-8 / three-bit metallic coordinates"
    )

    start = perf_counter()

    system = RecursivePrimeCycles(
        MAX_NUMBER
    )
    twin_stats = TwinStats()
    samples = SampleBuffer(
        SAMPLE_SIZE
    )

    csv_file = None
    csv_writer = None

    if WRITE_TWINS_CSV:
        csv_file = CSV_PATH.open(
            "w",
            newline="",
            encoding="utf-8",
        )
        csv_writer = csv.writer(
            csv_file
        )
        csv_writer.writerow(
            [
                "lower_prime",
                "centre",
                "upper_prime",
                "centre_index",
                "three_bit_address",
                "metallic_address",
            ]
        )

    previous_prime = None

    try:
        for prime in system.primes():
            if (
                previous_prime is not None
                and prime - previous_prime == 2
            ):
                record = make_twin_record(
                    previous_prime,
                    prime,
                )

                twin_stats.count += 1
                update_address_stats(
                    twin_stats,
                    record,
                )
                samples.add(
                    record
                )

                if csv_writer is not None:
                    csv_writer.writerow(
                        csv_row(record)
                    )

            previous_prime = prime
    finally:
        if csv_file is not None:
            csv_file.close()

    elapsed = perf_counter() - start

    print("\n" + "=" * 82)
    print("SUMMARY")
    print("=" * 82)
    print(
        f"Prime openings:           "
        f"{system.stats.prime_openings:,}"
    )
    print(
        f"Twin-prime pairs:         "
        f"{twin_stats.count:,}"
    )
    print(
        f"Odd positions visited:    "
        f"{system.stats.odd_positions_visited:,}"
    )
    print(
        f"Prime cycles opened:      "
        f"{system.stats.cycle_openings:,}"
    )
    print(
        f"Cycle completions:        "
        f"{system.stats.cycle_completions:,}"
    )
    print(
        f"Maximum active events:    "
        f"{system.stats.maximum_active_events:,}"
    )
    print(
        f"Elapsed time:             "
        f"{elapsed:.6f} seconds"
    )

    if WRITE_TWINS_CSV:
        print(
            f"Twin CSV:                 "
            f"{CSV_PATH.resolve()}"
        )

    if TRACK_ADDRESS_STATS:
        print_counter(
            "Twin counts by three-bit address depth",
            twin_stats.address_depths,
        )
        print_counter(
            "Least-significant local metallic layer",
            twin_stats.terminal_layers,
        )
        print_counter(
            "Least-significant indexed metallic coordinate",
            twin_stats.terminal_indices,
        )

    if PRINT_SAMPLE_TWINS:
        print("\n" + "=" * 82)
        print("FIRST SAMPLE")
        print("=" * 82)

        for record in samples.first:
            print_record(record)

        print("\n" + "=" * 82)
        print("LAST SAMPLE")
        print("=" * 82)

        for record in samples.last:
            print_record(record)

    print(
        "\nInterpretation:"
    )
    print(
        "The recursive prime cycles generate the complete prime stream."
    )
    print(
        "The twin stream is obtained without testing both sides of every centre."
    )
    print(
        "The metallic address is a compact exact coordinate for each twin centre."
    )
    print(
        "A future theorem would need to show which metallic addresses survive "
        "without first running the prime-cycle system."
    )


if __name__ == "__main__":
    main()
