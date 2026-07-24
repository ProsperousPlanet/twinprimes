#!/usr/bin/env python3
"""
ADAPTIVE RECURSIVE PRIME-DEPTH WHEEL
====================================

Purpose
-------
Generate every prime and twin-prime pair through MAX_NUMBER while
recursively compressing candidate addresses with every internally
generated prime through a chosen prime depth.

If the recursive wheel contains primes

    2, 3, 5, 7, 11, ...

then each new prime p removes exactly 1/p of the addresses that survived
the earlier prime cycles.

The surviving density is therefore

    product over wheel primes p of (1 - 1/p).

Examples
--------
After p=2:

    remaining = 1/2

After p=3:

    remaining = (1/2)(2/3) = 1/3

After p=5:

    remaining = (1/2)(2/3)(4/5) = 4/15

The fractions are sequential. The p=3 layer removes one third of the
survivors, not another one third of the original number line.

Internal construction only
--------------------------
The wheel primes are not supplied as a list and are not checked by an
external primality function.

They are opened by the same recursive composite-cycle rule used by the
main generator:

    an untouched odd address opens as prime;
    its first composite completion is p^2;
    later completions advance by 2p.

The wheel is also expanded recursively. When a new internally generated
prime p is added to a wheel of modulus W, every old residue r is lifted
to

    r, r+W, r+2W, ..., r+(p-1)W

and the one lift divisible by p is removed.

No gcd scan over the new modulus is required.

Depth
-----
WHEEL_DEPTH_PRIME is the highest internally generated prime requested
for the wheel.

A memory guard, MAX_WHEEL_STATES, prevents an impractically large wheel.
If the requested next layer would exceed the guard, the program stops
at the previous recursive prime layer and reports that fact.

Prime and twin rules
--------------------
After wheel compression, the remaining recursive prime cycles generate
all later primes.

Two consecutive generated primes separated by 2 form a twin-prime pair.
No separate primality test and no separate test of both centre
boundaries is used.

Memory
------
The program stores:
    - one cycle event per active later prime;
    - the reusable wheel gap pattern;
    - compact counters and a small first/last sample.

It does not allocate a Boolean array through MAX_NUMBER and does not
retain every twin pair unless CSV output is explicitly enabled.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from time import perf_counter
import csv


# ============================================================
# CONFIGURATION
# ============================================================

MAX_NUMBER = 100_000_000

# Requested highest internally generated prime in the wheel.
WHEEL_DEPTH_PRIME = 17

# Prevent explosive materialization of very deep wheels.
# Through 17 requires 92,160 wheel states.
# Through 19 requires 1,658,880 states.
MAX_WHEEL_STATES = 250_000

PRINT_SAMPLES = True
SAMPLE_SIZE = 10

WRITE_TWINS_CSV = False
CSV_PATH = Path("adaptive_recursive_wheel_twins.csv")


# ============================================================
# INTERNAL RECURSIVE PRIME STREAM
# ============================================================

def internal_prime_stream():
    """
    Yield primes forever using recursive postponed composite cycles.

    No trial division and no external primality function.
    """
    yield 2

    # composite completion -> odd cycle step
    events: dict[int, int] = {}
    candidate = 3

    while True:
        step = events.pop(candidate, None)

        if step is None:
            yield candidate

            square = candidate * candidate
            events[square] = 2 * candidate
        else:
            next_completion = candidate + step

            while next_completion in events:
                next_completion += step

            events[next_completion] = step

        candidate += 2


# ============================================================
# RECURSIVE WHEEL CONSTRUCTION
# ============================================================

@dataclass(frozen=True, slots=True)
class WheelLayer:
    prime: int
    modulus_before: int
    modulus_after: int
    states_before: int
    states_after: int
    density_after: Fraction
    removed_from_survivors: Fraction
    removed_from_original: Fraction


@dataclass(frozen=True, slots=True)
class RecursiveWheel:
    primes: tuple[int, ...]
    modulus: int
    residues: tuple[int, ...]
    gaps: tuple[int, ...]
    phase_by_residue: dict[int, int]
    density: Fraction
    layers: tuple[WheelLayer, ...]
    stopped_by_state_guard: bool
    next_rejected_prime: int | None


def extend_residues(
    residues: list[int],
    modulus: int,
    prime: int,
) -> list[int]:
    """
    Recursively lift an existing wheel through one new prime layer.

    Exactly one of the p lifts of each old residue is divisible by p.
    """
    lifted: list[int] = []
    append = lifted.append

    for residue in residues:
        candidate = residue

        for _ in range(prime):
            if candidate % prime != 0:
                append(candidate)

            candidate += modulus

    lifted.sort()
    return lifted


def build_recursive_wheel(
    requested_depth_prime: int,
    maximum_states: int,
) -> RecursiveWheel:
    if requested_depth_prime < 2:
        raise ValueError("WHEEL_DEPTH_PRIME must be at least 2")

    if maximum_states < 1:
        raise ValueError("MAX_WHEEL_STATES must be positive")

    # Modulus 1 has one residue class, represented by 0.
    modulus = 1
    residues = [0]
    density = Fraction(1, 1)

    accepted_primes: list[int] = []
    layers: list[WheelLayer] = []

    stopped_by_guard = False
    next_rejected_prime = None

    for prime in internal_prime_stream():
        if prime > requested_depth_prime:
            break

        expected_states = len(residues) * (prime - 1)

        if expected_states > maximum_states:
            stopped_by_guard = True
            next_rejected_prime = prime
            break

        modulus_before = modulus
        states_before = len(residues)
        density_before = density

        residues = extend_residues(
            residues=residues,
            modulus=modulus,
            prime=prime,
        )

        modulus *= prime
        density *= Fraction(prime - 1, prime)

        removed_from_survivors = Fraction(1, prime)
        removed_from_original = (
            density_before * removed_from_survivors
        )

        accepted_primes.append(prime)

        layers.append(
            WheelLayer(
                prime=prime,
                modulus_before=modulus_before,
                modulus_after=modulus,
                states_before=states_before,
                states_after=len(residues),
                density_after=density,
                removed_from_survivors=removed_from_survivors,
                removed_from_original=removed_from_original,
            )
        )

    # For modulus > 1, zero is not a surviving residue.
    residues_tuple = tuple(residues)

    gaps_list = [
        residues_tuple[index + 1] - residues_tuple[index]
        for index in range(len(residues_tuple) - 1)
    ]

    gaps_list.append(
        modulus + residues_tuple[0] - residues_tuple[-1]
    )

    phase_by_residue = {
        residue: index
        for index, residue in enumerate(residues_tuple)
    }

    return RecursiveWheel(
        primes=tuple(accepted_primes),
        modulus=modulus,
        residues=residues_tuple,
        gaps=tuple(gaps_list),
        phase_by_residue=phase_by_residue,
        density=density,
        layers=tuple(layers),
        stopped_by_state_guard=stopped_by_guard,
        next_rejected_prime=next_rejected_prime,
    )


# ============================================================
# MAIN RECURSIVE PRIME CYCLES
# ============================================================

@dataclass(slots=True)
class GeneratorStats:
    candidate_addresses_visited: int = 0
    prime_openings: int = 0
    cycle_openings: int = 0
    cycle_completions: int = 0
    collision_advances: int = 0
    maximum_active_events: int = 0


class AdaptiveRecursivePrimeCycles:
    """
    Generate primes only on recursively wheel-admissible addresses.

    events maps:
        next composite completion -> (prime, multiplier wheel phase)
    """

    def __init__(
        self,
        maximum: int,
        wheel: RecursiveWheel,
    ) -> None:
        if maximum < 2:
            raise ValueError("MAX_NUMBER must be at least 2")

        self.maximum = maximum
        self.wheel = wheel
        self.events: dict[int, tuple[int, int]] = {}
        self.stats = GeneratorStats()

    def _update_maximum_events(self) -> None:
        active = len(self.events)

        if active > self.stats.maximum_active_events:
            self.stats.maximum_active_events = active

    def _advance_cycle(
        self,
        completion: int,
        prime: int,
        multiplier_phase: int,
    ) -> None:
        gaps = self.wheel.gaps
        phase_count = len(gaps)

        next_completion = (
            completion
            + prime * gaps[multiplier_phase]
        )

        multiplier_phase += 1

        if multiplier_phase == phase_count:
            multiplier_phase = 0

        while next_completion in self.events:
            next_completion += (
                prime * gaps[multiplier_phase]
            )

            multiplier_phase += 1

            if multiplier_phase == phase_count:
                multiplier_phase = 0

            self.stats.collision_advances += 1

        if next_completion <= self.maximum:
            self.events[next_completion] = (
                prime,
                multiplier_phase,
            )
            self._update_maximum_events()

    def primes(self):
        # The wheel primes themselves are prime openings even though
        # their residue classes are removed from the wheel.
        for prime in self.wheel.primes:
            if prime <= self.maximum:
                self.stats.prime_openings += 1
                yield prime

        if self.maximum <= self.wheel.primes[-1]:
            return

        gaps = self.wheel.gaps
        phase_count = len(gaps)

        # Start from wheel residue 1 and recursively advance past the
        # largest wheel prime.
        candidate = self.wheel.residues[0]
        candidate_phase = 0

        while candidate <= self.wheel.primes[-1]:
            candidate += gaps[candidate_phase]
            candidate_phase += 1

            if candidate_phase == phase_count:
                candidate_phase = 0

        while candidate <= self.maximum:
            self.stats.candidate_addresses_visited += 1

            event = self.events.pop(candidate, None)

            if event is None:
                # Survived the wheel and every earlier later-prime cycle.
                prime = candidate
                self.stats.prime_openings += 1
                yield prime

                square = prime * prime

                if square <= self.maximum:
                    multiplier_phase = (
                        self.wheel.phase_by_residue[
                            prime % self.wheel.modulus
                        ]
                    )

                    self.events[square] = (
                        prime,
                        multiplier_phase,
                    )
                    self.stats.cycle_openings += 1
                    self._update_maximum_events()
            else:
                self.stats.cycle_completions += 1

                prime, multiplier_phase = event

                self._advance_cycle(
                    completion=candidate,
                    prime=prime,
                    multiplier_phase=multiplier_phase,
                )

            candidate += gaps[candidate_phase]
            candidate_phase += 1

            if candidate_phase == phase_count:
                candidate_phase = 0


# ============================================================
# TWIN ADDRESS AND COUNTERS
# ============================================================

LAYER_BY_WEIGHT = {
    0: "G",
    1: "S",
    2: "B",
    3: "L",
}


def address_depth(centre_index: int) -> int:
    return max(
        1,
        (centre_index.bit_length() + 2) // 3,
    )


def three_bit_address(centre_index: int) -> str:
    depth = address_depth(centre_index)

    return "|".join(
        format(
            (centre_index >> (3 * position)) & 0b111,
            "03b",
        )
        for position in reversed(range(depth))
    )


def metallic_address(centre_index: int) -> str:
    depth = address_depth(centre_index)
    tokens: list[str] = []

    for position in reversed(range(depth)):
        digit = (
            centre_index >> (3 * position)
        ) & 0b111

        weight = digit.bit_count()
        level = position + 1
        metallic_index = level + weight

        tokens.append(
            f"{LAYER_BY_WEIGHT[weight]}:M{metallic_index}"
        )

    return "|".join(tokens)


@dataclass(frozen=True, slots=True)
class TwinSample:
    lower: int
    centre: int
    upper: int
    centre_index: int | None


class SampleWindow:
    def __init__(self, size: int) -> None:
        self.size = size
        self.first: list[TwinSample] = []
        self.last: list[TwinSample] = []

    def add(self, sample: TwinSample) -> None:
        if len(self.first) < self.size:
            self.first.append(sample)

        self.last.append(sample)

        if len(self.last) > self.size:
            self.last.pop(0)


@dataclass(slots=True)
class TwinStats:
    count: int = 0
    ordinary_count: int = 0
    exceptional_count: int = 0
    shell_counts: Counter | None = None

    def __post_init__(self) -> None:
        if self.shell_counts is None:
            self.shell_counts = Counter()

    def record(
        self,
        lower: int,
        upper: int,
    ) -> TwinSample:
        centre = (lower + upper) // 2
        self.count += 1

        if centre % 6 != 0:
            self.exceptional_count += 1

            return TwinSample(
                lower=lower,
                centre=centre,
                upper=upper,
                centre_index=None,
            )

        self.ordinary_count += 1
        centre_index = centre // 6
        self.shell_counts[
            address_depth(centre_index)
        ] += 1

        return TwinSample(
            lower=lower,
            centre=centre,
            upper=upper,
            centre_index=centre_index,
        )


# ============================================================
# OUTPUT
# ============================================================

def percentage(fraction: Fraction) -> float:
    return 100.0 * fraction.numerator / fraction.denominator


def print_wheel_layers(wheel: RecursiveWheel) -> None:
    print("\nRECURSIVE EXCLUSION LAYERS")
    print("-" * 94)
    print(
        "prime | removes of survivors | removes of original | "
        "remaining density | wheel states"
    )

    for layer in wheel.layers:
        print(
            f"{layer.prime:>5} | "
            f"{percentage(layer.removed_from_survivors):>18.9f}% | "
            f"{percentage(layer.removed_from_original):>17.9f}% | "
            f"{percentage(layer.density_after):>16.9f}% | "
            f"{layer.states_after:>12,}"
        )


def print_sample(sample: TwinSample) -> None:
    print(
        f"{sample.lower:,} : "
        f"{sample.centre:,} : "
        f"{sample.upper:,}"
    )

    if sample.centre_index is None:
        print(
            "    exceptional pair outside ordinary 6n centres"
        )
        return

    print(
        f"    centre index: "
        f"{sample.centre_index:,}"
    )
    print(
        f"    three-bit address: "
        f"{three_bit_address(sample.centre_index)}"
    )
    print(
        f"    metallic address:  "
        f"{metallic_address(sample.centre_index)}"
    )


def main() -> None:
    print("=" * 94)
    print("ADAPTIVE RECURSIVE PRIME-DEPTH WHEEL")
    print("=" * 94)
    print(f"Maximum number:             {MAX_NUMBER:,}")
    print(f"Requested wheel depth:      prime {WHEEL_DEPTH_PRIME}")
    print(f"Maximum materialized states:{MAX_WHEEL_STATES:>12,}")
    print("Injected prime list:        none")
    print("External primality tests:   none")
    print("Full Boolean sieve:         none")

    wheel_start = perf_counter()

    wheel = build_recursive_wheel(
        requested_depth_prime=WHEEL_DEPTH_PRIME,
        maximum_states=MAX_WHEEL_STATES,
    )

    wheel_elapsed = perf_counter() - wheel_start

    print_wheel_layers(wheel)

    print("\nWHEEL SUMMARY")
    print("-" * 94)
    print(
        "Internally generated primes: "
        + ", ".join(
            str(prime)
            for prime in wheel.primes
        )
    )
    print(
        f"Actual wheel depth:          "
        f"prime {wheel.primes[-1]}"
    )
    print(
        f"Wheel modulus:               "
        f"{wheel.modulus:,}"
    )
    print(
        f"Reusable wheel states:       "
        f"{len(wheel.residues):,}"
    )
    print(
        f"Exact surviving density:     "
        f"{wheel.density}"
    )
    print(
        f"Surviving percentage:        "
        f"{percentage(wheel.density):.9f}%"
    )
    print(
        f"Wheel construction time:     "
        f"{wheel_elapsed:.6f} seconds"
    )

    if wheel.stopped_by_state_guard:
        print(
            f"State guard stopped before:  "
            f"prime {wheel.next_rejected_prime}"
        )

    generator = AdaptiveRecursivePrimeCycles(
        maximum=MAX_NUMBER,
        wheel=wheel,
    )

    twins = TwinStats()
    samples = SampleWindow(
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
        csv_writer = csv.writer(csv_file)
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

    start = perf_counter()
    previous_prime = None
    highest_twin: TwinSample | None = None

    try:
        for prime in generator.primes():
            if (
                previous_prime is not None
                and prime - previous_prime == 2
            ):
                sample = twins.record(
                    previous_prime,
                    prime,
                )

                samples.add(sample)
                highest_twin = sample

                if csv_writer is not None:
                    if sample.centre_index is None:
                        centre_index = ""
                        bit_address = ""
                        metal_address = ""
                    else:
                        centre_index = sample.centre_index
                        bit_address = three_bit_address(
                            sample.centre_index
                        )
                        metal_address = metallic_address(
                            sample.centre_index
                        )

                    csv_writer.writerow(
                        [
                            sample.lower,
                            sample.centre,
                            sample.upper,
                            centre_index,
                            bit_address,
                            metal_address,
                        ]
                    )

            previous_prime = prime
    finally:
        if csv_file is not None:
            csv_file.close()

    elapsed = perf_counter() - start

    visited = generator.stats.candidate_addresses_visited
    integer_baseline = max(1, MAX_NUMBER - 1)
    odd_baseline = max(1, (MAX_NUMBER - 1) // 2)

    print("\n" + "=" * 94)
    print("GENERATION SUMMARY")
    print("=" * 94)
    print(
        f"Prime openings:              "
        f"{generator.stats.prime_openings:,}"
    )
    print(
        f"Twin-prime pairs:            "
        f"{twins.count:,}"
    )
    print(
        f"Ordinary 6n twin pairs:      "
        f"{twins.ordinary_count:,}"
    )
    print(
        f"Candidate addresses visited: "
        f"{visited:,}"
    )
    print(
        f"Odd-address baseline:        "
        f"{odd_baseline:,}"
    )
    print(
        f"Reduction from odd scan:     "
        f"{100 * (1 - visited / odd_baseline):.9f}%"
    )
    print(
        f"Reduction from integer scan: "
        f"{100 * (1 - visited / integer_baseline):.9f}%"
    )
    print(
        f"Prime cycles opened:         "
        f"{generator.stats.cycle_openings:,}"
    )
    print(
        f"Cycle completions:           "
        f"{generator.stats.cycle_completions:,}"
    )
    print(
        f"Maximum active events:       "
        f"{generator.stats.maximum_active_events:,}"
    )
    print(
        f"Generation time:             "
        f"{elapsed:.6f} seconds"
    )

    if highest_twin is not None:
        print("\nHighest generated twin:")
        print_sample(highest_twin)
        print(
            f"    generated twin rank: "
            f"{twins.count:,}"
        )

    print("\nRadix-8 twin shells:")
    cumulative = 0

    for depth in sorted(twins.shell_counts):
        count = twins.shell_counts[depth]
        cumulative += count

        lower = 0 if depth == 1 else 8 ** (depth - 1)
        upper = 8 ** depth

        print(
            f"  depth {depth}: "
            f"[{lower:,}, {upper:,}) "
            f"count={count:,} "
            f"cumulative={cumulative:,}"
        )

    if PRINT_SAMPLES:
        print("\n" + "=" * 94)
        print("FIRST SAMPLE")
        print("=" * 94)

        for sample in samples.first:
            print_sample(sample)

        print("\n" + "=" * 94)
        print("LAST SAMPLE")
        print("=" * 94)

        for sample in samples.last:
            print_sample(sample)

    if WRITE_TWINS_CSV:
        print(
            f"\nCSV written to: "
            f"{CSV_PATH.resolve()}"
        )

    print("\nInterpretation:")
    print(
        "Each internally generated prime layer p removes exactly "
        "1/p of the addresses surviving the earlier layers."
    )
    print(
        "The wheel removes every address divisible by a wheel prime, "
        "not every composite address."
    )
    print(
        "Later recursive prime cycles remove composites whose smallest "
        "prime factor lies beyond the wheel depth."
    )
    print(
        "If the wheel depth reached at least sqrt(MAX_NUMBER), every "
        "composite through MAX_NUMBER would already be excluded, but "
        "materializing that full wheel is usually less efficient than "
        "the hybrid recursive event system."
    )


if __name__ == "__main__":
    main()
