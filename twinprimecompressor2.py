#!/usr/bin/env python3
"""
TWIN-PRIME FRAMEWORK: FROM SMALL COUNTERS TO THE K-CHAIN

Correct presentation order:
1. Generate ordinary primes and twin primes through a chosen limit using
   recursive composite-closure counters. No primality function is used
   during generation; SymPy audits the finished result afterward.
2. Show the seed 2,3, the completed cycle 6, the 6n±1 twin form, and the
   square-anchor chain 2 -> 4 -> 16 -> 256 -> 65,536.
3. Explain that 256 is a structural K-address, not a twin-prime centre.
4. Use K=256 in C(a+Kb) to generate the actual entry centre, then use K^2
   at the next Gold position to generate the square-closure centre.
5. Display the verified higher K-chain with K-addresses and generated
   twin centres kept in separate fields.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
from sympy import isprime

DEFAULT_LIMIT = 256
DEFAULT_REPORT = Path("twin_prime_framework_from_small_counts_to_k_chain.txt")


@dataclass(frozen=True, slots=True)
class SmallGeneration:
    limit: int
    primes: tuple[int, ...]
    twin_pairs: tuple[tuple[int, int], ...]


def generate_by_closure_counters(limit: int) -> SmallGeneration:
    """Generate primes by recursive counters, without primality tests."""
    if limit < 2:
        return SmallGeneration(limit, (), ())

    # next_closure[p] is the next multiple closed by the p-counter.
    next_closure: dict[int, int] = {}
    primes: list[int] = []

    for number in range(2, limit + 1):
        closing = [p for p, landing in next_closure.items() if landing == number]

        if closing:
            for p in closing:
                next_closure[p] += p
            continue

        # No existing counter closed this number, so it opens a new counter.
        primes.append(number)
        square = number * number
        if square <= limit:
            next_closure[number] = square

    twins = tuple(
        (left, right)
        for left, right in zip(primes, primes[1:])
        if right - left == 2
    )

    return SmallGeneration(limit, tuple(primes), twins)


def audit_small_generation(result: SmallGeneration) -> None:
    expected = tuple(n for n in range(2, result.limit + 1) if isprime(n))
    if result.primes != expected:
        raise RuntimeError("Recursive counter prime list failed independent audit.")

    for left, right in result.twin_pairs:
        if not (isprime(left) and isprime(right) and right - left == 2):
            raise RuntimeError("Recursive counter twin list failed independent audit.")


@dataclass(frozen=True, slots=True)
class GoldState:
    previous: int
    current: int
    centre: int


@dataclass(frozen=True, slots=True)
class TwinAudit:
    centre: int
    left: int
    right: int
    left_prime: bool
    right_prime: bool

    @property
    def twin(self) -> bool:
        return self.left_prime and self.right_prime


@dataclass(frozen=True, slots=True)
class KLevel:
    level: int
    order: int
    entry_step: int
    correction: int | None
    description: str


@dataclass(frozen=True, slots=True)
class AuditedKLevel:
    level: KLevel
    entry_position: GoldState
    square_position: GoldState
    entry_generated: GoldState
    square_generated: GoldState
    entry_audit: TwinAudit
    square_audit: TwinAudit

    @property
    def strict(self) -> bool:
        return self.entry_audit.twin and self.square_audit.twin


GOLD_SEED = GoldState(2, 3, 6)


def metallic_step(state: GoldState, order: int) -> GoldState:
    next_period = state.previous + order * state.current
    return GoldState(
        previous=state.current,
        current=next_period,
        centre=state.centre * next_period,
    )


def gold_position(step: int) -> GoldState:
    state = GOLD_SEED
    for _ in range(step):
        state = metallic_step(state, 1)
    return state


def audit_centre(centre: int) -> TwinAudit:
    left = centre - 1
    right = centre + 1
    return TwinAudit(centre, left, right, bool(isprime(left)), bool(isprime(right)))


def audit_k_level(level: KLevel) -> AuditedKLevel:
    entry_position = gold_position(level.entry_step)
    square_position = gold_position(level.entry_step + 1)
    entry_generated = metallic_step(entry_position, level.order)
    square_generated = metallic_step(square_position, level.order ** 2)
    return AuditedKLevel(
        level=level,
        entry_position=entry_position,
        square_position=square_position,
        entry_generated=entry_generated,
        square_generated=square_generated,
        entry_audit=audit_centre(entry_generated.centre),
        square_audit=audit_centre(square_generated.centre),
    )


K_CHAIN = (
    KLevel(0, 256, 2, None, "First higher metallic address"),
    KLevel(1, 65_615, 4, 79, "First reset above 256^2"),
    KLevel(2, 4_305_339_892, 6, 11_667, "Verified upward continuation"),
    KLevel(3, 18_535_951_585_646_718_710, 8, 147_046, "Verified upward continuation"),
    KLevel(
        4,
        343_581_501_185_439_105_620_765_555_789_867_061_134,
        10,
        2_997_034,
        "Verified upward continuation",
    ),
)


def audit_entire_k_chain() -> tuple[AuditedKLevel, ...]:
    chain = tuple(audit_k_level(level) for level in K_CHAIN)
    failed = [item.level.order for item in chain if not item.strict]
    if failed:
        raise RuntimeError("Displayed K-chain audit failed: " + ", ".join(map(str, failed)))
    return chain


def fmt(value: int) -> str:
    return f"{value:,}"


def compact(value: int, maximum: int = 90) -> str:
    text = fmt(value)
    if len(text) <= maximum:
        return text
    return text[:42] + "..." + text[-42:]


def centre_description(pair: tuple[int, int]) -> str:
    centre = (pair[0] + pair[1]) // 2
    if centre % 6 == 0:
        return f"{fmt(centre)} = 6({fmt(centre // 6)})"
    return f"{fmt(centre)} (exceptional first centre)"


def build_report(small: SmallGeneration, chain: tuple[AuditedKLevel, ...]) -> str:
    lines: list[str] = [
        "=" * 118,
        "TWIN-PRIME FRAMEWORK: FROM SMALL COUNTERS TO THE HIGHER K-CHAIN",
        "=" * 118,
        "",
        "IMPORTANT DISTINCTION",
        "-" * 118,
        "A twin-prime centre C has prime neighbours C-1 and C+1.",
        "A square anchor such as 16 or 256 is a structural scale, not automatically a twin-prime centre.",
        "A metallic K-address such as K=256 is inserted into C(a+Kb) to generate a different centre.",
        "Therefore 'K=256 succeeds' does NOT mean that 255 and 257 are both prime.",
        "",
        "PART I — RECURSIVE SMALL-NUMBER GENERATION",
        "-" * 118,
        f"Generation limit: {small.limit}",
        "Previously opened counters close their multiples. An unclosed number opens a new counter at its square.",
        "No primality function is used during generation. SymPy audits the completed output afterward.",
        f"Generated primes: {len(small.primes)}",
        f"Generated twin-prime pairs: {len(small.twin_pairs)}",
        "",
        "Twin-prime pairs through the limit:",
    ]

    for index, pair in enumerate(small.twin_pairs, start=1):
        lines.append(
            f"  {index:2d}. ({fmt(pair[0])}, {fmt(pair[1])})"
            f"    centre: {centre_description(pair)}"
        )

    lines += [
        "",
        "Small-number rule:",
        "  (3,5) is the exceptional first pair with centre 4.",
        "  Every later twin pair has the form 6n-1, 6n+1 and therefore has centre 6n.",
        "",
        "PART II — THE FOUNDATION BEFORE K=256",
        "-" * 118,
        "Seed counters: 2 and 3",
        "First completed multiplicative cycle: 2 * 3 = 6",
        "Gold additive backbone: 2, 3, 5, 8, 13, 21, 34, 55, 89, ...",
        "Square-anchor chain: 2 -> 4 -> 16 -> 256 -> 65,536",
        "Each anchor is the square of the previous anchor.",
        "These anchors are structural scales, not a list of twin-prime centres.",
        "",
        "Gold counting states:",
    ]

    for step in range(12):
        state = gold_position(step)
        lines.append(
            f"  step {step:2d}: ({fmt(state.previous)}, {fmt(state.current)}; centre {fmt(state.centre)})"
        )

    first = chain[0]
    lines += [
        "",
        "PART III — HOW K=256 BUILDS ABOVE THE SMALL RULES",
        "-" * 118,
        "K=256 is a metallic address, not the generated twin centre.",
        f"Entry Gold position: (a,b;C)=({first.entry_position.previous},{first.entry_position.current};{fmt(first.entry_position.centre)})",
        f"next period = {first.entry_position.previous} + 256({first.entry_position.current}) = {fmt(first.entry_generated.current)}",
        f"generated centre = {fmt(first.entry_position.centre)}({fmt(first.entry_generated.current)}) = {fmt(first.entry_audit.centre)}",
        "Actual entry twin pair:",
        f"  {fmt(first.entry_audit.left)}, {fmt(first.entry_audit.right)}",
        "",
        "Square the ADDRESS and move to the next Gold position:",
        "  K^2 = 256^2 = 65,536",
        f"  next Gold position: ({first.square_position.previous},{first.square_position.current};{fmt(first.square_position.centre)})",
        f"  next period = {first.square_position.previous} + 65,536({first.square_position.current}) = {fmt(first.square_generated.current)}",
        f"  generated closure centre = {fmt(first.square_position.centre)}({fmt(first.square_generated.current)}) = {fmt(first.square_audit.centre)}",
        "Actual square-closure twin pair:",
        f"  {fmt(first.square_audit.left)}, {fmt(first.square_audit.right)}",
        "",
        "PART IV — VERIFIED HIGHER K-CHAIN",
        "-" * 118,
        "Every level below separates the K-address from the centre that K generates.",
    ]

    for item in chain:
        construction = (
            "starting address"
            if item.level.correction is None
            else f"previous K^2 + {fmt(item.level.correction)}"
        )
        lines += [
            "",
            f"LEVEL {item.level.level}",
            f"  K-address (NOT the twin centre): {compact(item.level.order)}",
            f"  construction: {construction}",
            f"  entry Gold step: {item.level.entry_step}",
            f"  generated entry centre: {compact(item.entry_audit.centre)}",
            "  actual entry twin pair:",
            f"    {compact(item.entry_audit.left)}",
            f"    {compact(item.entry_audit.right)}",
            f"  K^2 address: {compact(item.level.order ** 2)}",
            f"  generated square-closure centre: {compact(item.square_audit.centre)}",
            "  actual square-closure twin pair:",
            f"    {compact(item.square_audit.left)}",
            f"    {compact(item.square_audit.right)}",
        ]

    lines += ["", "Compact K-address recurrence:"]
    for previous, current in zip(K_CHAIN, K_CHAIN[1:]):
        lines.append(
            f"  {compact(previous.order)}^2 + {fmt(current.correction or 0)} = {compact(current.order)}"
        )

    lines += [
        "",
        "PART V — WHAT HAS ACTUALLY BEEN SHOWN",
        "-" * 118,
        f"1. Recursive closure counters reproduce every ordinary prime and twin-prime pair through {small.limit}.",
        "2. The square-anchor chain reaches 256 before the higher K-chain begins.",
        "3. K=256 generates centre 492,720; it does not claim that 256 itself is a twin centre.",
        "4. K^2=65,536 generates the next square-closure centre at the following Gold position.",
        "5. Four additional K-addresses repeat the same entry-and-square pattern without an observed break.",
        "",
        "CONTINUATION CONJECTURE",
        "-" * 118,
        "We believe the higher K-chain may continue without bound and may support an infinite branching family of twin-prime centres.",
        "The current evidence is a finite verified chain together with additional Gold-memory branches.",
        "The exact closed memory-only formula deriving every future correction has not yet been proved.",
        "Until that formula and non-termination are proved, unbounded continuation remains a conjecture.",
    ]

    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    small = generate_by_closure_counters(args.limit)
    audit_small_generation(small)
    chain = audit_entire_k_chain()
    report = build_report(small, chain)
    args.report.write_text(report, encoding="utf-8")
    print(report)
    print()
    print(f"Saved report: {args.report.resolve()}")


if __name__ == "__main__":
    main()
