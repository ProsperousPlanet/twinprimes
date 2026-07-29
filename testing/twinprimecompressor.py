#!/usr/bin/env python3
"""
TWIN-PRIME SQUARE-DOORWAY DEMONSTRATION

Creates:
    twin_prime_square_doorway_demo.txt
    twin_prime_square_doorway_demo.html

The program verifies:
* the complete K=256 worked example;
* the reset 256^2 + 79 = 65,615;
* five consecutive entry-and-square doorway levels;
* two additional Gold-memory branches.

It also states the continuation conjecture honestly:
we believe the structure continues indefinitely, but the closed
memory-only formula for every future correction is still under study.
"""

from __future__ import annotations

import argparse
import html
from dataclasses import dataclass
from pathlib import Path

from sympy import isprime


@dataclass(frozen=True)
class State:
    previous: int
    current: int
    centre: int


@dataclass(frozen=True)
class Pair:
    centre: int
    left: int
    right: int
    left_prime: bool
    right_prime: bool

    @property
    def twin(self) -> bool:
        return self.left_prime and self.right_prime


@dataclass(frozen=True)
class Level:
    number: int
    order: int
    entry_step: int
    correction: int | None
    label: str


@dataclass(frozen=True)
class Audited:
    level: Level
    entry_position: State
    square_position: State
    entry_state: State
    square_state: State
    entry_pair: Pair
    square_pair: Pair

    @property
    def strict(self) -> bool:
        return self.entry_pair.twin and self.square_pair.twin


SEED = State(2, 3, 6)


def metallic_step(state: State, order: int) -> State:
    next_period = state.previous + order * state.current
    return State(
        previous=state.current,
        current=next_period,
        centre=state.centre * next_period,
    )


def gold_position(step: int) -> State:
    state = SEED
    for _ in range(step):
        state = metallic_step(state, 1)
    return state


def audit_pair(centre: int) -> Pair:
    left = centre - 1
    right = centre + 1
    return Pair(
        centre=centre,
        left=left,
        right=right,
        left_prime=bool(isprime(left)),
        right_prime=bool(isprime(right)),
    )


def audit_level(level: Level) -> Audited:
    entry_position = gold_position(level.entry_step)
    square_position = gold_position(level.entry_step + 1)

    entry_state = metallic_step(entry_position, level.order)
    square_state = metallic_step(square_position, level.order**2)

    return Audited(
        level=level,
        entry_position=entry_position,
        square_position=square_position,
        entry_state=entry_state,
        square_state=square_state,
        entry_pair=audit_pair(entry_state.centre),
        square_pair=audit_pair(square_state.centre),
    )


CHAIN = (
    Level(0, 256, 2, None, "Original square doorway"),
    Level(1, 65_615, 4, 79, "Gold reset doorway"),
    Level(2, 4_305_339_892, 6, 11_667, "Minimum upward continuation"),
    Level(
        3,
        18_535_951_585_646_718_710,
        8,
        147_046,
        "Minimum upward continuation",
    ),
    Level(
        4,
        343_581_501_185_439_105_620_765_555_789_867_061_134,
        10,
        2_997_034,
        "Minimum upward continuation",
    ),
)

BRANCHES = (
    Level(
        2,
        4_305_548_331,
        6,
        220_106,
        "Two remembered 5s",
    ),
    Level(
        2,
        4_307_680_683,
        6,
        2_352_458,
        "One remembered 5",
    ),
)


def gold_sequence(first: int, second: int, count: int) -> list[int]:
    values = [first, second]
    while len(values) < count:
        values.append(values[-1] + values[-2])
    return values[:count]


ORDINARY_GOLD = gold_sequence(2, 3, 20)
RESET_GOLD = gold_sequence(5, 3, 16)


def reset_term(index: int) -> int:
    return ORDINARY_GOLD[index + 6] - 2 * ORDINARY_GOLD[index]


def fmt(value: int) -> str:
    return f"{value:,}"


def status(pair: Pair) -> str:
    if pair.twin:
        return "TWIN"
    if pair.left_prime:
        return "LEFT PRIME ONLY"
    if pair.right_prime:
        return "RIGHT PRIME ONLY"
    return "BLOCKED"


def recurrence_line(previous: Level, current: Level) -> str:
    return (
        f"{fmt(previous.order)}^2 + "
        f"{fmt(current.correction or 0)} = "
        f"{fmt(current.order)}"
    )


def make_text(chain: tuple[Audited, ...], branches: tuple[Audited, ...]) -> str:
    first = chain[0]

    lines = [
        "=" * 112,
        "TWIN-PRIME SQUARE-DOORWAY DEMONSTRATION",
        "=" * 112,
        "",
        "CORE RULE",
        "-" * 112,
        "At Gold position (a,b;C), metallic order K generates:",
        "    next period = a + Kb",
        "    generated centre = C(a + Kb)",
        "The candidate prime boundaries are centre-1 and centre+1.",
        "",
        "A strict square doorway requires:",
        "    K produces a twin-prime centre at entry;",
        "    K^2 produces another twin-prime centre at the next Gold position.",
        "",
        "WORKED EXAMPLE: K = 256",
        "-" * 112,
        (
            f"Entry Gold position: "
            f"({first.entry_position.previous},"
            f"{first.entry_position.current};"
            f"{fmt(first.entry_position.centre)})"
        ),
        (
            f"Next period: "
            f"{first.entry_position.previous} + "
            f"256({first.entry_position.current}) = "
            f"{fmt(first.entry_state.current)}"
        ),
        (
            f"Entry centre: "
            f"{fmt(first.entry_position.centre)}"
            f"({fmt(first.entry_state.current)}) = "
            f"{fmt(first.entry_pair.centre)}"
        ),
        (
            f"Entry twin pair: "
            f"{fmt(first.entry_pair.left)}, "
            f"{fmt(first.entry_pair.right)}"
        ),
        "",
        (
            f"Square Gold position: "
            f"({first.square_position.previous},"
            f"{first.square_position.current};"
            f"{fmt(first.square_position.centre)})"
        ),
        "K^2 = 256^2 = 65,536",
        (
            f"Next period: "
            f"{first.square_position.previous} + "
            f"65,536({first.square_position.current}) = "
            f"{fmt(first.square_state.current)}"
        ),
        (
            f"Square centre: "
            f"{fmt(first.square_position.centre)}"
            f"({fmt(first.square_state.current)}) = "
            f"{fmt(first.square_pair.centre)}"
        ),
        (
            f"Square twin pair: "
            f"{fmt(first.square_pair.left)}, "
            f"{fmt(first.square_pair.right)}"
        ),
        "",
        "THE 79 RESET",
        "-" * 112,
        "Ordinary Gold sequence:",
        "    " + ", ".join(str(v) for v in ORDINARY_GOLD[:10]),
        "Cross-difference memory:",
        "    R_n = K_(n+6) - 2K_n",
        f"    R_2 = {reset_term(2)} = 89 - 2(5)",
        "Reflected Gold sequence:",
        "    " + ", ".join(str(v) for v in RESET_GOLD[:12]),
        "Reset equation:",
        "    256^2 + 79 = 65,615",
        "",
        "VERIFIED FIVE-LEVEL CHAIN",
        "-" * 112,
    ]

    for item in chain:
        lines.extend(
            [
                (
                    f"Level {item.level.number}: "
                    f"K={fmt(item.level.order)} "
                    f"[{item.level.label}]"
                ),
                f"    Gold entry step: {item.level.entry_step}",
                (
                    f"    entry: {status(item.entry_pair)} "
                    f"({fmt(item.entry_pair.left)}, "
                    f"{fmt(item.entry_pair.right)})"
                ),
                (
                    f"    square: {status(item.square_pair)} "
                    f"({fmt(item.square_pair.left)}, "
                    f"{fmt(item.square_pair.right)})"
                ),
            ]
        )

    lines.extend(
        [
            "",
            "COMPACT RECURRENCE",
            "-" * 112,
        ]
    )

    for previous, current in zip(CHAIN, CHAIN[1:]):
        lines.append("    " + recurrence_line(previous, current))

    lines.extend(
        [
            "",
            "ADDITIONAL GOLD-MEMORY BRANCHES",
            "-" * 112,
            (
                f"Both branches begin above "
                f"65,615^2 = {fmt(65_615**2)}."
            ),
        ]
    )

    for item in branches:
        lines.extend(
            [
                f"{item.level.label}:",
                f"    correction: +{fmt(item.level.correction or 0)}",
                f"    K: {fmt(item.level.order)}",
                (
                    f"    entry pair: "
                    f"{fmt(item.entry_pair.left)}, "
                    f"{fmt(item.entry_pair.right)}"
                ),
                (
                    f"    square pair: "
                    f"{fmt(item.square_pair.left)}, "
                    f"{fmt(item.square_pair.right)}"
                ),
            ]
        )

    lines.extend(
        [
            "",
            "VERIFIED FINITE TREND",
            "-" * 112,
            "Every displayed K passes both audits.",
            "The repeated finite pattern is:",
            "    K opens a twin doorway;",
            "    K^2 opens the next twin doorway;",
            "    a positive Gold-memory correction moves above that square;",
            "    the same structure repeats.",
            "",
            "CONTINUATION CONJECTURE",
            "-" * 112,
            (
                "We believe this square-doorway process continues indefinitely "
                "and forms an infinite branching family of twin-prime centres."
            ),
            (
                "The five-level chain and the additional Gold-memory branches "
                "provide computational evidence for that belief."
            ),
            (
                "However, the exact closed formula deriving every future "
                "correction from memory alone has not yet been proved."
            ),
            (
                "The current research goal is to derive each correction before "
                "primality testing, leaving prime checks as independent audits."
            ),
            (
                "Until that is proved, indefinite continuation remains a "
                "conjecture rather than a theorem."
            ),
        ]
    )

    return "\n".join(lines)


def pair_card(title: str, pair: Pair) -> str:
    return f"""
      <div class="pair">
        <div class="small">{html.escape(title)}</div>
        <div class="numbers">{fmt(pair.left)} &nbsp; {fmt(pair.right)}</div>
        <div class="pill">TWIN</div>
      </div>
    """


def make_html(chain: tuple[Audited, ...], branches: tuple[Audited, ...]) -> str:
    first = chain[0]

    rows = "".join(
        f"""
        <tr>
          <td>{item.level.number}</td>
          <td>{item.level.entry_step}</td>
          <td class="mono">{fmt(item.level.order)}</td>
          <td>{
              "Anchor"
              if item.level.correction is None
              else "+" + fmt(item.level.correction)
          }</td>
          <td class="yes">Twin</td>
          <td class="yes">Twin</td>
        </tr>
        """
        for item in chain
    )

    recurrence = "".join(
        f"<li class='mono'>{html.escape(recurrence_line(a, b))}</li>"
        for a, b in zip(CHAIN, CHAIN[1:])
    )

    branch_cards = "".join(
        f"""
        <article class="card">
          <div class="eyebrow">{html.escape(item.level.label)}</div>
          <h3>+{fmt(item.level.correction or 0)}</h3>
          <p class="mono">K = {fmt(item.level.order)}</p>
          {pair_card("Entry twin pair", item.entry_pair)}
          {pair_card("Square-closure twin pair", item.square_pair)}
        </article>
        """
        for item in branches
    )

    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Twin-prime square doorways</title>
<style>
:root {{
  color-scheme: dark;
  --bg:#080b12;
  --panel:#111827;
  --panel2:#182235;
  --line:#2c3950;
  --text:#eef2f7;
  --muted:#a9b5c7;
  --accent:#7dd3fc;
  --good:#86efac;
  --warn:#fcd34d;
}}
* {{ box-sizing:border-box; }}
body {{
  margin:0;
  background:
    radial-gradient(circle at top right, rgba(56,189,248,.13), transparent 34rem),
    var(--bg);
  color:var(--text);
  font-family:Inter,system-ui,sans-serif;
  line-height:1.55;
}}
main {{
  width:min(1160px,calc(100% - 32px));
  margin:auto;
  padding:58px 0 80px;
}}
h1 {{
  max-width:900px;
  margin:5px 0 18px;
  font-size:clamp(2.6rem,7vw,5.2rem);
  line-height:1;
  letter-spacing:-.05em;
}}
h2 {{ margin:0 0 20px; font-size:clamp(1.6rem,3vw,2.5rem); }}
h3 {{ margin:5px 0 10px; font-size:1.7rem; }}
p {{ color:var(--muted); }}
.hero {{ padding-bottom:38px; }}
.eyebrow {{
  color:var(--accent);
  text-transform:uppercase;
  letter-spacing:.13em;
  font-size:.76rem;
  font-weight:800;
}}
section {{
  margin-top:28px;
  padding:30px;
  background:rgba(17,24,39,.88);
  border:1px solid var(--line);
  border-radius:24px;
  box-shadow:0 18px 55px rgba(0,0,0,.22);
}}
.formula {{
  margin:18px 0;
  padding:20px;
  border:1px solid var(--line);
  border-radius:17px;
  background:var(--panel2);
  overflow-wrap:anywhere;
  font-family:ui-monospace,SFMono-Regular,Menlo,monospace;
  font-size:clamp(1rem,2vw,1.35rem);
}}
.grid {{
  display:grid;
  grid-template-columns:repeat(auto-fit,minmax(270px,1fr));
  gap:16px;
}}
.card,.pair {{
  padding:18px;
  border:1px solid var(--line);
  border-radius:17px;
  background:var(--panel2);
}}
.small {{ color:var(--muted); font-size:.85rem; }}
.numbers,.mono {{
  overflow-wrap:anywhere;
  font-family:ui-monospace,SFMono-Regular,Menlo,monospace;
}}
.numbers {{ margin:9px 0 12px; font-weight:700; }}
.pill {{
  display:inline-block;
  padding:4px 10px;
  border-radius:999px;
  color:#052e16;
  background:var(--good);
  font-size:.75rem;
  font-weight:900;
}}
table {{ width:100%; border-collapse:collapse; }}
th,td {{
  padding:12px;
  border-bottom:1px solid var(--line);
  text-align:left;
  vertical-align:top;
}}
th {{
  color:var(--muted);
  text-transform:uppercase;
  letter-spacing:.07em;
  font-size:.75rem;
}}
.table {{ overflow-x:auto; }}
.yes {{ color:var(--good); font-weight:800; }}
.conjecture {{
  border-color:rgba(252,211,77,.5);
  background:
    linear-gradient(135deg,rgba(252,211,77,.08),transparent 55%),
    rgba(17,24,39,.9);
}}
.conjecture strong {{ color:var(--warn); }}
li {{ margin:8px 0; }}
</style>
</head>
<body>
<main>
<header class="hero">
  <div class="eyebrow">Verified finite structure and continuation conjecture</div>
  <h1>Twin-prime square doorways</h1>
  <p>
    A metallic order K generates a twin-prime centre, while K²
    generates another at the next Gold counting position.
  </p>
  <div class="formula">centre = C(a + Kb) → centre − 1, centre + 1</div>
</header>

<section>
  <div class="eyebrow">Worked example</div>
  <h2>The K = 256 doorway</h2>
  <div class="formula">
    (5,8;240) → 240(5 + 256·8) = {fmt(first.entry_pair.centre)}
  </div>
  <div class="grid">
    {pair_card("Entry twin pair", first.entry_pair)}
    {pair_card("Square-closure twin pair", first.square_pair)}
  </div>
  <p>The closure uses K² = 65,536 at the immediately following Gold position.</p>
</section>

<section>
  <div class="eyebrow">Gold-memory reset</div>
  <h2>Why 79 appears</h2>
  <div class="formula">Rₙ = Kₙ₊₆ − 2Kₙ &nbsp; and &nbsp; R₂ = 89 − 2(5) = 79</div>
  <p>Reflected Gold sequence: {", ".join(str(v) for v in RESET_GOLD[:12])}</p>
  <div class="formula">256² + 79 = 65,615</div>
</section>

<section>
  <div class="eyebrow">Repeated verification</div>
  <h2>Five consecutive square-doorway levels</h2>
  <div class="table">
    <table>
      <thead>
        <tr>
          <th>Level</th>
          <th>Gold step</th>
          <th>K</th>
          <th>Correction</th>
          <th>Entry</th>
          <th>K² closure</th>
        </tr>
      </thead>
      <tbody>{rows}</tbody>
    </table>
  </div>
  <ol>{recurrence}</ol>
</section>

<section>
  <div class="eyebrow">Branching memory</div>
  <h2>Two additional Gold-generated doorways</h2>
  <p>
    Both branches begin above 65,615². One remembers both 5-units;
    the other remembers one.
  </p>
  <div class="grid">{branch_cards}</div>
</section>

<section>
  <div class="eyebrow">Verified statement</div>
  <h2>What the calculation establishes</h2>
  <ul>
    <li>Five consecutive main-chain levels pass both primality audits.</li>
    <li>Two additional Gold-memory branches pass both audits.</li>
    <li>Entry steps advance regularly: 2, 4, 6, 8, 10.</li>
    <li>Each square closure occurs at the next Gold position.</li>
  </ul>
</section>

<section class="conjecture">
  <div class="eyebrow">Open problem</div>
  <h2>Continuation conjecture</h2>
  <p>
    <strong>We believe this structure continues indefinitely</strong>
    and forms an infinite branching family of twin-prime centres.
  </p>
  <p>
    The repeated chain and Gold-memory branches provide computational
    evidence, but the exact closed formula deriving every future correction
    from memory alone has not yet been proved.
  </p>
  <p>
    The current goal is to derive each correction before primality testing,
    leaving the prime checks as independent verification only.
  </p>
</section>
</main>
</body>
</html>
"""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--text-output",
        type=Path,
        default=Path("twin_prime_square_doorway_demo.txt"),
    )
    parser.add_argument(
        "--html-output",
        type=Path,
        default=Path("twin_prime_square_doorway_demo.html"),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    chain = tuple(audit_level(level) for level in CHAIN)
    branches = tuple(audit_level(level) for level in BRANCHES)

    failed = [
        item.level.order
        for item in chain + branches
        if not item.strict
    ]

    if failed:
        raise RuntimeError(
            "Audit failed for K values: "
            + ", ".join(fmt(v) for v in failed)
        )

    text = make_text(chain, branches)
    page = make_html(chain, branches)

    args.text_output.write_text(text, encoding="utf-8")
    args.html_output.write_text(page, encoding="utf-8")

    print(text)
    print()
    print(f"Saved text report: {args.text_output.resolve()}")
    print(f"Saved HTML report: {args.html_output.resolve()}")


if __name__ == "__main__":
    main()
