#!/usr/bin/env python3
"""Check the single axiom report emitted by Verification/Axioms.lean."""

from pathlib import Path
import re
import sys


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
OPEN = "sorryAx"
TARGET = "HindmanSumsProducts.hindman_finite_sums_products"


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} AXIOM_LOG", file=sys.stderr)
        return 1

    log = Path(sys.argv[1]).read_text(encoding="utf-8")
    reports = [line for line in log.splitlines() if "depends on axioms:" in line]
    if len(reports) != 1:
        print(f"expected one axiom report, found {len(reports)}", file=sys.stderr)
        return 1

    report = reports[0]
    if TARGET not in report:
        print(f"axiom report is not for {TARGET}: {report}", file=sys.stderr)
        return 1

    match = re.search(r"depends on axioms:\s*\[([^\]]*)\]", report)
    if match is None:
        print(f"could not parse axiom report: {report}", file=sys.stderr)
        return 1

    axioms = {item.strip() for item in match.group(1).split(",") if item.strip()}
    print(f"Axioms for {TARGET}: {', '.join(sorted(axioms)) or '(none)'}")
    unexpected = axioms - ALLOWED - {OPEN}
    if unexpected:
        print(f"FAIL: unexpected axioms: {', '.join(sorted(unexpected))}", file=sys.stderr)
        return 1
    if OPEN in axioms:
        print(f"OPEN: {TARGET} depends on sorryAx; the proof is incomplete.")
        return 2

    print("PASS: all axioms are in the permitted set.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
