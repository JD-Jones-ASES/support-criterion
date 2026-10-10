"""Reject corrupted sharp-gap certificate data using exact arithmetic.

These controls exercise the generator's verifier, while the separately named
independent checker reconstructs the whole certificate by another algorithm.
Lean checks all displayed cell identities and coefficient signs independently.
"""
from fractions import Fraction as F
from pathlib import Path
import json

from generate_sharp_gap_certificate import (
    add, derive_polynomial, generate_certificate, quantitative_polynomial,
    verify_cell, verify_certificate,
)


def rejected(name, check):
    try:
        check()
    except ValueError as error:
        return {"name": name, "status": "REJECTED", "reason": str(error)}
    raise ValueError(f"Negative control was accepted: {name}")


def main():
    poly = quantitative_polynomial(derive_polynomial())
    coefficients = generate_certificate(poly)
    first = coefficients[:45]
    verify_cell(poly, 0, 0, first)
    perturbed = first.copy()
    perturbed[0] += F(1, 10**12)
    negative = first.copy()
    negative[0] = -F(1, 10**12)
    controls = [
        rejected("changed positive coefficient", lambda: verify_cell(poly, 0, 0, perturbed)),
        rejected("negative coefficient", lambda: verify_cell(poly, 0, 0, negative)),
        rejected("missing coefficient", lambda: verify_cell(poly, 0, 0, first[:-1])),
        rejected("wrong cell placement", lambda: verify_cell(poly, 0, 1, first)),
        rejected("changed compact polynomial", lambda: verify_cell(
            add(poly, {(0, 0): F(1, 10**12)}), 0, 0, first)),
        rejected("missing cell", lambda: verify_certificate(poly, coefficients[:-45])),
    ]
    report = {"status": "PASS", "positive_cell_control": "PASS", "controls": controls}
    out = Path(__file__).resolve().parents[1] / "verification" / "sharp_gap_negative_controls.json"
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
