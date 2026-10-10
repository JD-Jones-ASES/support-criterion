#!/usr/bin/env python3
"""Replay two rejected mutations of the analytic measure bridge.

Run after `lake build`. Baselines must compile, and each altered coefficient
must fail at its expected proof site; dependency or environmental failures do
not count as successful negative controls.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CASES = [
    (
        "strong_chord_coefficient",
        "SupportCriterion/Chord.lean",
        "    (x ^ 2 - lowerSq) * (upperSq - x ^ 2) * t ^ 4 / 24 ≤",
        "    (x ^ 2 - lowerSq) * (upperSq - x ^ 2) * t ^ 4 / 23 ≤",
        "Type mismatch",
    ),
    (
        "intrinsic_deficit_coefficient",
        "SupportCriterion/LawGap.lean",
        "fourthDeficit μ * t ^ 4 / 48000",
        "fourthDeficit μ * t ^ 4 / 47999",
        "linarith failed to find a contradiction",
    ),
]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake") or str(Path.home() / ".elan/bin/lake"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results = []
    with tempfile.TemporaryDirectory(prefix="support-criterion-negative-") as work:
        for name, relative, old, new, expected in CASES:
            source = (ROOT / relative).read_text()
            if old not in source:
                raise RuntimeError(f"Mutation target missing in {relative}")
            baseline = subprocess.run(
                [args.lake, "env", "lean", relative], cwd=ROOT,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300,
            )
            mutant_path = Path(work) / f"{name}.lean"
            mutant_path.write_text(source.replace(old, new, 1))
            mutant = subprocess.run(
                [args.lake, "env", "lean", str(mutant_path)], cwd=ROOT,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300,
            )
            rejected = mutant.returncode != 0 and expected in mutant.stdout and "error:" in mutant.stdout
            valid = baseline.returncode == 0 and rejected
            results.append({
                "name": name,
                "source": relative,
                "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                "baseline_exit": baseline.returncode,
                "mutant_exit": mutant.returncode,
                "expected_diagnostic": expected,
                "expected_rejection": valid,
                "baseline_output": baseline.stdout,
                "mutant_output": mutant.stdout.replace(work, "<temporary-directory>"),
            })
    report = {"passed": all(item["expected_rejection"] for item in results), "controls": results}
    output = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    print(output, end="")
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
