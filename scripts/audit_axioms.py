#!/usr/bin/env python3
"""Print and audit the transitive axioms of the selected contracts and public supporting theorems."""
from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


def main() -> None:
    config = json.loads((ROOT / "comparator.json").read_text())
    principal = config["theorem_names"] + config.get("definition_names", [])
    supporting = json.loads((ROOT / "verification/supporting-declarations.json").read_text())
    if not isinstance(supporting, list) or not supporting:
        raise SystemExit("Expected a nonempty supporting-declaration audit list")
    names = principal + supporting
    if len(names) != len(set(names)):
        raise SystemExit("Duplicate declaration in principal/supporting audit lists")
    module = config["solution_module"]
    if not NAME.fullmatch(module) or not all(NAME.fullmatch(n) for n in names):
        raise SystemExit("Invalid Lean names in Comparator configuration")
    work = ROOT / ".lake/verification"
    work.mkdir(parents=True, exist_ok=True)
    source = work / "AxiomAudit.lean"
    source.write_text("module\nimport SupportCriterion\nimport " + module + "\n" +
                      "\n".join("#print axioms " + n for n in names) + "\n")
    proc = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = proc.stdout
    (work / "axioms.log").write_text(output)
    print(output, end="")
    if proc.returncode:
        raise SystemExit(proc.returncode)
    result = {}
    for name in names:
        prefix = re.escape("'" + name + "'")
        matches = re.findall(prefix + r" depends on axioms:\s*\[([^]]*)\]", output)
        empty = re.findall(prefix + r" does not depend on any axioms", output)
        if len(matches) + len(empty) != 1:
            raise SystemExit(f"Missing or duplicate axiom report for {name}")
        used = set() if empty else {a.strip() for a in matches[0].split(",") if a.strip()}
        if used - ALLOWED:
            raise SystemExit(f"Unpermitted axioms for {name}: {sorted(used - ALLOWED)}")
        result[name] = sorted(used)
    (work / "axioms.json").write_text(json.dumps({
        "principal": {name: result[name] for name in principal},
        "supporting": {name: result[name] for name in supporting},
    }, indent=2) + "\n")
    print(f"Axiom audit passed for {len(principal)} principal and "
          f"{len(supporting)} supporting declarations")


if __name__ == "__main__":
    main()
