#!/usr/bin/env python3
"""Run bundled Comparator, Lean, NanoDa, and con-ron under its normal sandbox.

Kernel selection follows PalomarSubmission at
d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44. The saved intake configuration
is unchanged; the extra kernels belong to a generated verification config.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
LEAN_VERSION = "leanprover/lean4:v4.35.0-rc3"


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main() -> None:
    if platform.system() != "Linux":
        raise SystemExit("The authoritative Comparator and independent-kernel run requires Linux")
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    if toolchain != LEAN_VERSION:
        raise SystemExit("Update the audited release pin before changing the verification toolchain")
    prefix = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"], cwd=ROOT, text=True).strip())
    tools = {name: prefix / "bin" / name for name in
             ("lake", "lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron")}
    if any(not path.is_file() or not os.access(path, os.X_OK) for path in tools.values()):
        raise SystemExit("The selected release lacks a required bundled checker")
    work = ROOT / ".lake/verification"
    work.mkdir(parents=True, exist_ok=True)
    config = json.loads((ROOT / "comparator.json").read_text())
    config.pop("enable_nanoda", None)
    config["external_kernels"] = {
        "nanoda": [str(tools["nanoda_bin"])],
        "con-ron": [str(tools["con-ron"]), "--jobs=2"],
    }
    path = work / "comparator-with-kernels.json"
    path.write_text(json.dumps(config, indent=2) + "\n")
    sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    record = {"candidate_sha": sha, "toolchain": toolchain, "lean_source_commit": LEAN_COMMIT,
              "platform": platform.platform(), "tool_sha256": {n: digest(p) for n, p in tools.items()},
              "manifest_sha256": digest(ROOT / "lake-manifest.json"),
              "comparator_config_sha256": digest(ROOT / "comparator.json"),
              "external_kernels": config["external_kernels"], "status": "running"}
    bwrap = os.environ.get("COMPARATOR_BWRAP")
    if bwrap:
        record["bwrap_sha256"] = digest(Path(bwrap))
    record_path = work / "kernels.json"
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    command = [str(tools["lake"]), "comparator", "--config", str(path)]
    record["command"] = command
    with (work / "comparator.log").open("w") as log:
        process = subprocess.Popen(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, bufsize=1)
        assert process.stdout is not None
        for line in process.stdout:
            print(line, end="", flush=True)
            log.write(line)
            log.flush()
        code = process.wait()
    output = (work / "comparator.log").read_text()
    expected = [name + " kernel accepts the solution" for name in ("Lean default", "nanoda", "con-ron")]
    record["exit_code"] = code
    record["kernel_acceptance"] = {name: name in output for name in expected}
    passed = code == 0 and all(record["kernel_acceptance"].values())
    record["status"] = "passed" if passed else "failed"
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    if not passed:
        raise SystemExit(code or 1)
    print("Comparator statement comparison, axiom checks, and all three kernel replays passed")


if __name__ == "__main__":
    main()
