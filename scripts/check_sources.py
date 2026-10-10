#!/usr/bin/env python3
"""Check the committed package's source contract, before compiling it.

Reference: PalomarPolicy 96b034cc31a72a63d4f4041911dce337a85c9a04,
CONTRIBUTING.md sections 2.1--2.5. This is a local preparation check;
it does not replace Palomar's own complete verifier or editorial review.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
SHA = re.compile(r"[0-9a-f]{40}\Z")
PUBLIC_GIT = re.compile(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\Z")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
COMPILED = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}


def fail(message: str) -> None:
    raise SystemExit(message)


def code_only(text: str) -> str:
    """Blank comments and string literals, preserving line breaks and positions."""
    out = list(text)
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                out[i:i + 2] = " " * len(text[i:i + 2])
                i += 2
            else:
                if text[i] == '"':
                    string = False
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            i += 1
    if depth or string:
        fail("Unterminated Lean comment or string")
    return "".join(out)


def main() -> None:
    config = json.loads((ROOT / "comparator.json").read_text())
    required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    if not required <= config.keys() or config.keys() - required - {"definition_names", "enable_nanoda"}:
        fail("Unexpected Comparator configuration keys")
    modules = [config["challenge_module"], config["solution_module"]]
    if modules[0] == modules[1] or not all(isinstance(n, str) and NAME.fullmatch(n) for n in modules):
        fail("Challenge and Solution must be distinct unambiguous module names")
    names = config["theorem_names"] + config.get("definition_names", [])
    if not config["theorem_names"] or len(names) != len(set(names)) or not all(NAME.fullmatch(n) for n in names):
        fail("Invalid or duplicate compared declaration names")
    if set(config["permitted_axioms"]) != ALLOWED:
        fail("The configured axiom allowance differs from the three standard axioms")
    challenge = ROOT / (modules[0].replace(".", "/") + ".lean")
    solution = ROOT / (modules[1].replace(".", "/") + ".lean")
    for file in (challenge, solution):
        if file.is_symlink() or not file.is_file():
            fail(f"Missing regular project source: {file.relative_to(ROOT)}")

    count = 0
    def project_files():
        for directory, dirs, files in os.walk(ROOT):
            dirs[:] = [name for name in dirs if name not in {".git", ".lake", "__pycache__"}]
            for name in files:
                yield Path(directory) / name

    for file in project_files():
        relative = file.relative_to(ROOT)
        if file.suffix in COMPILED and file.is_file():
            fail(f"Compiled artifact outside .lake: {relative}")
        if file.suffix != ".lean":
            continue
        if file.is_symlink() or not file.is_file():
            fail(f"Lean source is not a regular file: {relative}")
        text = file.read_text()
        code = code_only(text)
        count += 1
        if len(text.splitlines()) > 10000:
            fail(f"Lean source exceeds 10,000 physical lines: {relative}")
        if file.name != "lakefile.lean" and not re.match(r"\s*module\b", code):
            fail(f"Missing module header: {relative}")
        forbidden = r"\b(?:axiom|native_decide|admit)\b"
        if file != challenge:
            forbidden = r"\b(?:axiom|native_decide|admit|sorry)\b"
        if re.search(forbidden, code):
            fail(f"Unpermitted proof construct in {relative}")
    text = challenge.read_text()
    if len(text.encode()) > 100 * 1024 or len(text.splitlines()) > 1000:
        fail("Challenge exceeds the source contract")
    code = code_only(text)
    for line in code.splitlines():
        match = re.match(r"\s*(?:public\s+)?import\s+(.+)", line)
        if match:
            for name in match.group(1).split():
                if not (name == "Mathlib" or name.startswith("Mathlib.") or name == "Init" or name.startswith("Init.")):
                    fail(f"Challenge imports a project-specific dependency: {name}")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = []
    for package in manifest["packages"]:
        if package["type"] != "git" or not SHA.fullmatch(package["rev"]) or not PUBLIC_GIT.fullmatch(package["url"]):
            fail(f"Dependency lacks an exact public Git pin: {package['name']}")
        if package["name"] == "mathlib":
            mathlib.append(package)
    if len(mathlib) != 1 or mathlib[0]["url"].removesuffix(".git") != "https://github.com/leanprover-community/mathlib4":
        fail("Expected one canonical Mathlib dependency")
    selected = (ROOT / "lean-toolchain").read_text().strip()
    if not re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(?:-rc[0-9]+)?", selected):
        fail("Expected an exact released Lean toolchain")
    mathlib_toolchain = ROOT / ".lake/packages/mathlib/lean-toolchain"
    if mathlib_toolchain.exists() and mathlib_toolchain.read_text().strip() != selected:
        fail("Lean and pinned Mathlib use different toolchains")
    if (ROOT / ".gitmodules").exists():
        fail("Submodules are not part of this package")
    licenses = [p for p in ROOT.iterdir() if re.fullmatch(r"(?:LICEN[CS]E|COPYING|UNLICENSE|OFL)(?:\.(?:md|markdown|txt))?", p.name, re.I)]
    if len(licenses) != 1 or licenses[0].is_symlink() or not licenses[0].read_text().startswith("MIT License"):
        fail("Expected exactly one regular MIT licence file")
    print(f"Source contract passed: {count} Lean files; {len(names)} compared declarations; {selected}")


if __name__ == "__main__":
    main()
