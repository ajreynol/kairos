#!/usr/bin/env python3
"""Executive summary of lines of code, specification and proof in Kairos.

Reports:

  (1) The checker: the root `Kairos` library, code only. Hand-written
      (Kairos/Runtime, Kairos/Checker) apart from generated (Kairos/Gen).
  (2) The specification kairos_refines_logos is stated against: the
      definitions of the verification project (Inv, Sim/SimR, the
      representations and decodings, the cache meaning `sem`, ...). For
      context, also the size of Logos's checker definitions the statement
      refers to (Cpc.Logos and its dependencies, in the pinned Logos).
  (3) The proofs: the theorems of the verification project, hand-written
      apart from generated, by part.
  (4) The generator: kairos-eoc's C++ and the install scripts.
  (5) soundness/: the opt-in composition with Logos's soundness theorem.

A "line of code" is a non-blank, non-comment line: Lean line comments `--`
and nested block comments `/- ... -/` (docstrings included) are stripped,
and C++ `//` and `/* */` comments likewise. In the verification project, a
line belongs to a proof when it is in a `theorem`/`lemma` declaration, and to
the specification otherwise (definitions, structures, macros, ...).

Usage:
  scripts/kairos-loc-summary.py            # the summary
  scripts/kairos-loc-summary.py --files    # also every file with its LOC
"""

from __future__ import annotations

import glob
import os
import re
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(SCRIPT_DIR)


def strip_lean(text: str) -> list[str]:
    """The non-blank lines of `text` with Lean comments removed."""
    out = []
    depth = 0
    for line in text.split("\n"):
        res = []
        i = 0
        while i < len(line):
            if depth > 0:
                if line.startswith("/-", i):
                    depth += 1
                    i += 2
                elif line.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            elif line.startswith("/-", i):
                depth += 1
                i += 2
            elif line.startswith("--", i):
                break
            elif line[i] == '"':
                # a string literal: copy it whole, so that `--` in it is kept
                j = i + 1
                while j < len(line) and line[j] != '"':
                    j += 2 if line[j] == "\\" else 1
                res.append(line[i : j + 1])
                i = j + 1
            else:
                res.append(line[i])
                i += 1
        s = "".join(res)
        if s.strip():
            out.append(s)
    return out


def strip_cpp(text: str) -> list[str]:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    out = []
    for line in text.split("\n"):
        s = re.sub(r"//.*", "", line)
        if s.strip():
            out.append(s)
    return out


def strip_shell(text: str) -> list[str]:
    return [l for l in text.split("\n") if l.strip() and not l.strip().startswith("#")]


DECL = re.compile(
    r"^(@\[[^\]]*\]\s*)?(private\s+|protected\s+)?(noncomputable\s+)?"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|macro|class|example)\b"
)
STRUCTURAL = re.compile(r"^(namespace|end|open|variable|section|set_option|import|mutual)\b")


def split_lean(lines: list[str]) -> tuple[int, int]:
    """(specification lines, proof lines) of comment-stripped Lean lines."""
    spec = proof = 0
    cur = "spec"
    for l in lines:
        m = DECL.match(l)
        if m:
            cur = "proof" if m.group(4) in ("theorem", "lemma", "example") else "spec"
        elif STRUCTURAL.match(l):
            cur = "spec"
        if cur == "proof":
            proof += 1
        else:
            spec += 1
    return spec, proof


def lean_files(pattern: str) -> list[str]:
    return sorted(glob.glob(os.path.join(ROOT, pattern), recursive=True))


def loc(path: str) -> list[str]:
    text = open(path, encoding="utf-8").read()
    if path.endswith(".lean"):
        return strip_lean(text)
    if path.endswith((".cpp", ".h")):
        return strip_cpp(text)
    return strip_shell(text)


def rel(path: str) -> str:
    return os.path.relpath(path, ROOT)


def show(title: str, files: list[str], show_files: bool, width: int = 8) -> int:
    total = 0
    rows = []
    for f in files:
        n = len(loc(f))
        total += n
        rows.append((n, rel(f)))
    print(f"    {title:<44} files: {len(files):>4}   lines: {total:>{width}}")
    if show_files:
        for n, r in sorted(rows, reverse=True):
            print(f"      {n:>8}  {r}")
    return total


def logos_checker_lines() -> int | None:
    """Cpc.Logos and its dependencies in the pinned Logos (Lake's checkout)."""
    base = os.path.join(ROOT, ".lake", "packages", "Cpc", "Cpc")
    mods = ["Logos", "LogosTerm", "LogosTermOrder", "SmtEval"]
    paths = [os.path.join(base, m + ".lean") for m in mods]
    if not all(os.path.exists(p) for p in paths):
        return None
    return sum(len(loc(p)) for p in paths)


def main() -> None:
    show_files = "--files" in sys.argv[1:]
    bar = "=" * 70
    print(bar)
    print("Kairos executive summary  (LOC = non-blank, non-comment lines)")
    print(bar)

    print("\n(1) The checker  [root Kairos library: code only]")
    hand_rt = lean_files("Kairos/Runtime/*.lean")
    hand_ck = lean_files("Kairos/Checker/*.lean")
    gen = lean_files("Kairos/Gen/*.lean")
    a = show("hand-written runtime (Kairos/Runtime)", hand_rt, show_files)
    b = show("hand-written checker (Kairos/Checker)", hand_ck, show_files)
    c = show("generated (Kairos/Gen)", gen, show_files)
    print(f"    {'total':<44} {'':>11}   lines: {a + b + c:>8}")

    print("\n(2) The specification  [definitions of the verification project]")
    print("    (what kairos_refines_logos is stated against, apart from Logos)")
    groups = [
        ("hand-written runtime", "verification/KairosVerification/Runtime/*.lean"),
        ("hand-written checker", "verification/KairosVerification/Checker/*.lean"),
        ("generated", "verification/KairosVerification/Gen/*.lean"),
    ]
    spec_total = proof_total = 0
    proof_rows = []
    for title, pat in groups:
        files = lean_files(pat)
        s = p = 0
        rows = []
        for f in files:
            fs, fp = split_lean(loc(f))
            s += fs
            p += fp
            rows.append((fs, fp, rel(f)))
        spec_total += s
        proof_total += p
        proof_rows.append((title, files, p, rows))
        print(f"    {title:<44} files: {len(files):>4}   lines: {s:>8}")
        if show_files:
            for fs, _, r in sorted(rows, reverse=True):
                print(f"      {fs:>8}  {r}")
    print(f"    {'total':<44} {'':>11}   lines: {spec_total:>8}")
    lc = logos_checker_lines()
    if lc is not None:
        print(f"    {'for context: Logos checker (Cpc.Logos + deps)':<44} {'':>11}   lines: {lc:>8}")

    print("\n(3) The proofs  [theorems of the verification project]")
    for title, files, p, rows in proof_rows:
        print(f"    {title:<44} files: {len(files):>4}   lines: {p:>8}")
        if show_files:
            for _, fp, r in sorted(rows, key=lambda x: -x[1]):
                print(f"      {fp:>8}  {r}")
    print(f"    {'total':<44} {'':>11}   lines: {proof_total:>8}")

    print("\n(4) The generator")
    cpp = sorted(glob.glob(os.path.join(ROOT, "eoc", "**", "*.cpp"), recursive=True)
                 + glob.glob(os.path.join(ROOT, "eoc", "**", "*.h"), recursive=True))
    tmpl = lean_files("eoc/**/*.lean")
    sh = sorted(glob.glob(os.path.join(ROOT, "install", "*.sh"))
                + glob.glob(os.path.join(ROOT, "scripts", "*.sh")))
    show("kairos-eoc (C++)", cpp, show_files)
    if tmpl:
        show("templates (Lean)", tmpl, show_files)
    show("install and helper scripts (shell)", sh, show_files)

    snd = lean_files("soundness/*.lean")
    if snd:
        print("\n(5) Soundness  [opt-in; composes with Logos's theorem]")
        show("soundness/", snd, show_files)
    print()


if __name__ == "__main__":
    main()
