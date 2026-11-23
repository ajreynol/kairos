#!/usr/bin/env python3
"""Executive summary of lines of code, specification and proof in Kairos.

Reports:

  (1) The checker: the root `Kairos` library, code only. Hand-written
      (Kairos/Runtime, Kairos/Checker) apart from generated (Kairos/Gen).
  (2) The proofs: the verification project, hand-written apart from
      generated, by part; its theorems apart from its auxiliary definitions
      (the store invariant, Sim/SimR, the decodings, the generated specs).
  (3) The generator: kairos-eoc's C++ and the install scripts.
  (4) soundness/: the opt-in composition with Logos's soundness theorem.

There is no specification section: Kairos adds none. The central statement,
kairos_refines_logos, depends only on Logos's definitions, the checker's code
and Lean, which verification/KairosVerification/Statement.lean checks in the
build; the verification project's definitions are proof devices.

A "line of code" is a non-blank, non-comment line: Lean line comments `--`
and nested block comments `/- ... -/` (docstrings included) are stripped,
and C++ `//` and `/* */` comments likewise. In the verification project, a
line belongs to a proof when it is in a `theorem`/`lemma` declaration, and to
an auxiliary definition otherwise (definitions, structures, macros, ...).

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

    print("\n(2) The proofs  [the verification project]")
    groups = [
        ("hand-written runtime", "verification/KairosVerification/Runtime/*.lean"),
        ("hand-written checker", "verification/KairosVerification/Checker/*.lean"),
        ("hand-written statement check", "verification/KairosVerification/Statement.lean"),
        ("generated", "verification/KairosVerification/Gen/*.lean"),
    ]
    aux_total = thm_total = 0
    for title, pat in groups:
        files = lean_files(pat)
        a_ = t_ = 0
        rows = []
        for f in files:
            fa, ft = split_lean(loc(f))
            a_ += fa
            t_ += ft
            rows.append((fa + ft, fa, ft, rel(f)))
        aux_total += a_
        thm_total += t_
        print(f"    {title:<36} files: {len(files):>4}   lines: {a_ + t_:>8}"
              f"   (theorems {t_}, auxiliary definitions {a_})")
        if show_files:
            for n, fa, ft, r in sorted(rows, reverse=True):
                print(f"      {n:>8}  {r}")
    print(f"    {'total':<36} {'':>11}   lines: {aux_total + thm_total:>8}"
          f"   (theorems {thm_total}, auxiliary definitions {aux_total})")
    print("    Specification added by Kairos: none. The central statement depends only on")
    print("    Logos's definitions, the checker's code and Lean (checked by")
    print("    verification/KairosVerification/Statement.lean).")
    lc = logos_checker_lines()
    if lc is not None:
        print(f"    (For context: Logos's checker, Cpc.Logos and its dependencies: {lc} lines.)")

    print("\n(3) The generator")
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
        print("\n(4) Soundness  [opt-in; composes with Logos's theorem]")
        show("soundness/", snd, show_files)
    print()


if __name__ == "__main__":
    main()
