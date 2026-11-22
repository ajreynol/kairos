# Kairos

A fast CPC proof checker in Lean that is generated from CPC and proven to
refine [Logos](https://github.com/cvc5/logos). See [VISION.md](VISION.md) for
the goals, the correctness argument, and how it is compared with
[Pathos](https://github.com/daniel-larraz/pathos).

**Status: full CPC.** Kairos checks proofs in the CPC calculus of the pinned
Logos (all 616 rules), and is proven to agree with Logos:
`Kairos.Checker.kairos_refines_logos` says that if Kairos's checker accepts a
refutation, so does Logos's `__eo_checker_is_refutation` (Lean's standard
axioms only). `kairos-eoc` generates the term programs (1111 of 1140; 19 of
them lifted, i.e. computed by Logos on decoded arguments, and listed in the
generated file), the rule dispatch, and all their proofs. The checker's
template part is mirrored by hand (`Kairos/Checker/`). There is no parser or
executable yet.

## Three projects

Laid out like Logos (checker apart from verification):

| Project | What | Needs | CI |
| --- | --- | --- | --- |
| `.` (`Kairos`) | the checker: code only | Logos's `Cpc` definitions | yes |
| `verification/` (`KairosVerification`) | Kairos's proofs, up to `kairos_refines_logos` | the checker, Logos's definitions (no Mathlib) | yes |
| `soundness/` (`KairosSoundness`) | composition with Logos's `correct___eo_is_refutation` | Logos's `verification/`, Mathlib | no; by hand |

## Layout

| Path | What |
| --- | --- |
| `lakefile.toml`, `lake-manifest.json` | The Logos pin (package `Cpc`), the single source of truth for the CPC signature and the Ethos commit |
| `eoc/` | `kairos-eoc`, our code-generation stage, a standalone CMake project built against the pinned Ethos tree |
| `eoc/kairos_meta/` | The stage (`kairos_meta_reduce.{h,cpp}`) and its Lean templates |
| `eoc/FORK_BASE` | The upstream Ethos files the stage is forked from, and the commit they were forked at |
| `Kairos/Runtime/`, `Kairos/Checker/` | Hand-written code: the store, matching and program primitives; the checker's datatypes and functions |
| `Kairos/Gen/` | Generated code, committed, never edited by hand |
| `verification/KairosVerification/` | The proofs: the same layout, `Gen/` generated |
| `soundness/` | The opt-in composition with Logos's soundness theorem |
| `install/` | Regeneration, laid out like Logos's: `get-eo-compiler.sh`, `install-cpc.sh` |
| `scripts/` | `fork-drift.sh`, `logos-rev.sh` |

## Building

Requirements: elan, cmake >= 3.12, a C++17 compiler, GMP headers
(`libgmp-dev`), python3, curl or wget.

```sh
install/get-eo-compiler.sh   # the pinned Logos, its Ethos, ethos-eoc and kairos-eoc
install/install-cpc.sh       # regenerate Kairos/Gen/  (--check: verify only)
lake build                   # the checker (under a minute)
(cd verification && lake build)   # its proofs
```

See [install/README.md](install/README.md) for what these do and how to move
the Logos pin.
