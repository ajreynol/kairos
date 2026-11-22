# Kairos

A fast CPC proof checker in Lean that is generated from CPC and proven to
refine [Logos](https://github.com/cvc5/logos). See [VISION.md](VISION.md) for
the goals, the correctness argument, and how it is compared with
[Pathos](https://github.com/daniel-larraz/pathos).

**Status: milestone 2 (CpcMini) end to end.** For CpcMini, Logos's five-rule
calculus, Kairos checks proofs and is proven to agree with Logos:
`Kairos.Checker.kairos_refines_logos` says that if Kairos's checker accepts a
refutation, so does Logos's `__eo_checker_is_refutation` (Lean's standard
axioms only). `kairos-eoc` generates the term programs and their proofs
(`Kairos/Gen/Programs.lean`: 36 of 57 programs, 2 of them lifted, 4 over
native values only). The checker (`Kairos/Checker/`) mirrors lean-meta's
fixed checker template by hand; the rule dispatch, the part of the checker
that depends on the rules, is generated (`Kairos/Gen/Dispatch.lean`). See [docs/prototype.md](docs/prototype.md)
for the design.

## Layout

| Path | What |
| --- | --- |
| `lakefile.toml`, `lake-manifest.json` | The Logos pin (package `Cpc`), the single source of truth for the CPC signature and the Ethos commit |
| `eoc/` | `kairos-eoc`, our code-generation stage, a standalone CMake project built against the pinned Ethos tree |
| `eoc/kairos_meta/` | The stage (`kairos_meta_reduce.{h,cpp}`) and its Lean templates |
| `eoc/FORK_BASE` | The upstream Ethos files the stage is forked from, and the commit they were forked at |
| `Kairos/Runtime/` | The hand-written core: store, program logic, contexts of facts, matching, program primitives |
| `Kairos/Gen/` | Generated Lean, committed, never edited by hand |
| `Kairos/Checker/` | The checker's datatypes and functions over ids, the end-to-end theorem, a smoke test |
| `Kairos/Proto/` | The prototype and the golden generated-style file |
| `install/` | Regeneration, laid out like Logos's: `get-eo-compiler.sh`, `install-cpc.sh` |
| `scripts/` | `fork-drift.sh`, `logos-rev.sh` |

## Building

Requirements: elan, cmake >= 3.12, a C++17 compiler, GMP headers
(`libgmp-dev`), python3, curl or wget.

```sh
install/get-eo-compiler.sh   # the pinned Logos, its Ethos, ethos-eoc and kairos-eoc
install/install-cpc.sh       # regenerate Kairos/Gen/  (--check: verify only)
lake build                   # Kairos and its proofs
```

See [install/README.md](install/README.md) for what these do and how to move
the Logos pin.
