# Kairos

A fast CPC proof checker in Lean that is generated from CPC and proven to
refine [Logos](https://github.com/cvc5/logos). See [VISION.md](VISION.md) for
the goals, the correctness argument, and how it is compared with
[Pathos](https://github.com/daniel-larraz/pathos).

**Status: milestone 2 (CpcMini) in progress.** `kairos-eoc` generates
Kairos programs with machine-checked proofs that they compute Logos's
functions (`Kairos/Gen/Programs.lean`). It currently covers 36 of CpcMini's 57
programs, including the five rules and `__eo_typeof`; what remains is the
checker's state machine. The hand-written runtime the
generated code builds on is in `Kairos/Runtime/`; `Kairos/Proto/` holds the
prototype and the golden output the generator was written against (see
[docs/prototype.md](docs/prototype.md)).

## Layout

| Path | What |
| --- | --- |
| `lakefile.toml`, `lake-manifest.json` | The Logos pin (package `Cpc`), the single source of truth for the CPC signature and the Ethos commit |
| `eoc/` | `kairos-eoc`, our code-generation stage, a standalone CMake project built against the pinned Ethos tree |
| `eoc/kairos_meta/` | The stage (`kairos_meta_reduce.{h,cpp}`) and its Lean templates |
| `eoc/FORK_BASE` | The upstream Ethos files the stage is forked from, and the commit they were forked at |
| `Kairos/Runtime/` | The hand-written core: store, program logic, contexts of facts, matching, program primitives |
| `Kairos/Gen/` | Generated Lean, committed, never edited by hand |
| `Kairos/Proto/` | The prototype and the golden generated-style file |
| `scripts/` | `get-deps.sh`, `generate.sh`, `fork-drift.sh`, `logos-rev.sh`, `gen-mini.sh` (development loop) |

## Building

Requirements: elan, cmake >= 3.12, a C++17 compiler, GMP headers
(`libgmp-dev`), python3, curl or wget.

```sh
lake update Cpc            # only if .lake/packages/Cpc is missing
scripts/get-deps.sh        # Ethos at Logos's pin -> ethos-eoc; then kairos-eoc
scripts/generate.sh        # regenerate Kairos/Gen/  (--check: verify only)
lake build
```

`generate.sh` runs Logos's own Lean pipeline on Logos's
`install/defs/Cpc.cached.eo`. It checks that the Lean it produces is Logos's
committed `Cpc/` byte for byte, apart from the header Logos's
`install-sig.sh` adds. It then runs `kairos-eoc` on the same final signature.
So Kairos is always compiled from exactly the input Logos was.

## Moving the Logos pin

1. Change `rev` in `lakefile.toml`, then `lake update Cpc`.
2. `scripts/get-deps.sh` (rebuilds `ethos-eoc` at the new Ethos commit).
3. `scripts/fork-drift.sh`: review upstream changes to the forked files, port
   them, and update `eoc/FORK_BASE`.
4. `scripts/generate.sh`, then `lake build`, then commit `Kairos/Gen/`.
