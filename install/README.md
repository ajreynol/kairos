# Regenerating Kairos

`Kairos/Gen/` is compiled from the CPC signature of the Logos that
`lake-manifest.json` pins, never written by hand. This directory is what does
that, laid out like Logos's own `install/`:

```text
install/install-cpc.sh       regenerate Kairos/Gen/ (--check: only compare)
install/get-eo-compiler.sh   fetch the pinned Logos and its Ethos; build both compilers
install/deps/                Logos, Ethos, ethos-eoc and kairos-eoc, ignored by git
```

## Usage

```bash
install/get-eo-compiler.sh          # once, and after moving the Logos pin
install/install-cpc.sh              # regenerate Kairos/Gen/
install/install-cpc.sh --check      # is Kairos/Gen/ what the pin compiles to?
lake build                          # build Kairos and check its proofs
```

There is no signature to pass. Kairos is compiled from exactly what Logos's
checker was: Logos's recorded copy of the signature,
`install/defs/Cpc.cached.eo`, in the Logos that `get-eo-compiler.sh`
downloaded at the pinned revision. (`--cached` is accepted, for symmetry with
Logos; it is the only mode.)

## What a run does

`get-eo-compiler.sh`:

1. downloads Logos at the revision `lake-manifest.json` pins into
   `install/deps/logos`;
2. runs that Logos's own `install/get-eo-compiler.sh`, which fetches Ethos at
   the commit Logos pins and builds `ethos-eoc`, into `install/deps/eoc`;
3. builds `kairos-eoc` (the stage in `eoc/`) against that Ethos tree, into
   `install/deps/kairos-eoc`;

and records the paths in `install/deps/eoc-env.sh`.

`install-cpc.sh`:

1. runs Logos's Lean pipeline (Ethos's `tools/eoc/driver.py`, with Logos's
   semantics) on Logos's cached signature, for `Cpc` and for `CpcMini`;
2. checks that the Lean it yields is Logos's committed `Cpc/` and `CpcMini/`,
   modulo the header and module name Logos's `install-sig.sh` adds. If not,
   the final signature would not be the one Logos's checker was compiled
   from, and the run fails;
3. runs `kairos-eoc` on Cpc's final signature, and installs (or, under
   `--check`, compares) `Kairos/Gen/`.

It exits 0 when it did what it was asked (under `--check`: when `Kairos/Gen/`
is up to date) and 1 otherwise. CI runs `--check` on every push (the
`regeneration` job).

## Moving the Logos pin

1. Change `rev` in `lakefile.toml`, then `lake update Cpc`.
2. `install/get-eo-compiler.sh` (Logos and Ethos at the new pin).
3. `scripts/fork-drift.sh`: review upstream changes to the Ethos files the
   stage mirrors, port them, and update `eoc/FORK_BASE`.
4. `install/install-cpc.sh`, then `lake build`, then commit `Kairos/Gen/`.
