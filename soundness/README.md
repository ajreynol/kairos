# Soundness (opt-in)

`KairosSoundness.lean` composes Kairos's refinement theorem
(`kairos_refines_logos`, proved in `../verification`) with Logos's
`correct___eo_is_refutation`, which says that a refutation Logos's checker
accepts has unsatisfiable assumptions.

It is a separate project because Logos's theorem lives in Logos's
`verification/` project, which needs Mathlib and builds Logos's own proofs of
CPC, which take hours. CI builds neither. Build it by hand:

```sh
cd soundness
lake update
lake build      # fetches Mathlib and builds Logos's verification: hours
```

The Logos revision in `lakefile.toml` must be the one the root `lakefile.toml`
pins.
