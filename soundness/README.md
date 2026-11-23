# Soundness (opt-in)

`KairosSoundness.lean` proves `correct___kairos_is_refutation`, Logos's
`correct___eo_is_refutation` with Kairos's checker in place of Logos's: if
`kairos_checker_is_refutation F C = true`, the assumptions `F` are
unsatisfiable (under Logos's two translation hypotheses). It composes Kairos's
`kairos_refines_logos` (`../verification`) with Logos's theorem.

It is a separate project because Logos's theorem lives in Logos's
`verification/` project, which needs Mathlib and builds Logos's own proofs of
CPC, which take hours. CI builds neither. Build it by hand:

```sh
cd soundness
lake update
lake build      # fetches Mathlib and builds Logos's verification: hours
```

It has not been built yet.

The Logos revision in `lakefile.toml` must be the one the root `lakefile.toml`
pins.
