# The design of the core and of the generated proofs

This page describes the hand-written core (`Kairos/Runtime/`, its proofs in
`verification/KairosVerification/Runtime/`) and the shape of the code and
proofs that `kairos-eoc` generates (`Kairos/Gen/`,
`verification/KairosVerification/Gen/`). The shape was settled by a
hand-written prototype at milestone 2a. That prototype has since been replaced
by the generated code and is no longer in the tree.

## Design decisions

| Decision | Choice | Why |
| --- | --- | --- |
| Term representation | `Id := Nat` into a `Store` of `Node`s. A node is one level of Logos's `Term`, with `Term` children replaced by ids smaller than the parent's. `Node` is generated from `Term` (`Kairos/Gen/Term.lean`). | O(1) equality, hashing and matching; children-before-parents makes `decode` well founded |
| Meaning | `decode : Store → Id → Term`, for specification only, never run | The simulation is a plain equation against Logos |
| `Stuck` | id 0, and `Apply f Stuck` is an ordinary node | Faithful to Logos, so there is no `norm` relation (Pathos needs one) |
| Invariant | `Inv sem σ`: id 0 is `Stuck`; children precede parents; the interning table is exact; every cache entry is sound against `sem` | From these: `decode_inj`, i.e. equal ids ⇔ equal terms |
| Monad | `K := EStateM Err Store`, where `Err` is resource exhaustion (`fuel`) only | The store is threaded uniquely and updated in place |
| Logic | `Ok m σ Q`: if `m` returns, `Q` holds (errors satisfy everything). `Sim sem σ m t`: if `m` returns `r`, the invariant still holds, the store only grew, and `r` decodes to `t` | Refinement: Kairos may give up, it may not be wrong |
| Termination | Every generated program takes a fuel `Nat`; running out is an error | Structural recursion; proofs go by induction on fuel |
| Laziness | `k_ite` evaluates only the branch taken, for Logos's `__eo_ite` and `native_ite`. Everything else, `__eo_requires` included, is evaluated as Logos does | Logos is strict but pure, so results agree; Kairos does less work |
| Cache | `cached p args body`, keyed by (program id, argument ids), on each recursive program whose arguments are all terms. `kairos-eoc` chooses them from the call graph. Soundness is against a `Sem` table of Logos functions | `cached_sim` is proven once; a miss is only slower |
| Lifted programs | A program the generator does not compile yet runs Logos's own function on the decoded arguments. The generated file lists them | The checker covers all of CPC before the generator compiles every program |

## How a generated proof goes

For each program `f`, the generator emits the program `k_f`, a spec
`S_f n` (at fuel `n`, `k_f` simulates Logos's `f` on decoded arguments) and a
step lemma proving `S_f (n+1)` from the specs of its callees. `__mk_symm` in
`verification/KairosVerification/Gen/Programs.lean` is a short example.

1. **Matchers.** Each pattern becomes a pure matcher `m_f_k : Store → ids →
   Option ids`, a chain of continuation-passing steps: `leaf` and `stuck`
   (`Kairos/Runtime/Match.lean`) and one step per `Term` constructor
   (`Kairos/Gen/Prims.lean`). Each matcher has a `_some` lemma (the bound ids
   are valid and the argument decodes to the pattern) and a `_none` lemma
   (`∀ vars, decode x ≠ pattern`).
2. **Cases.** A program is a chain of `kcase`, split by `kcase_sim` one case
   at a time. Case `k` is closed by rewriting with Lean's equation lemma
   `f.eq_k` of Logos's definition. Its side conditions ("not Stuck", "not an
   earlier pattern") come from the earlier matchers' `_none` lemmas and are
   discharged by `kside`.
3. **Right-hand sides.** These are chains of `Sim.step` over interning
   (`intern_leaf`, `intern_Apply`), calls (the callee's spec, through its
   `C_f` lemma) and `k_ite_sim`. What is known about each id is a list of
   facts `Ctx σ Γ`, carried to each new store by `Ctx.mono`. This replaced
   the prototype's hand-written transport with `decode_extends`, which made
   up about four fifths of each hand-written proof.

## Prototype measurements (milestone 2a)

These numbers are from the prototype's benchmark, `kairos-proto-bench`, in
native code, as single runs. The benchmark was removed with the prototype, so
they cannot be reproduced from this tree. They are kept as the only
measurements so far, not as figures for the current checker.

**No sharing**: `__mk_trans` on a chain of N equalities.

| N | Logos build | Logos `__mk_trans` | Kairos build (intern) | Kairos `k_mk_trans` |
| --- | --- | --- | --- | --- |
| 10,000 | 0.6 ms | 1.6 ms | 18.6 ms | 5.0 ms |
| 100,000 | 4.8 ms | 16.3 ms | 162 ms | 34.2 ms |

Running the program cost 2–3× Logos. Interning cost about 0.3 µs per node,
about 30× Logos's plain allocation. A parser that interns pays that once per
distinct node.

**Sharing**: `__eo_is_closed` on a DAG of depth D (`t' = (and t t)`).

| D | distinct nodes | Logos | Kairos |
| --- | --- | --- | --- |
| 20 | 46 | 44.6 ms | 0.03 ms |
| 26 | 58 | 1,619 ms | 0.04 ms |
| 60 | 126 | (2^60 leaves) | 0.06 ms |

## Open items

- Faster interning: hashing of `Node`, and table growth.
- `DatatypeDecl` is stored by value with a constant hash
  (`Kairos/Gen/Term.lean`). It should be interned.
- A benchmark of the current checker. It needs a parser first.
