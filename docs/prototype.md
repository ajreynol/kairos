# Milestone 2a: the hand-written prototype

Before generating anything, the core and two CpcMini programs were written by
hand (`Kairos/Proto/`). The goal was to fix the shape of the code and of the
proofs that `kairos-eoc` will emit. Everything here checks with Lean's three
standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## Design decisions

| Decision | Choice | Why |
| --- | --- | --- |
| Term representation | `Id := Nat` into a `Store` of `Node`s. A node is one level of Logos's `Term`, with `Term` children replaced by ids smaller than the parent's. | O(1) equality, hashing and matching; children-before-parents makes `decode` well founded |
| Meaning | `decode : Store → Id → Term`, for specification only, never run | The simulation is a plain equation against Logos |
| `Stuck` | id 0, and `Apply f Stuck` is an ordinary node | Faithful to Logos, so there is no `norm` relation (Pathos needs one) |
| Invariant | `Inv`: id 0 is `Stuck`; children precede parents; the interning table is exact; every cache entry is sound | From these: `decode_inj`, i.e. equal ids ⇔ equal terms |
| Monad | `K := EStateM Err Store`, where `Err` is resource exhaustion only | The store is threaded uniquely and updated in place |
| Logic | `Ok m σ Q`: if `m` returns, `Q` holds (errors satisfy everything) | Refinement: Kairos may give up, it may not be wrong |
| Termination | Every generated program takes a fuel `Nat`; running out is an error | Structural recursion; proofs go by induction on fuel |
| Laziness | `k_requires` evaluates its body only when the guard holds | Logos is strict but pure, so results agree; Kairos does less work |
| Cache | `cached p args body`, keyed by (program id, argument ids); soundness against a `Sem` table of Logos functions | `cached_sim` is proven once; a miss is only slower |

## How a generated proof goes

For each program, the generated proof has the same steps:

1. **Matchers.** Each pattern becomes a pure matcher `Store → Id → Option ids`,
   with a `_some` lemma (the decoded shape) and a `_none` lemma
   (`∀ vars, decode x ≠ pattern`). For CpcMini, `matchBin` and `matchUn`
   cover most patterns.
2. **Cases.** Case `k` of the Logos program is closed by rewriting with
   Lean's generated equation lemma `f.eq_k`. Its hypotheses ("not Stuck",
   "not an earlier pattern") are exactly the earlier matchers' `_none`
   lemmas. The generator knows `k` and which matchers came before.
3. **Right-hand sides.** These are chains of `Sim.bind` over builders
   (`mkBin_sim`, `mkApply_sim`), recursive calls (the induction hypothesis),
   and natives (`k_requires_sim`). After each step, earlier ids are
   transported with `decode_extends`.

`k_mk_symm_sim` is about 60 lines and `k_mk_trans_sim` about 80. Most of that
is the repeated transport of step 3, which a small tactic should absorb.

## Measurements

These are from `lake exe kairos-proto-bench`, native code, on the development
machine. Times are single runs.

**No sharing**: `__mk_trans` on a chain of N equalities.

| N | Logos build | Logos `__mk_trans` | Kairos build (intern) | Kairos `k_mk_trans` |
| --- | --- | --- | --- | --- |
| 10,000 | 0.6 ms | 1.6 ms | 18.6 ms | 5.0 ms |
| 100,000 | 4.8 ms | 16.3 ms | 162 ms | 34.2 ms |

Running the program costs 2–3× Logos. Interning costs about 0.3 µs per node,
about 30× Logos's plain allocation. A parser that interns pays that once per
distinct node.

**Sharing**: `__eo_is_closed` on a DAG of depth D (`t' = (and t t)`).

| D | distinct nodes | Logos | Kairos |
| --- | --- | --- | --- |
| 20 | 46 | 44.6 ms | 0.03 ms |
| 26 | 58 | 1,619 ms | 0.04 ms |
| 60 | 126 | (2^60 leaves) | 0.06 ms |

## Open items

- A tactic for the step-3 transport, which is about four fifths of each proof.
- Faster interning: hashing of `Node`, and table growth.
- `DatatypeDecl` is stored by value with a constant hash. It should be
  interned.
- `k_is_closed_rec` in the benchmark is hand-compiled and unverified.
