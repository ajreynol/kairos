# Kairos: vision

## In one sentence

Kairos is a CPC proof checker written in Lean and generated from CPC. It is
built for speed: terms are hash-consed and side-condition results are cached.
It is proven to compute what [Logos](https://github.com/cvc5/logos) computes,
so it inherits Logos's soundness theorem and trusts exactly what Logos trusts.

## Why it exists

Kairos is an experiment. [Pathos](https://github.com/daniel-larraz/pathos)
already builds a fast, generated CPC checker in Rust (Ethos's `rust-meta`
stage) and plans to prove it equivalent to Logos through Charon and Aeneas.
Kairos makes the same bet in Lean. The question is how useful Rust is compared
with Lean for this kind of artifact, measured on:

- **speed**, where Rust is expected to win and we accept that;
- **trust**: what each checker's guarantee rests on beyond Logos's own
  trusted base;
- **proof cost**: how much of the equivalence proof is automatic, how much is
  written by hand, and what it costs to keep it working as CPC changes;
- **composability**: whether other verified Lean developments can call the
  fast checker and keep their theorems.

Beating Pathos's times is not a goal. Being far faster than Logos is.

## What Kairos is

1. **Generated from CPC, with nothing written per rule.** A vendored compiler
   stage, `kairos_meta_reduce.cpp` (forked from Ethos's
   `plugins/lean_meta/lean_meta_reduce.cpp`), compiles CPC into Kairos's Lean
   source. The generated code mirrors Logos's generated code function by
   function, which is what makes the equivalence proof generatable too.
2. **Pinned to Logos.** Kairos pins one Logos commit as a Lake dependency.
   Through that pin it uses the same `Cpc.cached.eo` and the same Ethos commit
   (`ETHOS_VERSION` in Logos's `install/get-eo-compiler.sh`). Our stage is
   built as its own binary, `kairos-eoc`, out of Ethos's tree but against
   that commit. It uses Ethos's plugin CMake infrastructure
   (`cmake/EthosPlugin.cmake`), so Ethos is not patched. The stage runs only
   the last step, on the exact `lean-cpc-final.eo` that Logos's `lean-meta`
   stage compiles, and the pipeline checks that this input reproduces Logos's
   committed `Cpc/`. Upgrading means bumping the Logos pin, regenerating,
   reviewing upstream drift in the forked files (`scripts/fork-drift.sh`),
   and re-checking. The C++ is ours and lives here; what we need from Ethos
   we ask for as features.
3. **Fast by construction.**
   - *Hash-consed terms.* A term is an ID into a monotonically growing store.
     Equality, hashing and pattern matching (including non-linear patterns)
     are O(1) ID comparisons.
   - *Memoized side conditions.* Program results are cached, keyed by
     (program, all argument IDs), across the whole proof. Typing has a cache
     row for each term.
   - *Sharing kept from the start.* Proofs are parsed straight into the store,
     so `let`/`define` sharing is never expanded into a tree.
4. **Proven equivalent to Logos, not proven sound rule by rule.** Kairos
   proves nothing about SMT semantics or about individual rules. It proves
   that it simulates Logos (below).

### The performance invariant

"No tree traversals" means this precisely: **no operation costs more than the
number of distinct subterms of its inputs (their DAG size), and each
(program, arguments) pair is evaluated at most once per run, apart from cache
eviction.** Some CPC side conditions are traversals by nature, such as
substitution, list operations and evaluation. The invariant bounds them by DAG
size; it does not make them free.

## Correctness

### The theorem

The top theorem is refinement, on parsed assumptions and commands:

```lean
theorem kairos_refines_logos (F : CArgList) (C : CCmdList) :
    kairos_checker_is_refutation F C = true → __eo_checker_is_refutation F C = true
```

Combined with Logos's `correct___eo_is_refutation`, this gives soundness of
Kairos (`correct___kairos_is_refutation`, in `soundness/`). Refinement is all
soundness needs. It lets Kairos answer "incomplete" where Logos would decide,
for example when Kairos runs out of a resource. Full equivalence, the converse
included, is a later completeness goal.

There is no parser yet. Once there is, a theorem about the text of a proof
file needs a parser-agreement statement against Logos's parser if Kairos
reads straight into the store. If proving that turns out to be expensive, the
fallback is to treat the parser as outside the theorem, as both Logos and
Pathos do for their front ends.

### How it is proven

There are two layers:

- **The hand-written core, independent of CPC and proven once:**
  - the store invariant: an ID decodes to exactly one `Eo.Term`; equal IDs
    mean equal terms and the converse; decoding stays the same as the store
    grows;
  - cache soundness: every entry is its program's result on the decoded
    arguments (a lookup that misses is slower, not wrong);
  - compiled pattern matching agrees with Logos's `match`, including
    non-linear patterns;
  - stuck results, failure and fuel are handled the same way as in Logos;
  - one lemma per store operation, for the step after it.
- **The generated layer, one simulation lemma per generated function:** at
  every fuel, if `kairos_f` returns, its result decodes to `logos_f` of the
  decoded arguments (`Sim`). The lemma and its proof are both emitted by
  `kairos_meta_reduce.cpp`; [design.md](design.md) shows how such a proof
  goes. **If a generated proof fails on a function, that is a bug in the code
  generator, not a proof to write by hand.** This is what keeps Kairos as
  agile as CPC.

### Design rules, from Pathos's findings

- **Represent `Stuck` exactly as Logos does.** Pathos's store refuses to
  build an application with a stuck argument, while Logos builds
  `Apply f Stuck`. In CpcMini alone this gave three places where the two
  differ, and it forced a `norm` function plus an extra lemma per function.
  Kairos stores whatever Logos would build, so the simulation is a plain
  equation.
- **Cache only completed results.** `Stuck` is a legitimate cached result.
  Errors, exhausted budgets and unfinished calls are never cached.
- **Mind laziness.** Memoization must not make Kairos compute something that
  Logos would not reach (lazy `ite`). The equation is stated
  against Logos's evaluation order.
- **Choose what to cache from the call graph.** Following `rust_meta`'s
  analysis, `kairos-eoc` caches programs in recursive cycles that take terms
  as arguments, and keeps the lookup cost off non-recursive helpers.
- **Trust nothing beyond Logos.** No `unsafe`, no pointer equality, no
  `@[implemented_by]` outside an explicit allowlist. The allowlist is empty
  and none is used today; no script checks this yet.

## Consumers

1. **The `kairos` executable**, a drop-in for `logos`: the same input, the
   same verdicts (`correct` / `incorrect` / `incomplete`), and the same exit
   codes.
2. **A fast oracle for [Telos](https://github.com/ajreynol/telos).** Telos
   calls Logos's generated functions at run time, mainly `__eo_to_smt`,
   `__eo_mk_apply`, `__eo_typeof`, `__eo_invoke_cmd_list` and `__eo_prog_*`.
   Those are tree-recursive and too slow on large, shared terms. Kairos can
   offer the same functions on IDs, each with its simulation lemma, so Telos
   can switch implementations and rewrite its proofs through the lemma
   instead of re-proving anything. Two consequences:
   - Kairos is a **library first**. It exports a stable API of store, intern,
     decode and the generated functions, and the executable is one client of
     it.
   - The boundary must not reintroduce tree traversals. Telos nodes are DAGs,
     so they should be interned into the Kairos store directly, memoized per
     node, with a lemma that this agrees with Telos's existing translation to
     Logos terms. They should not go through `Eo.Term`.

   This is the part of the experiment Pathos cannot do: a Rust checker cannot
   be called from a Lean proof with its guarantee intact.

## Measurement

We follow Pathos's `compare-logos` setup so the numbers compare: the
400-proof safe corpus and the 43 large proofs (1 MB or more), the same memory
caps and timeouts, and one process at a time. Rows: Kairos, Kairos with
caching off, Logos, Pathos, Ethos.

| Axis | Metrics |
| --- | --- |
| Speed | correct / incorrect / error / timeout; time on the proofs every checker decided; time on all proofs; peak memory; startup time on a trivial proof |
| Trust | axioms reached by the top theorem (target: Logos's set); trusted tools beyond Lean |
| Proof cost | share of generated functions whose simulation lemma closes automatically; lines of hand-written proof; build time and memory of the proofs |
| Agility | work to move to a new Logos pin: regenerate, re-check, and count the hand edits (target: zero) |
| Telos | time of Telos's oracle-heavy workloads with Logos and with Kairos |

## Non-goals

- Supporting Eunoia signatures other than CPC.
- Beating Pathos on speed.
- Proving SMT semantics or individual rules. That is Logos's job.
- Being a general Eunoia interpreter.
- Upstreaming `kairos_meta_reduce.cpp` into Ethos, for now.

## Milestones

1. **Toolchain.** *(done)* Pin Logos. Build `ethos-eoc` at Logos's Ethos
   commit and `kairos-eoc` with a stub stage that emits a manifest of the
   signature. Check that the pipeline reproduces Logos's `Cpc/`. Regeneration
   and a `--check` mode run in CI.
2. **CpcMini end to end.** *(done, including the composition with Logos's
   `correct___eo_is_refutation` in `soundness/`, which needs Mathlib.)*
   Generate the code for Logos's five-rule CpcMini,
   build the store and cache core, and prove `kairos_refines_logos` for
   CpcMini with generated lemmas. This is the direct counterpart of Pathos's
   pilot, where they proved four programs by hand.
3. **All of CPC, executable.** *(in part: the whole checker is generated,
   with 18 programs still lifted to Logos's own functions. Remaining: the
   parser, the CLI, and the first measurements against Logos and Pathos.)*
   Generate the whole checker, plus the parser and the CLI.
4. **All of CPC, proven.** *(done for the checker: `kairos_refines_logos`
   for all 616 rules, with Lean's standard axioms only.)* Every simulation
   lemma generated and closed, and the top theorem with Logos's axioms only.
5. **Telos oracle.** The library API and the interning boundary for Telos
   nodes, measured on Telos workloads.

## Open questions

- **Lean runtime cost.** How close can threaded, uniquely referenced
  `Array`/`HashMap` state get to the Rust arena? The milestone 2a prototype
  measured intern plus cached recursion ([design.md](design.md)); the
  current checker is not measured yet.
- **Parser.** Write our own, reading straight into the store with a proven
  agreement with Logos's parser, or keep it outside the theorem?
- **Cache across calls.** For Telos, does one long-lived store across many
  oracle calls stay within memory, and what eviction policy keeps refinement
  intact?
