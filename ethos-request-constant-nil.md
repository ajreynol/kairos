# lean-meta: don't compute the type of the first argument when an operator's nil terminator is constant

## Problem

The generated parser computes the nil terminator of an n-ary operator from the
type of its first argument:

```lean
private def parserNil (op : Term) : Option Term → Term
  | some seed => __eo_nil op (__eo_typeof seed)
  | none => __eo_nil op Term.Type
```

`__eo_typeof` is an uncached walk over the whole argument, and it runs each time
such an application is built. For many operators the result is then ignored: the
nil of `or` is `false` whatever the type. The wasted walk is exponential when
terms are shared, because the parser shares the term of a `define` in memory but
the walk visits it as a tree:

```smt2
(declare-const p Bool)
(define @t0 () (and p p))
(define @t1 () (and @t0 @t0))
(define @t2 () (and @t1 @t1))
; ...
```

At 20 levels this takes about 60 ms to parse, and grows by 4x for every two more
levels. With `=>` in place of `and`, the same file parses in 0.35 ms.

## Effect on real proofs

CPC proofs of cvc5 regressions (cvc5 1.4.3.dev), parse time only, with and
without the change. Timings are from a busy machine, so they are rough.

| Regression | Now | Constant nils |
| --- | --- | --- |
| `regress0/bv/overflow/sdivo1` | > 20 s | 7 ms |
| `regress0/bv/fuzz15.delta01` | > 20 s | 16 ms |
| `regress1/bvdiv2` | > 20 s | 20 ms |
| `regress0/bv/holes/srem-eliminate-fewer-bitwise-ops` | > 20 s | 32 ms |
| `regress3/quantifiers/ForElimination-scala-9` | 9.2 s | 775 ms |
| `regress1/auflia/bug330` | 7.7 s | 26 ms |
| `regress0/bv/abstract/cross-term-div-mul-rem` | 2.4 s | 520 ms |
| `regress1/bv/incorrect1` | 1.4 s | 12 ms |
| `regress1/bv/proj-issue438-prerewrite-fixed-point-original` | 1.1 s | 119 ms |

Over the 721 proofs (of 906) that finish either way, total parse time falls from
4.1 s to 2.6 s. The verdict of the checker used for the test (Kairos) is
unchanged on all of them.

This was measured by overriding the nils in `parserConfig.ops`, not by changing
the generator.

## Request

When the nil terminator of an operator is a ground term, print it directly
instead of going through `parserNil`:

```lean
arity := .rightAssocNil (fun _ => Term.Boolean false)
```

In CPC this covers `or`, `and`, `concat`, `@from_bools`, `re.++`, `re.inter`,
`re.union`, `Tuple`, `tuple` and `@@poly`. It also covers the `and` that
chainable operators (`=`, `<`, `<=`, ...) build.

`LeanMetaReduce::printParserOp` (`plugins/lean_meta/lean_meta_reduce.cpp`) builds
these strings in three places: the `*-assoc-nil` attributes, `arg-list`, and
`chainable`/`pairwise`. A helper that takes the operator and returns either the
constant function or `parserNil <op>` would serve all three. A guess at the size
is 20-40 lines.

## One behavior change

Today an ill-typed first argument has type `Stuck`, and `__eo_nil _ Stuck` is
`Stuck`, so the list ends in `Stuck`. With this change the list is well formed
and only its ill-typed element is at fault. Such a term should still have no
type, so anything that asks for its type should reject it as before. If keeping
the exact term matters, this needs a closer look before it goes in.

## Out of scope

`+`, `*`, `bvand`, `bvor`, `bvxor`, `bvadd`, `bvmul`, `str.++` and
`@@TypedList.cons` have a nil that depends on the type, so they would keep the
walk. `regress1/strings/ss-combine-large-substr` still takes 0.4 s to parse
either way, and `regress1/proofs/base-lfsc-treesize` still does not finish
within 20 s. A later step could be to cache the type of each bound name.
