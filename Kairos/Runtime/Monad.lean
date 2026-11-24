/-
The Kairos monad and its program logic.

* `K` threads the store; it can fail only by running out of a resource.
* `Ok m σ Q`: if `m` returns from `σ`, then `Q` holds of its result. Errors
  satisfy everything: this is the refinement reading (Kairos may give up, it
  may not be wrong).
* `Post sem σ t r σ'`: the standard postcondition of a term-producing
  computation started in `σ`: the invariant holds in `σ'`, `σ'` extends `σ`,
  and `r` is a valid id that reads as the Logos term `t`.
-/
import Kairos.Runtime.Core

namespace Kairos
open Eo Store

abbrev K := EStateM Err Store

/-! ## Interning -/
/-! The table's hash. Nothing is proven of it: it only has to be a function. -/
@[inline] def mixApply (a b : Id) : UInt64 :=
  let h := (a.toUInt64 * 0x9E3779B97F4A7C15) ^^^ (b.toUInt64 * 0xC2B2AE3D27D4EB4F)
  h ^^^ (h >>> 29)

@[inline] def mixOp (o : UserOp) : UInt64 :=
  (UInt64.ofNat o.ctorIdx * (0x9E3779B97F4A7C15 : UInt64)) >>> (20 : UInt64)

@[inline] def nhash (n : Node) : UInt64 :=
  match n with
  | .Apply a b => mixApply a b
  | .UOp o => mixOp o
  | n => hash n

/-- The bucket of a hash, of `sz` (a power of two, though only `0 < sz`
matters for correctness). -/
@[inline] def bucket (h : UInt64) (sz : Nat) : Nat :=
  let k := (h &&& (sz.toUInt64 - 1)).toNat
  if k < sz then k else 0

/-- The first id of the chain from `i` whose node satisfies `p`, or 0. Chains go
to smaller ids; the test makes that plain to Lean. -/
@[specialize] def find (p : Node → Bool) (nodes : Array Node) (next : Array Id) (i : Id) : Id :=
  if i = 0 then 0
  else if p nodes[i]! then i
  else
    let j := next[i]!
    if j < i then find p nodes next j else 0
termination_by i

@[inline] def isApply (a b : Id) (m : Node) : Bool :=
  match m with
  | .Apply a' b' => decide (a' = a) && decide (b' = b)
  | _ => false

@[inline] def isUOp (o : UserOp) (m : Node) : Bool :=
  match m with
  | .UOp o' => decide (o' = o)
  | _ => false

def findApply (nodes : @& Array Node) (next : @& Array Id) (a b : @& Id) (i : Id) : Id :=
  find (isApply a b) nodes next i

def findUOp (nodes : @& Array Node) (next : @& Array Id) (o : UserOp) (i : Id) : Id :=
  find (isUOp o) nodes next i

def findNode (nodes : @& Array Node) (next : @& Array Id) (n : @& Node) (i : Id) : Id :=
  find (fun m => decide (m = n)) nodes next i

/-- Link the ids from `i` on into `heads`. -/
def rehash (nodes : @& Array Node) (i : Nat) (heads next : Array Id) : Array Id × Array Id :=
  if i < nodes.size then
    let k := bucket (nhash nodes[i]!) heads.size
    let o := heads[k]!
    rehash nodes (i + 1) (heads.set! k i) (next.set! i o)
  else (heads, next)
termination_by nodes.size - i

/-- Use four times as many buckets. -/
@[noinline] def grow (σ : Store) : Store :=
  let ⟨nodes, heads, next, cache⟩ := σ
  let (heads, next) := rehash nodes 1 (Array.replicate (heads.size * 4) 0) next
  ⟨nodes, heads, next, cache⟩

/-- Add `n`, which is new, to bucket `k`. Taking the store apart lets its
arrays be updated in place. -/
@[inline] def addNode (n : Node) (k : Nat) (σ : Store) : EStateM.Result Err Store Id :=
  let ⟨nodes, heads, next, cache⟩ := σ
  let i := nodes.size
  let o := heads[k]!
  let σ : Store := ⟨nodes.push n, heads.set! k i, next.push o, cache⟩
  .ok i (if i ≥ σ.heads.size then grow σ else σ)

def internNode (n : Node) : K Id := fun σ =>
  match n with
  | .Stuck => .ok 0 σ
  | _ =>
    let k := bucket (nhash n) σ.heads.size
    let i := findNode σ.nodes σ.next n σ.heads[k]!
    if i = 0 then addNode n k σ else .ok i σ

/-- `internNode (.Apply a b)`, building the node only if it is new. -/
def internApply (a b : Id) : K Id := fun σ =>
  let k := bucket (mixApply a b) σ.heads.size
  let i := findApply σ.nodes σ.next a b σ.heads[k]!
  if i = 0 then addNode (.Apply a b) k σ else .ok i σ

def internUOp (o : UserOp) : K Id := fun σ =>
  let k := bucket (mixOp o) σ.heads.size
  let i := findUOp σ.nodes σ.next o σ.heads[k]!
  if i = 0 then addNode (.UOp o) k σ else .ok i σ

/-- The id of node `n`, adding it if it is new. Its children must be valid. -/
@[inline] def intern (n : Node) : K Id :=
  match n with
  | .Apply a b => internApply a b
  | .UOp o => internUOp o
  | n => internNode n

/-! ## The result cache -/
/-- Run `body` for program `p` on `args`, unless the result is cached. -/
def cached (p : Nat) (args : List Id) (body : K Id) : K Id := fun σ =>
  match σ.cache[(p, args)]? with
  | some r => .ok r σ
  | none =>
    match body σ with
    | .ok r σ' => .ok r { σ' with cache := σ'.cache.insert (p, args) r }
    | .error e σ' => .error e σ'

end Kairos
