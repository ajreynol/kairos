/-
The Kairos monad and its program logic (prototype, milestone 2a).

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
/-- The id of node `n`, adding it if it is new. Its children must be valid. -/
def intern (n : Node) : K Id := fun σ =>
  match σ.table[n]? with
  | some i => .ok i σ
  | none =>
    let i := σ.nodes.size
    .ok i { σ with nodes := σ.nodes.push n, table := σ.table.insert n i }

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
