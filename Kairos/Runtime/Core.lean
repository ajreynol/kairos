/-
The Kairos core: the store, reading ids back as Logos terms, and the store
invariant.

* A term is an `Id` into a hash-consed `Store`: `nodes[i]` is one level of a
  Logos `Term` whose `Term` children are `Id`s smaller than `i`. `Node` is
  generated from Logos's `Term` (Kairos/Gen/Term.lean).
* `decode` reads an `Id` back as Logos's `Term`. It is a specification
  function only; the checker never runs it.
* `Inv` is the store invariant: id 0 is `Stuck`, children precede parents, and
  the interning table is exact (so equal ids ⇔ equal terms).
-/
import Kairos.Gen.Term

namespace Kairos
open Eo

/-- Errors are resource exhaustion only: a Kairos error is never a verdict. -/
inductive Err where
  | fuel
  deriving Repr, Inhabited

structure Store where
  nodes : Array Node
  /-- The interning table, a chained hash table kept in two arrays:
  `heads[k]` is the newest id of bucket `k`, and `next[i]` the next older id in
  the bucket of `i`. 0 ends a chain (`Stuck` is not in the table). -/
  heads : Array Id
  next : Array Id
  /-- Program results, keyed by (program id, argument ids). -/
  cache : Std.HashMap (Nat × List Id) Id

namespace Store

/-- The store with only `Stuck`, at id 0. -/
def init : Store :=
  { nodes := #[.Stuck], heads := Array.replicate 1024 0, next := #[0], cache := ∅ }

def size (σ : Store) : Nat := σ.nodes.size

/-- The node of `i`; `Stuck` for an id that is not in the store. -/
def view (σ : Store) (i : Id) : Node := σ.nodes[i]?.getD .Stuck

/-- Read an id of a node array back as Logos's term. Specification only. -/
def decodeA (nodes : Array Node) (i : Id) : Term :=
  match nodes[i]? with
  | none => .Stuck
  | some n => n.toTerm (fun j => if j < i then decodeA nodes j else .Stuck)
termination_by i
decreasing_by assumption

/-- Read an id back as Logos's term. Specification only. -/
def decode (σ : Store) (i : Id) : Term := decodeA σ.nodes i

end Store

open Store
section decode
end decode
end Kairos
