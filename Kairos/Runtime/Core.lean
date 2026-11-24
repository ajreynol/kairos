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

/-- A key of the result cache: a program and its arguments, flat for few
arguments. -/
inductive CKey where
  | k1 (p a : Nat)
  | k2 (p a b : Nat)
  | k3 (p a b c : Nat)
  | kn (p : Nat) (args : List Id)
  deriving DecidableEq

/-- Nothing is proven of the hash. -/
@[inline] def mix64 (h : UInt64) (a : Nat) : UInt64 :=
  let h := (h ^^^ a.toUInt64) * 0x9E3779B97F4A7C15
  h ^^^ (h >>> 32)

def CKey.hash : CKey → UInt64
  | .k1 p a => mix64 p.toUInt64 a
  | .k2 p a b => mix64 (mix64 p.toUInt64 a) b
  | .k3 p a b c => mix64 (mix64 (mix64 p.toUInt64 a) b) c
  | .kn p l => l.foldl mix64 p.toUInt64

instance : Hashable CKey := ⟨CKey.hash⟩

/-- The key of a program and its arguments; different ones differ. -/
@[inline] def ckey (p : Nat) (args : List Id) : CKey :=
  match args with
  | [a] => .k1 p a
  | [a, b] => .k2 p a b
  | [a, b, c] => .k3 p a b c
  | l => .kn p l

structure Store where
  nodes : Array Node
  /-- The interning table, a chained hash table kept in two arrays:
  `heads[k]` is the newest id of bucket `k`, and `next[i]` the next older id in
  the bucket of `i`. 0 ends a chain; ids 0 to 2 are not in the table (`init`). -/
  heads : Array Id
  next : Array Id
  /-- Program results, by `ckey` of the program id and argument ids. -/
  cache : Std.HashMap CKey Id

namespace Store

/-- The first store: `Stuck` at id 0, `true` at 1 and `false` at 2. These are not
in the table; interning one answers its id at once. -/
def init : Store :=
  { nodes := #[.Stuck, .Boolean true, .Boolean false], heads := Array.replicate 1024 0, next := #[0, 0, 0], cache := ∅ }

def size (σ : Store) : Nat := σ.nodes.size

/-- The node of `i`; `Stuck` for an id that is not in the store. -/
@[inline] def view (σ : Store) (i : Id) : Node := σ.nodes[i]?.getD .Stuck

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
