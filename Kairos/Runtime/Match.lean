/-
Pattern-matching primitives and their lemmas.

A generated matcher is a chain of primitives in continuation-passing style:
`leaf` and `stuck` here, and one per constructor of `Term`, generated
(Kairos/Gen/Prims.lean). Generated proofs take a chain apart one
step at a time with the `_some` lemmas, run it on a known shape with the
`_of_view` lemmas, and invert a decoded shape with the `_inv` lemmas. Under the invariant, none of these needs the id to be
valid: an id outside the store reads as `Stuck` and views as `stuck`.
-/
import Kairos.Runtime.Monad

namespace Kairos
open Eo Store


namespace Store

/-! Matcher steps, in continuation-passing style: each takes an id apart and
hands its parts to the rest of the matcher. They inline to nested matches. -/

@[inline] def leaf {α : Type} (σ : Store) (x : Id) (n : Node) (k : Option α) : Option α :=
  match n with
  | .UOp o => match σ.view x with
    | .UOp o' => if o' = o then k else none
    | _ => none
  | .Boolean b => match σ.view x with
    | .Boolean b' => if b' = b then k else none
    | _ => none
  | n => if σ.view x = n then k else none

/-- A native field a pattern fixes, e.g. the operator of an indexed operator. -/
@[inline] def _root_.Kairos.kguard {α : Type} (c : Prop) [Decidable c] (k : Option α) : Option α :=
  if c then k else none

/-- The `Stuck` pattern, which is id 0. -/
@[inline] def stuck {α : Type} (x : Id) (k : Option α) : Option α :=
  if x = 0 then k else none

end Store
end Kairos
