/-
What generated programs are built from, beyond interning and matching: reading
the store, Logos's builtin `__eo_ite` and `native_ite` (lazy in Kairos),
natives over terms, and the call-site lemmas.
-/
import Kairos.Gen.Prims

namespace Kairos
open Eo Store SmtEval


/-- Run `f` on the current store, without changing it. -/
@[inline] def withStore {α : Type} (f : Store → K α) : K α := fun σ => f σ σ

/-! ## Trying a case

A program tries its cases in order: `kcase (m σ args) rhs rest` runs `rhs`
on what the matcher bound, or `rest`. Proofs split it with `kcase_sim`, which
only sees the case at hand, however many cases follow. -/
@[inline] def kcase {α β : Type} (o : Option α) (f : α → K β) (g : K β) : K β :=
  match o with
  | some v => f v
  | none => g

/-! ## Natives over terms -/
/-- `native_teq` on ids: equal ids are equal terms. -/
@[inline] def knative_teq (a b : Id) : Bool := decide (a = b)

/-- Logos's `__eo_ite` on the id `c`, evaluating only the branch taken. -/
@[inline] def k_ite (c : Id) (mt me : K Id) : K Id := 
  if c = 1 then mt else if c = 2 then me else pure 0

end Kairos
