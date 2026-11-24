/-
Interning that sees sharing.

Logos's parser shares the term of a `define` wherever it is used, so a proof's
terms are a DAG in memory, which a plain walk visits as a tree; on real proofs
that tree can be many orders of magnitude larger. `internShared` visits each
shared object once: it remembers the ids of applications by their address.

Addresses are read with Lean's `withPtrAddr`, which asks for a proof that the
result does not depend on the address. It does not, because the result is
determined: it is what `internTerm` gives (`Shared`), along with a memo that is
hidden behind a `Squash`. An entry of the memo holds its term, so the address
cannot be reused, and is used only if its term is the one looked up (`withPtrEq`,
which answers at once for one object).
-/
import Kairos.Runtime.Table

namespace Kairos
open Eo Store

structure AKey where
  addr : USize
  deriving DecidableEq

instance : Hashable AKey :=
  ⟨fun k => ((k.addr.toUInt64 >>> (3 : UInt64)) * (0x9E3779B97F4A7C15 : UInt64)) >>> (12 : UInt64)⟩

/-- Ids of terms, by address. In `σ` and later stores, interning the term of an
entry gives its id and changes nothing. -/
def Memo (σ : Store) : Type :=
  { m : Std.HashMap AKey (Term × Id) // ∀ (k : AKey) (e : Term × Id), m[k]? = some e → Settled (internTerm e.1) σ e.2 }

/-- The result of `m` in `σ`, and a memo for the store it leaves. -/
structure Shared {α : Type} (m : K α) (σ : Store) where
  val : α
  store : Store
  eq : m σ = .ok val store
  memo : Squash (Memo store)

theorem Shared.allEq {α : Type} {m : K α} {σ : Store} (a b : Shared m σ) : a = b := by
  cases a with
  | mk v s e mm =>
    cases b with
    | mk v' s' e' mm' =>
      have h := e.symm.trans e'
      injection h with h1 h2
      subst h1; subst h2
      have : mm = mm' := Subsingleton.elim _ _
      rw [this]

instance {α : Type} {m : K α} {σ : Store} : Subsingleton (Shared m σ) := ⟨Shared.allEq⟩

namespace Shared

theorem stable {α : Type} {m : K α} {σ : Store} (hm : Stable m) (hI : TInv σ) (r : Shared m σ) :
    TInv r.store ∧ Le σ r.store ∧ Settled m r.store r.val := by
  obtain ⟨a, σ', e, h1, h2, h3⟩ := hm σ hI
  have h := e.symm.trans r.eq
  injection h with e1 e2
  subst e1; subst e2
  exact ⟨h1, h2, h3⟩

end Shared

/-- A memo stays good in a later store. -/
@[inline] def Memo.mono {σ σ' : Store} (h : Le σ σ') (m : Memo σ) : Memo σ' :=
  ⟨m.1, fun k e he => (m.2 k e he).mono h⟩

@[inline] def Memo.insert {σ : Store} (m : Memo σ) (u : USize) (t : Term) (i : Id)
    (h : Settled (internTerm t) σ i) : Memo σ :=
  ⟨m.1.insert ⟨u⟩ (t, i), fun k e he => by
    simp only [Std.HashMap.getElem?_insert] at he
    split at he
    · cases he; exact h
    · exact m.2 k e he⟩

/-- Run a stable computation that does not use the memo. -/
@[inline] def Shared.run {m : K Id} (hm : Stable m) (σ : Store) (hI : TInv σ)
    (mm : Squash (Memo σ)) : Shared m σ :=
  match e : m σ with
  | .ok i σ' => ⟨i, σ', e, mm.lift (fun x => Squash.mk (x.mono (by
      obtain ⟨_, _, e', _, hL, _⟩ := hm σ hI
      have h := e'.symm.trans e
      injection h with _ h2
      exact h2 ▸ hL)))⟩
  | .error _ _ => False.elim (by
      obtain ⟨_, _, e', _⟩ := hm σ hI
      rw [e'] at e; cases e)

/-- Sequencing. -/
@[inline] def Shared.bind {α β : Type} {m : K α} {f : α → K β} {σ : Store} (hm : Stable m)
    (hI : TInv σ) (r : Shared m σ)
    (k : (a : α) → (σ' : Store) → TInv σ' → Squash (Memo σ') → Shared (f a) σ') :
    Shared (m >>= f) σ :=
  have h := r.stable hm hI
  match r, h with
  | ⟨a, σ1, e, mm⟩, h =>
    match k a σ1 h.1 mm with
    | ⟨b, σ2, e2, mm2⟩ => ⟨b, σ2, (bind_ok e).trans e2, mm2⟩

theorem internTerm_UOp1 (o : UserOp1) (x : Term) :
    internTerm (.UOp1 o x) = (internTerm x >>= fun a => intern (.UOp1 o a)) := by
  simp only [internTerm]

theorem internTerm_UOp2 (o : UserOp2) (x y : Term) :
    internTerm (.UOp2 o x y) =
      (internTerm x >>= fun a => internTerm y >>= fun b => intern (.UOp2 o a b)) := by
  simp only [internTerm]

theorem internTerm_UOp3 (o : UserOp3) (x y z : Term) :
    internTerm (.UOp3 o x y z) =
      (internTerm x >>= fun a => internTerm y >>= fun b => internTerm z >>= fun c =>
        intern (.UOp3 o a b c)) := by
  simp only [internTerm]

theorem internTerm_apply (f x : Term) :
    internTerm (.Apply f x) =
      (internTerm f >>= fun a => internTerm x >>= fun b => intern (.Apply a b)) := by
  simp only [internTerm]

/-- Look an application up by its address, or run `miss` and remember it. -/
@[inline] def memoized (t : Term) (σ : Store) (hI : TInv σ) (mm : Squash (Memo σ))
    (miss : Unit → Squash (Memo σ) → Shared (internTerm t) σ) : Shared (internTerm t) σ :=
  withPtrAddr t (fun u =>
    mm.lift (fun m =>
      match h : m.1[(⟨u⟩ : AKey)]? with
      | some e =>
        if he : withPtrEq e.1 t (fun _ => decide (e.1 = t)) (fun h => by simp [h]) = true then
          ⟨e.2, σ, by
            have h1 : e.1 = t := of_decide_eq_true he
            have h2 := m.2 _ _ h σ hI (Le.refl σ)
            rwa [h1] at h2, Squash.mk m⟩
        else miss () (Squash.mk m)
      | none =>
        have r := miss () (Squash.mk m)
        have hs := r.stable (internTerm_stable t) hI
        match r, hs with
        | ⟨i, σ', e, mm'⟩, hs =>
          ⟨i, σ', e, mm'.lift (fun m' => Squash.mk (m'.insert u t i hs.2.2))⟩))
    (fun _ _ => Subsingleton.elim _ _)

@[inline] def isApp : Term → Bool
  | .Apply _ _ => true
  | _ => false

/-- `internTerm`, visiting each shared application once. -/
def internShared : (t : Term) → (σ : Store) → TInv σ → Squash (Memo σ) → Shared (internTerm t) σ
  | .Apply f x, σ, hI, mm =>
    -- a partial application, the head of a list cell, is cheap: its operator and
    -- argument are visited, and the argument is remembered if it is worth it
    let visit := fun (_ : Unit) (mm : Squash (Memo σ)) =>
      (internTerm_apply f x ▸
        Shared.bind (internTerm_stable f) hI (internShared f σ hI mm) fun a σ1 hI1 mm1 =>
          Shared.bind (internTerm_stable x) hI1 (internShared x σ1 hI1 mm1) fun b σ2 hI2 mm2 =>
            Shared.run (Stable.intern (.Apply a b)) σ2 hI2 mm2 : Shared (internTerm (.Apply f x)) σ)
    if isApp f then memoized (.Apply f x) σ hI mm visit else visit () mm
  | .UOp1 o x, σ, hI, mm =>
    internTerm_UOp1 o x ▸
      Shared.bind (internTerm_stable x) hI (internShared x σ hI mm) fun a σ1 hI1 mm1 =>
        Shared.run (Stable.intern (.UOp1 o a)) σ1 hI1 mm1
  | .UOp2 o x y, σ, hI, mm =>
    internTerm_UOp2 o x y ▸
      Shared.bind (internTerm_stable x) hI (internShared x σ hI mm) fun a σ1 hI1 mm1 =>
        Shared.bind (internTerm_stable y) hI1 (internShared y σ1 hI1 mm1) fun b σ2 hI2 mm2 =>
          Shared.run (Stable.intern (.UOp2 o a b)) σ2 hI2 mm2
  | .UOp3 o x y z, σ, hI, mm =>
    internTerm_UOp3 o x y z ▸
      Shared.bind (internTerm_stable x) hI (internShared x σ hI mm) fun a σ1 hI1 mm1 =>
        Shared.bind (internTerm_stable y) hI1 (internShared y σ1 hI1 mm1) fun b σ2 hI2 mm2 =>
          Shared.bind (internTerm_stable z) hI2 (internShared z σ2 hI2 mm2) fun c σ3 hI3 mm3 =>
            Shared.run (Stable.intern (.UOp3 o a b c)) σ3 hI3 mm3
  | t, σ, hI, mm => Shared.run (internTerm_stable t) σ hI mm

end Kairos
