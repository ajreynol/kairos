/-
Native versions of Eunoia's list operations, which `kairos-eoc` calls in
place of compiling Logos's definitions (`Kairos/Gen/Programs.lean` lists them).
Their proofs are in `verification/KairosVerification/Runtime/Lists.lean`.

Each follows Logos's recursion down the list, but works on ids: a cell is
`Apply (Apply f x) y`, its head `f x` is reused rather than interned again, and
a walk that changes nothing answers `none`, so that the caller returns the list
it was given (the same id: equal terms have equal ids). Elements are compared
by id. Each takes a fuel bound and gives up (`.fuel`) when it runs out.
-/
import Kairos.Runtime.Prog

namespace Kairos.Native
open Eo Kairos Store

/-! ## `__eo_list_erase_rec`: erase the first `z` -/
/-- `none`: `z` is not in `l`, which is the result. `z` is not `Stuck`. -/
def eraseR (z : Id) : Nat → Id → K (Option Id)
  | 0, _ => throw .fuel
  | n + 1, l => withStore fun σ =>
    match σ.view l with
    | .Apply fx y =>
      match σ.view fx with
      | .Apply _ x =>
        if x = 0 then pure (some 0)
        else if x = z then pure (some y)
        else do
          match ← eraseR z n y with
          | none => pure none
          | some r =>
            if r = 0 then pure (some 0)
            else do
              let c ← intern (.Apply fx r)
              pure (some c)
      | _ => pure (if l = 0 then some 0 else none)
    | _ => pure (if l = 0 then some 0 else none)

def erase (n : Nat) (l z : Id) : K Id :=
  if l = 0 ∨ z = 0 then pure 0 else do
    match ← eraseR z n l with
    | none => pure l
    | some r => pure r

/-! ## `__eo_list_erase_all_rec`: erase every `z` -/
def eraseAllR (z : Id) : Nat → Id → K (Option Id)
  | 0, _ => throw .fuel
  | n + 1, l => withStore fun σ =>
    match σ.view l with
    | .Apply fx y =>
      match σ.view fx with
      | .Apply f x =>
        if f = 0 ∨ x = 0 then pure (some 0)
        else do
          let r? ← eraseAllR z n y
          let res := r?.getD y
          if res = 0 then pure (some 0)
          else if x = z then pure (some res)
          else
            match r? with
            | none => pure none
            | some r => do
              let c ← intern (.Apply fx r)
              pure (some c)
      | _ => pure (if l = 0 then some 0 else none)
    | _ => pure (if l = 0 then some 0 else none)

def eraseAll (n : Nat) (l z : Id) : K Id :=
  if l = 0 ∨ z = 0 then pure 0 else do
    match ← eraseAllR z n l with
    | none => pure l
    | some r => pure r

/-! ## `__eo_list_setof_rec`: the first occurrence of each element -/
def setofR : Nat → Id → K (Option Id)
  | 0, _ => throw .fuel
  | n + 1, l => withStore fun σ =>
    match σ.view l with
    | .Apply fx y =>
      match σ.view fx with
      | .Apply _ x => do
        let s? ← setofR n y
        let e ← eraseAll n (s?.getD y) x
        if e = 0 then pure (some 0)
        else if e = y then pure none
        else do
          let c ← intern (.Apply fx e)
          pure (some c)
      | _ => pure (if l = 0 then some 0 else none)
    | _ => pure (if l = 0 then some 0 else none)

def setof (n : Nat) (l : Id) : K Id := do
  match ← setofR n l with
  | none => pure l
  | some r => pure r

/-! ## `__eo_list_diff_rec`: multiset difference -/
def diffR : Nat → Id → Id → K (Option Id)
  | 0, _, _ => throw .fuel
  | n + 1, l, b => withStore fun σ =>
    if b = 0 then pure (some 0) else
    match σ.view l with
    | .Apply fx y =>
      match σ.view fx with
      | .Apply f x =>
        if f = 0 ∨ x = 0 then pure (some 0)
        else do
          let v ← erase n b x
          if v = 0 then pure (some 0)
          else do
            let r? ← diffR n y v
            let res := r?.getD y
            if res = 0 then pure (some 0)
            else if v = b then
              match r? with
              | none => pure none
              | some r => do
                let c ← intern (.Apply fx r)
                pure (some c)
            else pure (some res)
      | _ => pure (if l = 0 then some 0 else none)
    | _ => pure (if l = 0 then some 0 else none)

def diff (n : Nat) (l b : Id) : K Id := do
  match ← diffR n l b with
  | none => pure l
  | some r => pure r

/-! ## `__eo_get_nil_rec`: the nil of a list whose cells all have head `f` -/
/-- `isNil` is `__eo_is_list_nil`. -/
def getNilR (isNil : Id → Id → K Id) (f : Id) : Nat → Id → K Id
  | 0, _ => throw .fuel
  | n + 1, l => withStore fun σ =>
    if l = 0 then pure 0 else
    let atNil : K Id := do
      let b ← isNil f l
      withStore fun σ => pure (if σ.view b = .Boolean true then l else 0)
    match σ.view l with
    | .Apply gx y =>
      match σ.view gx with
      | .Apply g _ => if g = f then getNilR isNil f n y else pure 0
      | _ => atNil
    | _ => atNil

def getNil (isNil : Id → Id → K Id) (n : Nat) (f l : Id) : K Id :=
  if f = 0 then pure 0 else getNilR isNil f n l

end Kairos.Native
