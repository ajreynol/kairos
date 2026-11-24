/-
Native versions of Eunoia's list operations and term comparison, which `kairos-eoc` calls in
place of compiling Logos's definitions (`Kairos/Gen/Programs.lean` lists them).
Their proofs are in `verification/KairosVerification/Runtime/Lists.lean`.

The list operations follow Logos's recursion down the list, but works on ids: a cell is
`Apply (Apply f x) y`, its head `f x` is reused rather than interned again, and
a walk that changes nothing answers `none`, so that the caller returns the list
it was given (the same id: equal terms have equal ids). Elements are compared
by id. Each takes a fuel bound and gives up (`.fuel`) when it runs out.
-/
import Kairos.Runtime.Prog
import Kairos.Gen.Intern

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

/-! ## `__eo_is_list`: is it a list of `f`'s? -/
def isListR (isNil : Id → Id → K Id) (f : Id) : Nat → Id → K Id
  | 0, _ => throw .fuel
  | n + 1, l => withStore fun σ =>
    match σ.view l with
    | .Apply gx y =>
      match σ.view gx with
      | .Apply g _ => if g = f then isListR isNil f n y else pure 2
      | _ => isNilB l
    | _ => isNilB l
where isNilB (l : Id) : K Id := do
  if l = 0 then pure 2 else
  let b ← isNil f l
  pure (if b = 1 then 1 else 2)

def isList (isNil : Id → Id → K Id) (n : Nat) (f l : Id) : K Id :=
  if f = 0 ∨ l = 0 then pure 0 else isListR isNil f n l

/-! ## `__eo_list_concat_rec`: append -/
/-- `z` is not `Stuck`. -/
def concatR (z : Id) : Nat → Id → K Id
  | 0, _ => throw .fuel
  | n + 1, l => withStore fun σ =>
    match σ.view l with
    | .Apply fx y =>
      match σ.view fx with
      | .Apply _ _ => do
        let r ← concatR z n y
        if r = 0 then pure 0 else intern (.Apply fx r)
      | _ => pure (if l = 0 then 0 else z)
    | _ => pure (if l = 0 then 0 else z)

def concat (n : Nat) (l z : Id) : K Id :=
  if z = 0 then pure 0 else concatR z n l

/-! ## `__eo_list_rev_rec`: reverse onto an accumulator -/
/-- `acc` is not `Stuck`. -/
def revR : Nat → Id → Id → K Id
  | 0, _, _ => throw .fuel
  | n + 1, l, acc => withStore fun σ =>
    match σ.view l with
    | .Apply fx y =>
      match σ.view fx with
      | .Apply _ _ => do
        let c ← intern (.Apply fx acc)
        revR n y c
      | _ => pure (if l = 0 then 0 else acc)
    | _ => pure (if l = 0 then 0 else acc)

def rev (n : Nat) (l acc : Id) : K Id :=
  if acc = 0 then pure 0 else revR n l acc

/-! ## `__eo_get_elements_rec`: the elements, as an `__eo_List` -/
/-- `k` is `__eo_List_cons` and `e` is `__eo_List_nil`. -/
def elementsR (k e : Id) : Nat → Id → K Id
  | 0, _ => throw .fuel
  | n + 1, l => withStore fun σ =>
    match σ.view l with
    | .Apply fx y =>
      match σ.view fx with
      | .Apply _ x => do
        let r ← elementsR k e n y
        if r = 0 then pure 0
        else do
          let c ← intern (.Apply k x)
          intern (.Apply c r)
      | _ => pure (if l = 0 then 0 else e)
    | _ => pure (if l = 0 then 0 else e)

def elements (n : Nat) (l : Id) : K Id := do
  let k ← intern .__eo_List_cons
  let e ← intern .__eo_List_nil
  elementsR k e n l

/-! ## `__eo_list_len_rec`: the length -/
/-- `none`: the list ends in `Stuck`. `i` is the length so far. -/
def lenR : Nat → Id → Nat → K (Option Nat)
  | 0, _, _ => throw .fuel
  | n + 1, l, i => withStore fun σ =>
    match σ.view l with
    | .Apply fx y =>
      match σ.view fx with
      | .Apply _ _ => lenR n y (i + 1)
      | _ => pure (if l = 0 then none else some i)
    | _ => pure (if l = 0 then none else some i)

def len (n : Nat) (l : Id) : K Id := do
  match ← lenR n l 0 with
  | none => pure 0
  | some i => intern (.Numeral i)

/-! ## `__eo_list_nth_rec`: the element at an index -/
def nthR : Nat → Id → Int → K Id
  | 0, _, _ => throw .fuel
  | n + 1, l, i => withStore fun σ =>
    match σ.view l with
    | .Apply fx y =>
      match σ.view fx with
      | .Apply _ x => if i = 0 then pure x else nthR n y (i - 1)
      | _ => pure 0
    | _ => pure 0

/-- An index that is not a numeral is left to Logos. -/
def nth (n : Nat) (l i : Id) : K Id := withStore fun σ =>
  match σ.view i with
  | .Numeral j => nthR n l j
  | _ => internTerm (__eo_list_nth_rec (σ.decode l) (σ.decode i))

/-! ## `__eo_list_find_rec`: the index of an element -/
/-- `z` is not `Stuck`. The answer is `none` for `Stuck`, and -1 if there is
no `z`. -/
def findR (z : Id) : Nat → Id → Int → K (Option Int)
  | 0, _, _ => throw .fuel
  | n + 1, l, i => withStore fun σ =>
    match σ.view l with
    | .Apply fx y =>
      match σ.view fx with
      | .Apply _ x =>
        if x = 0 then pure none
        else if x = z then pure (some i)
        else findR z n y (i + 1)
      | _ => pure (if l = 0 then none else some (-1))
    | _ => pure (if l = 0 then none else some (-1))

/-- A start that is not a numeral is left to Logos. -/
def findIdx (n : Nat) (l z i : Id) : K Id := withStore fun σ =>
  match σ.view i with
  | .Numeral j =>
    if z = 0 then pure 0 else do
      match ← findR z n l j with
      | none => pure 0
      | some r => intern (.Numeral r)
  | _ => internTerm (__eo_list_find_rec (σ.decode l) (σ.decode z) (σ.decode i))

/-! ## `__eo_list_minclude_rec`: multiset inclusion -/
/-- Are the elements of the `__eo_List` `z` in `y` (not `Stuck`)? -/
def mincludeR : Nat → Id → Id → K Id
  | 0, _, _ => throw .fuel
  | n + 1, y, z => withStore fun σ =>
    match σ.view z with
    | .Apply cx z' =>
      match σ.view cx with
      | .Apply c x =>
        match σ.view c with
        | .__eo_List_cons => do
          let v ← erase n y x
          if v = 0 ∨ z' = 0 then pure 0
          else if v = y then pure 2
          else mincludeR n v z'
        | _ => pure 0
      | _ => pure 0
    | .__eo_List_nil => pure 1
    | _ => pure 0

def minclude (n : Nat) (y z b : Id) : K Id :=
  if y = 0 ∨ z = 0 then pure 0
  else if b = 1 then mincludeR n y z
  else if b = 2 then pure 2
  else pure 0

/-! ## `__eo_list_inter_rec`: multiset intersection -/
def interR : Nat → Id → Id → K (Option Id)
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
            let r? ← interR n y v
            let res := r?.getD y
            if res = 0 then pure (some 0)
            else if v = b then pure (some res)
            else
              match r? with
              | none => pure none
              | some r => do
                let c ← intern (.Apply fx r)
                pure (some c)
      | _ => pure (if l = 0 then some 0 else none)
    | _ => pure (if l = 0 then some 0 else none)

def inter (n : Nat) (l b : Id) : K Id := do
  match ← interR n l b with
  | none => pure l
  | some r => pure r

/-! ## `__eo_list_repeat_rec`: `i` cells of one element -/
/-- `fa` is the cell's head, and `e` the nil. -/
def repeatR (fa e : Id) : Nat → K Id
  | 0 => pure e
  | i + 1 => do
    let r ← repeatR fa e i
    if r = 0 then pure 0 else intern (.Apply fa r)

/-- `typeOf` is `__eo_typeof` and `nilOf` is `__eo_nil`. -/
def rep (typeOf : Id → K Id) (nilOf : Id → Id → K Id) (f a : Id) (i : Nat) : K Id :=
  if f = 0 ∨ a = 0 then pure 0 else do
    let t ← typeOf a
    let e ← nilOf f t
    let fa ← intern (.Apply f a)
    repeatR fa e i

/-! ## Small builtins -/
@[inline] def mkApply (f x : Id) : K Id :=
  if f = 0 ∨ x = 0 then pure 0 else intern (.Apply f x)

@[inline] def eq (a b : Id) : K Id :=
  if a = 0 ∨ b = 0 then pure 0 else pure (if b = a then 1 else 2)

@[inline] def requires (a b c : Id) : K Id :=
  pure (if a = b ∧ a ≠ 0 then c else 0)

@[inline] def isOk (a : Id) : K Id :=
  pure (if a = 0 then 2 else 1)

/-! ## `__eo_cmp`: Logos's order on terms -/
/-- `termCmp` on ids. Equal ids are equal terms, different constructors are
ordered by constructor, and applications by their parts; what remains (a few
leaves) is left to `termCmp` itself. -/
def cmpId (σ : Store) (a b : Id) : Ordering :=
  if a = b then .eq else
  match σ.view a, σ.view b with
  | .Apply f x, .Apply g y =>
    if _h : f < a ∧ x < a then
      match cmpId σ f g with
      | .eq => cmpId σ x y
      | o => o
    else .eq
  | .UConst i x, .UConst j y =>
    if _h : x < a then
      match natCmp i j with
      | .eq => cmpId σ x y
      | o => o
    else .eq
  | .UOp o, .UOp o' => userOpCmp o o'
  | m, n =>
    if m.ctorIdx = n.ctorIdx then termCmp (σ.decode a) (σ.decode b)
    else natCmp m.ctorIdx n.ctorIdx
termination_by a
decreasing_by all_goals first | exact _h.1 | exact _h.2 | exact _h

def cmp (a b : Id) : K Id :=
  if a = 0 ∨ b = 0 then pure 0 else withStore fun σ =>
    let r := cmpId σ a b
    intern (.Boolean (r == .lt))

end Kairos.Native
