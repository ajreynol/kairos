/-
Micro-benchmark of the prototype against Logos's CpcMini (milestone 2a).

* `trans N`: `__mk_trans` over a chain of N equalities. No sharing, so this
  measures Kairos's constant-factor overhead (interning, cache, store
  threading) against Logos's structural terms.
* `closed D`: `__eo_is_closed` on a DAG of depth D: `t_{k+1} = (and t_k t_k)`.
  Its tree has 2^D leaves but only D+1 distinct subterms.
-/
import Kairos.Proto.Mini

namespace Kairos.Bench
open Eo Kairos Store SmtEval

/-! `__eo_is_closed_rec`, hand-compiled (unverified; for the benchmark). -/

def k_and (a b : Id) : K Id := withStore fun σ =>
  match σ.view a, σ.view b with
  | .Boolean x, .Boolean y => intern (.Boolean (x && y))
  | _, _ => pure 0

def k_is_closed_rec : Nat → Id → Id → K Id
  | 0, _, _ => throw .fuel
  | n + 1, x, env => cached 1 [x, env] <| withStore fun σ =>
    if x = 0 ∨ env = 0 then pure 0 else
    match σ.view x, σ.view env with
    | .Var _ _, .__eo_List_nil => intern (.Boolean false)
    | .Var _ _, .Apply g vs =>
      match σ.view g with
      | .Apply c y =>
        if σ.view c = .__eo_List_cons then
          if x = y then intern (.Boolean true) else k_is_closed_rec n x vs
        else pure 1 -- unreachable for well-formed environments
      | _ => intern (.Boolean true)
    | .Apply f y, _ => do
      let a ← k_is_closed_rec n f env
      let b ← k_is_closed_rec n y env
      k_and a b
    | _, _ => intern (.Boolean true)

def k_is_closed (fuel : Nat) (x : Id) : K Id := do
  if x = 0 then return 0
  let nil ← intern .__eo_List_nil
  k_is_closed_rec fuel x nil

/-! Workloads -/

def logosConst (i : Nat) : Term := .UConst i .Bool
def kConst (i : Nat) : K Id := do let b ← intern .Bool; intern (.UConst i b)

/-- `(and (= a_i a_{i+1}) (and ... true))` for i from k to n-1. -/
def logosChain (n : Nat) : Term := Id.run do
  let mut acc := Term.Boolean true
  for j in [0:n] do
    let i := n - 1 - j
    acc := .Apply (.Apply (.UOp .and) (.Apply (.Apply (.UOp .eq) (logosConst i)) (logosConst (i+1)))) acc
  return acc

def kChain (n : Nat) : K Id := do
  let mut acc ← intern (.Boolean true)
  for j in [0:n] do
    let i := n - 1 - j
    let a ← kConst i
    let b ← kConst (i+1)
    let e ← mkBin .eq a b
    acc ← mkBin .and e acc
  return acc

def logosDag (d : Nat) : Term := Id.run do
  let mut t := logosConst 0
  for _ in [0:d] do
    t := .Apply (.Apply (.UOp .and) t) t
  return t

def kDag (d : Nat) : K Id := do
  let mut t ← kConst 0
  for _ in [0:d] do
    t ← mkBin .and t t
  return t

def fuel : Nat := 1 <<< 40

def run (σ : Store) (m : K Id) : Id × Store :=
  match m σ with
  | .ok r σ' => (r, σ')
  | .error _ σ' => (0, σ')

def time {α : Type} (label : String) (f : Unit → IO α) : IO α := do
  let t0 ← IO.monoNanosNow
  let a ← f ()
  let t1 ← IO.monoNanosNow
  IO.println s!"  {label}: {(t1 - t0).toFloat / 1e6} ms"
  return a

def benchTrans (n : Nat) : IO Unit := do
  IO.println s!"trans {n}"
  let t ← time "logos build" fun _ => pure (logosChain n)
  let r ← time "logos __mk_trans" fun _ => match t with
    | .Apply (.Apply _ (.Apply (.Apply _ t1) t2)) tail => pure (__mk_trans t1 t2 tail)
    | _ => pure .Stuck
  IO.println s!"    logos result is (= a0 a{n}): {decide (r = .Apply (.Apply (.UOp .eq) (logosConst 0)) (logosConst n))}"
  let (x, σ) ← time "kairos build" fun _ => pure (run .init (kChain n))
  let (r, σ) ← time "kairos k_mk_trans" fun _ => pure (run σ (do
    match matchTransCons σ x with
    | some (t1, t2, tail) => k_mk_trans fuel t1 t2 tail
    | none => pure 0))
  IO.println s!"    kairos result decodes to Logos's: {decide (σ.decode r = .Apply (.Apply (.UOp .eq) (logosConst 0)) (logosConst n))}, store {σ.size} nodes"

def benchClosed (d : Nat) : IO Unit := do
  IO.println s!"closed {d}"
  let (x, σ) ← time "kairos build" fun _ => pure (run .init (kDag d))
  let (r, σ) ← time "kairos k_is_closed" fun _ => pure (run σ (k_is_closed fuel x))
  IO.println s!"    kairos result is true: {decide (σ.view r = .Boolean true)}, store {σ.size} nodes"
  if d ≤ 26 then
    let t := logosDag d
    let r ← time "logos __eo_is_closed" fun _ => pure (__eo_is_closed t)
    IO.println s!"    logos result: {decide (r = .Boolean true)}"
  else
    IO.println s!"  logos __eo_is_closed: skipped (2^{d} leaves)"

end Kairos.Bench

open Kairos.Bench in
def main (args : List String) : IO Unit := do
  match args with
  | ["trans", n] => benchTrans n.toNat!
  | ["closed", d] => benchClosed d.toNat!
  | _ => IO.println "usage: kairos-proto-bench (trans N | closed D)"
