/-
The checker, below the rule dispatch: Kairos versions of the functions of
lean-meta's checker template that the dispatch uses, and their proofs.

The template is the same for every signature; only the rule dispatch
(`Kairos/Gen/Dispatch.lean`, generated) depends on the rules. None of these
functions needs fuel of its own: each recurses structurally on a checker
list, and calls generated programs, which are proven at every fuel
(`Gen.spec`).
-/
import Kairos.Checker.Types
import Kairos.Gen.Programs

set_option linter.unusedVariables false

namespace Kairos.Checker
open Eo Kairos Store SmtEval Kairos.Gen

/-! ## Proven formulas of a state -/
/-- The `n`th formula from the top, by indexing the array: Logos walks its list. -/
def k_state_proven_nth (s : KState) (n : Int) : K Id :=
  if 0 ≤ n ∧ n.toNat < s.objs.size then
    match s.objs[s.objs.size - 1 - n.toNat]? with
    | some so => pure so.id
    | none => intern (.Boolean true)
  else intern (.Boolean true)

def k_state_is_closed (s : KState) : Bool :=
  !s.stuck && s.objs.all (fun so => !so.isPush)

/-! ## Pushing onto a state -/
/-- `(Boolean true), F, s => cons (mk F) s | _ => Stuck`, the shape of the three
`__eo_push_*_check` functions. -/
@[inline] def k_push_check (mk : Id → KStateObj) (b F : Id) (s : KState) : K KState :=
  withStore fun σ => pure (if σ.view b = .Boolean true then s.push (mk F) else .Stuck)

def k_push_proven (fuel : Nat) (F : Id) (s : KState) : K KState := do
  let b ← k__eo_is_bool_type fuel F
  k_push_check .proven b F s

/-! ## Premise lists -/
def k_mk_premise_list (fuel : Nat) (f : Id) : CIndexList → KState → K Id
  | .nil, _ => do
    let b ← intern .Bool
    k__eo_nil fuel f b
  | .cons n pl, S => do
    let x ← k_state_proven_nth S n
    let r ← k_mk_premise_list fuel f pl S
    k__eo_cons fuel f x r

/-! ## Checking what a step proves -/
def k_invoke_cmd_check_proven (fuel : Nat) (s : KState) (p : Id) : K KState :=
  match s.objs.back? with
  | some (.proven F) => do
    let e ← k__eo_eq fuel F p
    k_push_check .proven e F { s with objs := s.objs.pop }
  | _ => pure .Stuck

end Kairos.Checker
