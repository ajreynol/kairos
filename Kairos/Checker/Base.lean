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
def k_state_proven_nth : KState → Int → K Id
  | .cons so s, n => if n = 0 then pure so.id else k_state_proven_nth s (native_zplus n (native_zneg 1))
  | _, _ => intern (.Boolean true)

def k_state_is_closed : KState → Bool
  | .cons (.assume_push _) _ => false
  | .cons _ s => k_state_is_closed s
  | .nil => true
  | .Stuck => false

/-! ## Pushing onto a state -/
/-- `(Boolean true), F, s => cons (mk F) s | _ => Stuck`, the shape of the three
`__eo_push_*_check` functions. -/
@[inline] def k_push_check (mk : Id → KStateObj) (b F : Id) (s : KState) : K KState :=
  withStore fun σ => pure (if σ.view b = .Boolean true then .cons (mk F) s else .Stuck)

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
def k_invoke_cmd_check_proven (fuel : Nat) : KState → Id → K KState
  | .cons (.proven F) S, p => do
    let e ← k__eo_eq fuel F p
    k_push_check .proven e F S
  | _, _ => pure .Stuck

end Kairos.Checker
