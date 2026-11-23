/-
The checker, above the rule dispatch: commands, command lists, assumption
lists, and the end-to-end theorem.
-/
import Kairos.Gen.Dispatch

set_option linter.unusedVariables false

namespace Kairos.Checker
open Eo Kairos Store SmtEval Kairos.Gen


/-! ## Commands -/

/-- The index and formula of the most recent `assume_push` below index `i`. -/
def findPush (a : Array KStateObj) : Nat → Option (Nat × Id)
  | 0 => none
  | i + 1 =>
    match a[i]? with
    | some (.assume_push A) => some (i, A)
    | _ => findPush a i

/-- Pop to the most recent `assume_push`, and push what the step proves. The
state is shrunk in place once the step has read its premises. -/
def k_invoke_cmd_step_pop (fuel : Nat) (s : KState) (r : CRule) (args : KArgList)
    (prems : CIndexList) : K KState :=
  match findPush s.objs s.objs.size with
  | some (i, A) => do
    let t ← k__eo_cmd_step_pop_proven fuel s r args A prems
    k_push_proven fuel t { s with objs := s.objs.shrink i }
  | none => pure .Stuck

/-- `__eo_and (__eo_is_bool_type F) (__eo_is_closed F)`, the guard of an
assumption. -/
def k_assume_guard (fuel : Nat) (F : Id) : K Id := do
  let b ← k__eo_is_bool_type fuel F
  let c ← k__eo_is_closed fuel F
  k__eo_and fuel b c

def k_invoke_cmd (fuel : Nat) (S : KState) (c : KCmd) : K KState :=
  if S.stuck && S.objs.isEmpty then pure .Stuck else
  match c with
  | .assume_push F => do
    let a ← k_assume_guard fuel F
    k_push_check .assume_push a F S
  | .check_proven F => k_invoke_cmd_check_proven fuel S F
  | .step r args prems => do
    let t ← k__eo_cmd_step_proven fuel S r args prems
    k_push_proven fuel t S
  | .step_pop r args prems => k_invoke_cmd_step_pop fuel S r args prems

def k_invoke_cmd_list (fuel : Nat) : KState → KCmdList → K KState
  | S, .nil => pure S
  | S, .cons c cs => do
    let S' ← k_invoke_cmd fuel S c
    k_invoke_cmd_list fuel S' cs

/-! ## Refutations -/
def k_state_is_refutation (fuel : Nat) (s : KState) : K Bool := do
  let f ← intern (.Boolean false)
  let s' ← k_invoke_cmd_check_proven fuel s f
  pure (k_state_is_closed s')

def k_invoke_assume_list (fuel : Nat) (S : KState) : KArgList → K KState
  | .nil => pure S
  | .cons F as => do
    let rest ← k_invoke_assume_list fuel S as
    let a ← k_assume_guard fuel F
    k_push_check .assume a F rest

def k_checker_is_refutation (fuel : Nat) (as : KArgList) (cs : KCmdList) : K Bool := do
  let s ← k_invoke_assume_list fuel .nil as
  let s' ← k_invoke_cmd_list fuel s cs
  k_state_is_refutation fuel s'

end Kairos.Checker
