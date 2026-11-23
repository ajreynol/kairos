/-
Kairos's checker, on Logos's values: the counterpart of Logos's
`__eo_checker_is_refutation`, which the central theorem is stated against.

It interns Logos's argument and command lists into an empty store and runs
the checker. Running out of fuel makes it answer `false`: Kairos may give up,
it may not be wrong.
-/
import Kairos.Checker.Main

namespace Kairos.Checker
open Eo Kairos

def internArgs : CArgList → K KArgList
  | .nil => pure .nil
  | .cons t r => do
    let x ← internTerm t
    let r' ← internArgs r
    pure (.cons x r')

def internCmd : CCmd → K KCmd
  | .assume_push F => do let x ← internTerm F; pure (.assume_push x)
  | .check_proven F => do let x ← internTerm F; pure (.check_proven x)
  | .step r a p => do let a' ← internArgs a; pure (.step r a' p)
  | .step_pop r a p => do let a' ← internArgs a; pure (.step_pop r a' p)

def internCmds : CCmdList → K KCmdList
  | .nil => pure .nil
  | .cons c cs => do
    let c' ← internCmd c
    let cs' ← internCmds cs
    pure (.cons c' cs')

/-- Fuel for the checker: enough for any proof that fits in memory. -/
def defaultFuel : Nat := 2 ^ 62

/-- Intern the assumptions and the commands, then check. -/
def kairos_check (fuel : Nat) (F : CArgList) (C : CCmdList) : K Bool := do
  let as ← internArgs F
  let cs ← internCmds C
  k_checker_is_refutation fuel as cs

/-- Kairos's checker on Logos's values, from an empty store. -/
def kairos_checker_is_refutation (F : CArgList) (C : CCmdList) : Bool :=
  match kairos_check defaultFuel F C Store.init with
  | .ok b _ => b
  | .error _ _ => false

end Kairos.Checker
