/- A smoke test: Kairos and Logos on the same CpcMini proofs. -/
import Kairos.Checker.Main

namespace Kairos.Checker.Test
open Eo Kairos Store SmtEval

def run {α : Type} (m : K α) (σ : Store) : Option (α × Store) :=
  match m σ with
  | .ok a σ' => some (a, σ')
  | .error _ _ => none

/-- Assumptions (= a b) and (not (= b a)); symm on the first, then contra. -/
def build (bad : Bool) : K (KArgList × KCmdList) := do
  let bool ← intern .Bool
  let a ← intern (.UConst 0 bool)
  let b ← intern (.UConst 1 bool)
  let eq ← intern (.UOp .eq)
  let not ← intern (.UOp .not)
  let ea ← intern (.Apply eq a)
  let eab ← intern (.Apply ea b)
  let eb ← intern (.Apply eq b)
  let eba ← intern (.Apply eb a)
  let neba ← intern (.Apply not eba)
  let fls ← intern (.Boolean false)
  let concl := if bad then eab else eba
  let as := KArgList.cons eab (.cons neba .nil)
  -- state after assumptions: [eab, neba] (head first); premise index 0 = eab
  let cs := KCmdList.cons (.step .symm .nil (.cons 0 .nil))
    (.cons (.check_proven concl)
    (.cons (.step .contra .nil (.cons 0 (.cons 2 .nil)))
    (.cons (.check_proven fls) .nil)))
  pure (as, cs)

def check (bad : Bool) : String :=
  match run (build bad) Store.init with
  | none => "build failed"
  | some ((as, cs), σ) =>
    let logos := __eo_checker_is_refutation (as.dec σ) (cs.dec σ)
    match run (k_checker_is_refutation (1 <<< 20) as cs) σ with
    | none => s!"kairos: out of fuel; logos: {logos}"
    | some (b, _) => s!"kairos: {b}; logos: {logos}"

#eval check false
#eval check true

end Kairos.Checker.Test
