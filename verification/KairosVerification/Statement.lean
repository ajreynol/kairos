/-
Kairos adds nothing to what must be trusted: its central statement depends
only on Logos's definitions, Kairos's checker code, and Lean.

`#check_statement_base thm` walks every constant `thm`'s statement depends on
(its type, then the types and values of the definitions it reaches, and the
constructors of the inductives, transitively) and fails if any is defined in a
module of this project. So the store invariant, the decodings, the program
logic and the generated specs are all proof devices: reading the theorem needs
none of them. (Proofs are not walked: what a theorem's proof uses is checked
by Lean, not trusted.)
-/
import KairosVerification.Checker.Api
import Lean

open Lean Elab Command

elab "#check_statement_base " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  let some ci := env.find? n | throwError "unknown constant {n}"
  let mut todo : Array Name := ci.type.getUsedConstants
  let mut seen : NameSet := {}
  let mut bad : Array (Name × Name) := #[]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some idx := env.getModuleIdxFor? c then
      let m := env.header.moduleNames[idx.toNat]!
      if (`KairosVerification).isPrefixOf m then
        bad := bad.push (c, m)
    match env.find? c with
    | some (.defnInfo d) => todo := todo ++ d.type.getUsedConstants ++ d.value.getUsedConstants
    | some (.inductInfo d) => todo := todo ++ d.type.getUsedConstants ++ d.ctors.toArray
    | some info => todo := todo ++ info.type.getUsedConstants
    | none => pure ()
  unless bad.isEmpty do
    throwError m!"the statement of {n} depends on this project's definitions: " ++
      m!"{bad.toList.take 20}"
  logInfo m!"{n}: its statement depends on {seen.size} constants, none of this project"

#check_statement_base Kairos.Checker.kairos_refines_logos
