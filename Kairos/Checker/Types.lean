/-
The checker's datatypes in Kairos: Logos's CArgList, CStateObj, CState, CCmd
and CCmdList with term ids in place of terms. They are fixed by lean-meta's
checker template, as Logos's are; CRule and CIndexList hold no terms and are
used as they are.
-/
import Kairos.Gen.Intern

namespace Kairos
open Eo Store


inductive KArgList where
  | nil
  | cons (a : Id) (rest : KArgList)

inductive KStateObj where
  | assume (F : Id)
  | assume_push (F : Id)
  | proven (F : Id)

inductive KState where
  | nil
  | cons (so : KStateObj) (s : KState)
  | Stuck

inductive KCmd where
  | assume_push (F : Id)
  | check_proven (F : Id)
  | step (r : CRule) (args : KArgList) (prems : CIndexList)
  | step_pop (r : CRule) (args : KArgList) (prems : CIndexList)

inductive KCmdList where
  | nil
  | cons (c : KCmd) (cs : KCmdList)

def KStateObj.id : KStateObj → Id
  | .assume F => F
  | .assume_push F => F
  | .proven F => F

end Kairos
