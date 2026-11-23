/-
The checker's datatypes in Kairos: Logos's CArgList, CStateObj, CState, CCmd
and CCmdList with term ids in place of terms. They are fixed by lean-meta's
checker template, as Logos's are; CRule and CIndexList hold no terms and are
used as they are.
-/
import Kairos.Checker.Types
import KairosVerification.Runtime.Val

namespace Kairos
open Eo Store

variable {σ σ' : Store}
/-! ## Reading them as Logos values -/
def KArgList.dec (σ : Store) : KArgList → CArgList
  | .nil => .nil
  | .cons a r => .cons (σ.decode a) (r.dec σ)

def KArgList.valid (σ : Store) : KArgList → Prop
  | .nil => True
  | .cons a r => a < σ.size ∧ r.valid σ

def KStateObj.dec (σ : Store) : KStateObj → CStateObj
  | .assume F => .assume (σ.decode F)
  | .assume_push F => .assume_push (σ.decode F)
  | .proven F => .proven (σ.decode F)

def KStateObj.valid (σ : Store) (so : KStateObj) : Prop := so.id < σ.size

def KState.dec (σ : Store) : KState → CState
  | .nil => .nil
  | .cons so s => .cons (so.dec σ) (s.dec σ)
  | .Stuck => .Stuck

def KState.valid (σ : Store) : KState → Prop
  | .nil => True
  | .cons so s => so.valid σ ∧ s.valid σ
  | .Stuck => True

def KCmd.dec (σ : Store) : KCmd → CCmd
  | .assume_push F => .assume_push (σ.decode F)
  | .check_proven F => .check_proven (σ.decode F)
  | .step r a p => .step r (a.dec σ) p
  | .step_pop r a p => .step_pop r (a.dec σ) p

def KCmd.valid (σ : Store) : KCmd → Prop
  | .assume_push F => F < σ.size
  | .check_proven F => F < σ.size
  | .step _ a _ => a.valid σ
  | .step_pop _ a _ => a.valid σ

def KCmdList.dec (σ : Store) : KCmdList → CCmdList
  | .nil => .nil
  | .cons c cs => .cons (c.dec σ) (cs.dec σ)

def KCmdList.valid (σ : Store) : KCmdList → Prop
  | .nil => True
  | .cons c cs => c.valid σ ∧ cs.valid σ

/-! ## Stability under store growth -/
theorem KArgList.mono (hE : Extends σ σ') :
    ∀ a : KArgList, a.valid σ → a.valid σ' ∧ a.dec σ' = a.dec σ
  | .nil, _ => ⟨trivial, rfl⟩
  | .cons x r, ⟨hx, hr⟩ =>
    have ih := KArgList.mono hE r hr
    ⟨⟨Nat.lt_of_lt_of_le hx hE.size_le, ih.1⟩, by
      simp [KArgList.dec, decode_extends hE x hx, ih.2]⟩

theorem KStateObj.mono (hE : Extends σ σ') (so : KStateObj) (h : so.valid σ) :
    so.valid σ' ∧ so.dec σ' = so.dec σ := by
  refine ⟨Nat.lt_of_lt_of_le h hE.size_le, ?_⟩
  cases so <;> simp only [KStateObj.valid, KStateObj.id] at h <;>
    simp [KStateObj.dec, decode_extends hE _ h]

theorem KState.mono (hE : Extends σ σ') :
    ∀ s : KState, s.valid σ → s.valid σ' ∧ s.dec σ' = s.dec σ
  | .nil, _ => ⟨trivial, rfl⟩
  | .Stuck, _ => ⟨trivial, rfl⟩
  | .cons so s, ⟨hso, hs⟩ =>
    have h1 := KStateObj.mono hE so hso
    have ih := KState.mono hE s hs
    ⟨⟨h1.1, ih.1⟩, by simp [KState.dec, h1.2, ih.2]⟩

theorem KCmd.mono (hE : Extends σ σ') (c : KCmd) (h : c.valid σ) :
    c.valid σ' ∧ c.dec σ' = c.dec σ := by
  cases c with
  | assume_push F => exact ⟨Nat.lt_of_lt_of_le h hE.size_le, by simp [KCmd.dec, decode_extends hE F h]⟩
  | check_proven F => exact ⟨Nat.lt_of_lt_of_le h hE.size_le, by simp [KCmd.dec, decode_extends hE F h]⟩
  | step r a p => exact ⟨(KArgList.mono hE a h).1, by simp [KCmd.dec, (KArgList.mono hE a h).2]⟩
  | step_pop r a p => exact ⟨(KArgList.mono hE a h).1, by simp [KCmd.dec, (KArgList.mono hE a h).2]⟩

theorem KCmdList.mono (hE : Extends σ σ') :
    ∀ cs : KCmdList, cs.valid σ → cs.valid σ' ∧ cs.dec σ' = cs.dec σ
  | .nil, _ => ⟨trivial, rfl⟩
  | .cons c cs, ⟨hc, hcs⟩ =>
    have h1 := KCmd.mono hE c hc
    have ih := KCmdList.mono hE cs hcs
    ⟨⟨h1.1, ih.1⟩, by simp [KCmdList.dec, h1.2, ih.2]⟩

def argsRep : RepD KArgList CArgList := ⟨KArgList.dec, KArgList.valid, fun a hE h => KArgList.mono hE a h⟩
def stateRep : RepD KState CState := ⟨KState.dec, KState.valid, fun s hE h => KState.mono hE s h⟩
def cmdRep : RepD KCmd CCmd := ⟨KCmd.dec, KCmd.valid, fun c hE h => KCmd.mono hE c h⟩
def cmdsRep : RepD KCmdList CCmdList := ⟨KCmdList.dec, KCmdList.valid, fun c hE h => KCmdList.mono hE c h⟩

end Kairos
