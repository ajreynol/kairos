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

/-- A state's objects read top first, onto its bottom. -/
def KState.decL (σ : Store) (b : Bool) : List KStateObj → CState
  | [] => if b then .Stuck else .nil
  | so :: l => .cons (so.dec σ) (KState.decL σ b l)

def KState.dec (σ : Store) (s : KState) : CState := KState.decL σ s.stuck s.objs.toList.reverse

def KState.valid (σ : Store) (s : KState) : Prop := ∀ so ∈ s.objs.toList, so.valid σ

@[simp] theorem KState.dec_push (σ : Store) (s : KState) (so : KStateObj) :
    (s.push so).dec σ = .cons (so.dec σ) (s.dec σ) := by
  simp [KState.dec, KState.push, KState.decL]

@[simp] theorem KState.dec_Stuck (σ : Store) : KState.Stuck.dec σ = .Stuck := rfl
@[simp] theorem KState.dec_nil (σ : Store) : KState.nil.dec σ = .nil := rfl

theorem KState.valid_push {σ : Store} {s : KState} {so : KStateObj} (hs : s.valid σ)
    (hso : so.valid σ) : (s.push so).valid σ := by
  intro x hx
  simp only [KState.push, Array.toList_push, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hs x hx
  · exact hso

theorem KState.valid_push_inv {σ : Store} {s : KState} {so : KStateObj}
    (h : (s.push so).valid σ) : s.valid σ ∧ so.valid σ :=
  ⟨fun x hx => h x (by simp [KState.push, hx]), h so (by simp [KState.push])⟩

/-- A state whose top is `x`, as that push. -/
theorem KState.back_view {s : KState} {x : KStateObj} (h : s.objs.back? = some x) :
    s = ({ s with objs := s.objs.pop } : KState).push x := by
  rw [← Array.getLast?_toList, List.getLast?_eq_some_iff] at h
  obtain ⟨ys, hys⟩ := h
  cases s with
  | mk b a =>
    simp only [KState.push, KState.mk.injEq, true_and]
    apply Array.toList_inj.mp
    simp only at hys
    simp [Array.toList_pop, hys]

theorem KState.dec_eq_Stuck {σ : Store} {s : KState} :
    s.dec σ = .Stuck ↔ (s.stuck && s.objs.isEmpty) = true := by
  cases s with
  | mk b a =>
    simp only [KState.dec, Bool.and_eq_true, Array.isEmpty_iff]
    rcases hl : a.toList.reverse with _ | ⟨x, l⟩
    · have : a = #[] := by
        apply Array.toList_inj.mp; simpa using hl
      cases b <;> simp [KState.decL, this]
    · have : a ≠ #[] := by rintro rfl; simp at hl
      simp [KState.decL, this]

theorem KState.valid_Stuck (σ : Store) : KState.Stuck.valid σ := by
  intro x hx; simp [KState.Stuck] at hx
theorem KState.valid_nil (σ : Store) : KState.nil.valid σ := by
  intro x hx; simp [KState.nil] at hx

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

theorem KState.decL_mono (hE : Extends σ σ') (b : Bool) :
    ∀ l : List KStateObj, (∀ so ∈ l, so.valid σ) → KState.decL σ' b l = KState.decL σ b l
  | [], _ => rfl
  | so :: l, h => by
    simp only [KState.decL, (KStateObj.mono hE so (h so (.head _))).2,
      KState.decL_mono hE b l (fun x hx => h x (.tail _ hx))]

theorem KState.mono (hE : Extends σ σ') (s : KState) (h : s.valid σ) :
    s.valid σ' ∧ s.dec σ' = s.dec σ :=
  ⟨fun so hso => (KStateObj.mono hE so (h so hso)).1,
   KState.decL_mono hE _ _ (fun so hso => h so (List.mem_reverse.mp hso))⟩

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
