/-
The lifted fallback: run Logos's own function on decoded arguments and
intern the result. It is correct for any function, generically; it costs a
traversal of the arguments and of the result, so the generator uses it only
for programs it cannot compile yet, and lists them.
-/
import Kairos.Runtime.Prog

namespace Kairos
open Eo Store

variable {sem : Sem} {σ : Store}

/-- Intern a Logos term, bottom up. -/
def internTerm : Term → K Id
  | .Apply f x => do let a ← internTerm f; let b ← internTerm x; intern (.Apply a b)
  | .Var s T => do let a ← internTerm s; let b ← internTerm T; intern (.Var a b)
  | .DtcAppType s T => do let a ← internTerm s; let b ← internTerm T; intern (.DtcAppType a b)
  | .UConst i T => do let b ← internTerm T; intern (.UConst i b)
  | .Stuck => pure 0
  | .UOp o => intern (.UOp o)
  | .__eo_List => intern .__eo_List
  | .__eo_List_nil => intern .__eo_List_nil
  | .__eo_List_cons => intern .__eo_List_cons
  | .Bool => intern .Bool
  | .Boolean b => intern (.Boolean b)
  | .Numeral n => intern (.Numeral n)
  | .Rational q => intern (.Rational q)
  | .String s => intern (.String s)
  | .Binary w n => intern (.Binary w n)
  | .Type => intern .Type
  | .FunType => intern .FunType
  | .DatatypeType s dd => intern (.DatatypeType s dd)
  | .DatatypeTypeRef s => intern (.DatatypeTypeRef s)
  | .DtCons s dd i => intern (.DtCons s dd i)
  | .DtSel s dd i j => intern (.DtSel s dd i j)
  | .USort i => intern (.USort i)

theorem internTerm_sim : (t : Term) → ∀ {σ : Store}, Inv sem σ → Sim sem σ (internTerm t) t
  | .Apply f x, σ, hI => by
    simp only [internTerm]
    refine Sim.step (Ctx.nil σ) (internTerm_sim f hI) fun a σ1 hI1 hΓ1 => ?_
    refine Sim.step hΓ1 (internTerm_sim x hI1) fun b σ2 hI2 hΓ2 => ?_
    exact intern_apply hI2 hΓ2 (.tail _ (.head _)) (.head _)
  | .Var s T, σ, hI => by
    simp only [internTerm]
    refine Sim.step (Ctx.nil σ) (internTerm_sim s hI) fun a σ1 hI1 hΓ1 => ?_
    refine Sim.step hΓ1 (internTerm_sim T hI1) fun b σ2 hI2 hΓ2 => ?_
    exact intern_var hI2 hΓ2 (.tail _ (.head _)) (.head _)
  | .DtcAppType s T, σ, hI => by
    simp only [internTerm]
    refine Sim.step (Ctx.nil σ) (internTerm_sim s hI) fun a σ1 hI1 hΓ1 => ?_
    refine Sim.step hΓ1 (internTerm_sim T hI1) fun b σ2 hI2 hΓ2 => ?_
    exact intern_dtcAppType hI2 hΓ2 (.tail _ (.head _)) (.head _)
  | .UConst i T, σ, hI => by
    simp only [internTerm]
    refine Sim.step (Ctx.nil σ) (internTerm_sim T hI) fun b σ1 hI1 hΓ1 => ?_
    exact intern_uconst hI1 hΓ1 (.head _)
  | .Stuck, σ, hI => by simp only [internTerm]; exact Sim.stuck hI
  | .UOp _, σ, hI | .__eo_List, σ, hI | .__eo_List_nil, σ, hI | .__eo_List_cons, σ, hI
  | .Bool, σ, hI | .Boolean _, σ, hI | .Numeral _, σ, hI | .Rational _, σ, hI
  | .String _, σ, hI | .Binary _ _, σ, hI | .Type, σ, hI | .FunType, σ, hI
  | .DatatypeType _ _, σ, hI | .DatatypeTypeRef _, σ, hI | .DtCons _ _ _, σ, hI
  | .DtSel _ _ _ _, σ, hI | .USort _, σ, hI => by
    simp only [internTerm]; exact intern_leaf hI rfl

/-- A program computed by Logos on decoded arguments. -/
theorem Sim.lift {t : Term} (hI : Inv sem σ) : Sim sem σ (internTerm t) t :=
  internTerm_sim t hI

end Kairos
