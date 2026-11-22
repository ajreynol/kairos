/-
Golden output for the generated rule dispatch (Kairos/Gen/Dispatch.lean),
written by hand for CpcMini's rules. Kept for reference; not built.
-/
import Kairos.Checker.Base

set_option linter.unusedVariables false

namespace Kairos.Checker
open Eo Kairos Store SmtEval Kairos.Gen

variable {σ : Store} {Γ : List Fact}

/-! ## The rule dispatch (CpcMini's rules; to be generated) -/

def k__eo_cmd_step_proven (fuel : Nat) (S : KState) : CRule → KArgList → CIndexList → K Id
  | .contra, .nil, .cons n1 (.cons n2 .nil) => do
    let p1 ← k_state_proven_nth S n1
    let p2 ← k_state_proven_nth S n2
    k__eo_prog_contra fuel p1 p2
  | .refl, .cons a1 .nil, .nil => k__eo_prog_refl fuel a1
  | .symm, .nil, .cons n1 .nil => do
    let p1 ← k_state_proven_nth S n1
    k__eo_prog_symm fuel p1
  | .trans, .nil, prems => do
    let a ← intern (.UOp .and)
    let l ← k_mk_premise_list fuel a prems S
    k__eo_prog_trans fuel l
  | _, _, _ => pure 0

theorem k__eo_cmd_step_proven_sim (fuel : Nat) (hI : Inv sem σ) {S : KState} (hS : S.valid σ)
    (r : CRule) {args : KArgList} (hargs : args.valid σ) (prems : CIndexList) :
    Sim sem σ (k__eo_cmd_step_proven fuel S r args prems)
      (__eo_cmd_step_proven (S.dec σ) r (args.dec σ) prems) := by
  have hΓ := Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.stuck hI)
  unfold k__eo_cmd_step_proven
  split
  · rw [KArgList.dec, __eo_cmd_step_proven.eq_1]
    refine Sim.step hΓ (k_state_proven_nth_sim hI S _ hS) fun p1 σ1 hI1 hΓ1 => ?_
    have hS1 := Ctx.state hΓ1 (.tail _ (.head _))
    refine Sim.step hΓ1 ((k_state_proven_nth_sim hI1 S _ hS1.1).congr (by rw [hS1.2]))
      fun p2 σ2 hI2 hΓ2 => ?_
    exact C__eo_prog_contra (spec fuel) hI2 hΓ2 (.tail _ (.head _)) (.head _)
  · rename_i a1
    obtain ⟨ha1, -⟩ := hargs
    simp only [KArgList.dec]
    rw [__eo_cmd_step_proven.eq_2]
    exact (spec fuel).s__eo_prog_refl hI ha1
  · rw [KArgList.dec, __eo_cmd_step_proven.eq_3]
    refine Sim.step hΓ (k_state_proven_nth_sim hI S _ hS) fun p1 σ1 hI1 hΓ1 => ?_
    exact C__eo_prog_symm (spec fuel) hI1 hΓ1 (.head _)
  · rw [KArgList.dec, __eo_cmd_step_proven.eq_4]
    refine Sim.step hΓ (intern_leaf hI rfl) fun a σ1 hI1 hΓ1 => ?_
    have hS1 := Ctx.state hΓ1 (.tail _ (.head _))
    have ha := hΓ1.term (.head _)
    refine Sim.step hΓ1 ((k_mk_premise_list_sim fuel prems hI1 ha.1 hS1.1).congr
      (by rw [ha.2, hS1.2])) fun l σ2 hI2 hΓ2 => ?_
    exact C__eo_prog_trans (spec fuel) hI2 hΓ2 (.head _)
  · rename_i h1 h2 h3 h4
    rw [__eo_cmd_step_proven.eq_5]
    · exact Sim.stuck hI
    all_goals (intros; simp_all)

def k__eo_cmd_step_pop_proven (fuel : Nat) (S : KState) : CRule → KArgList → Id → CIndexList → K Id
  | .scope, .nil, A, .cons n1 .nil => do
    let p1 ← k_state_proven_nth S n1
    k__eo_prog_scope fuel A p1
  | _, _, _, _ => pure 0

theorem k__eo_cmd_step_pop_proven_sim (fuel : Nat) (hI : Inv sem σ) {S : KState} (hS : S.valid σ)
    (r : CRule) {args : KArgList} (hargs : args.valid σ) {A : Id} (hA : A < σ.size)
    (prems : CIndexList) :
    Sim sem σ (k__eo_cmd_step_pop_proven fuel S r args A prems)
      (__eo_cmd_step_pop_proven (S.dec σ) r (args.dec σ) (σ.decode A) prems) := by
  have hΓ := Ctx.arg hA (Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.stuck hI))
  unfold k__eo_cmd_step_pop_proven
  split
  · rw [KArgList.dec, __eo_cmd_step_pop_proven.eq_1]
    refine Sim.step hΓ (k_state_proven_nth_sim hI S _ hS) fun p1 σ1 hI1 hΓ1 => ?_
    exact C__eo_prog_scope (spec fuel) hI1 hΓ1 (.tail _ (.head _)) (.head _)
  · rw [__eo_cmd_step_pop_proven.eq_2]
    · exact Sim.stuck hI
    all_goals (intros; simp_all)

end Kairos.Checker
