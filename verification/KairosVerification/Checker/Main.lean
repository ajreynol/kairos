/-
The checker, above the rule dispatch: commands, command lists, assumption
lists, and the end-to-end theorem.
-/
import Kairos.Checker.Main
import KairosVerification.Gen.Dispatch

set_option linter.unusedVariables false

namespace Kairos.Checker
open Eo Kairos Store SmtEval Kairos.Gen

variable {σ : Store} {Γ : List Fact}
theorem k_invoke_cmd_step_pop_sim (fuel : Nat) (hI : Inv sem σ) {s : KState} (hs : s.valid σ)
    (r : CRule) {args : KArgList} (hargs : args.valid σ) (prems : CIndexList) :
    ∀ s2 : KState, s2.valid σ →
      SimR stateRep sem σ (k_invoke_cmd_step_pop fuel s s2 r args prems)
        (__eo_invoke_cmd_step_pop (s.dec σ) (s2.dec σ) r (args.dec σ) prems)
  | .cons (.assume_push A) s2, ⟨hA, hs2⟩ => by
    have hΓ := Ctx.cons (f := Fact.state s2 (s2.dec σ)) ⟨hs2, rfl⟩ (Ctx.nil σ)
    simp only [k_invoke_cmd_step_pop, KState.dec, KStateObj.dec]
    rw [__eo_invoke_cmd_step_pop.eq_1]
    refine SimR.step hΓ (simR_of (k__eo_cmd_step_pop_proven_sim fuel hI hs r hargs hA prems))
      fun t σ1 hI1 hΓ1 => ?_
    have ht := hΓ1.term (.head _)
    have hs21 := Ctx.state hΓ1 (.tail _ (.head _))
    exact (k_push_proven_sim fuel hI1 ht.1 hs21.1).congr (by rw [ht.2, hs21.2]; rfl)
  | .cons (.assume F) s2, ⟨_, hs2⟩ => by
    simp only [k_invoke_cmd_step_pop, KState.dec, KStateObj.dec]
    rw [__eo_invoke_cmd_step_pop.eq_2]; kside
    exact k_invoke_cmd_step_pop_sim fuel hI hs r hargs prems s2 hs2
  | .cons (.proven F) s2, ⟨_, hs2⟩ => by
    simp only [k_invoke_cmd_step_pop, KState.dec, KStateObj.dec]
    rw [__eo_invoke_cmd_step_pop.eq_2]; kside
    exact k_invoke_cmd_step_pop_sim fuel hI hs r hargs prems s2 hs2
  | .nil, _ => by
    simp only [k_invoke_cmd_step_pop, KState.dec]
    rw [__eo_invoke_cmd_step_pop.eq_3]; kside
    exact SimR.pure hI trivial rfl
  | .Stuck, _ => by
    simp only [k_invoke_cmd_step_pop, KState.dec]
    rw [__eo_invoke_cmd_step_pop.eq_3]; kside
    exact SimR.pure hI trivial rfl

theorem k_assume_guard_sim (fuel : Nat) (hI : Inv sem σ) {F : Id} (hF : F < σ.size) :
    Sim sem σ (k_assume_guard fuel F)
      (__eo_and (__eo_is_bool_type (σ.decode F)) (__eo_is_closed (σ.decode F))) := by
  have hΓ := Ctx.arg hF (Ctx.nil σ)
  refine Sim.step hΓ ((allS__eo_is_bool_type fuel) hI hF) fun b σ1 hI1 hΓ1 => ?_
  refine Sim.step hΓ1 (C__eo_is_closed (allS__eo_is_closed fuel) hI1 hΓ1 (.tail _ (.head _)))
    fun c σ2 hI2 hΓ2 => ?_
  exact C__eo_and (allS__eo_and fuel) hI2 hΓ2 (.tail _ (.head _)) (.head _)

theorem k_invoke_cmd_sim (fuel : Nat) (hI : Inv sem σ) :
    ∀ (S : KState) (c : KCmd), S.valid σ → c.valid σ →
      SimR stateRep sem σ (k_invoke_cmd fuel S c) (__eo_invoke_cmd (S.dec σ) (c.dec σ))
  | .Stuck, c, _, _ => by
    simp only [k_invoke_cmd, KState.dec]
    rw [__eo_invoke_cmd.eq_1]
    exact SimR.pure hI trivial rfl
  | S, .assume_push F, hS, hF => by
    have hΓ := Ctx.arg hF (Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.nil σ))
    cases S with
    | Stuck => simp only [k_invoke_cmd, KState.dec]; rw [__eo_invoke_cmd.eq_1]; exact SimR.pure hI trivial rfl
    | _ =>
      all_goals
        simp only [k_invoke_cmd, KState.dec, KCmd.dec]
        rw [__eo_invoke_cmd.eq_2] <;> try (intros; simp_all; done)
        refine SimR.step hΓ (simR_of (k_assume_guard_sim fuel hI hF)) fun a σ1 hI1 hΓ1 => ?_
        have ha := hΓ1.term (.head _)
        have hF1 := hΓ1.term (.tail _ (.head _))
        have hS1 := Ctx.state hΓ1 (.tail _ (.tail _ (.head _)))
        have := k_push_check_sim (mk := .assume_push) (lmk := .assume_push) (fun _ _ => rfl)
          (fun _ => rfl) __eo_push_assume_check.eq_1
          (fun b F S h => by rw [__eo_push_assume_check.eq_2]; exact h) hI1 hF1.1 hS1.1 (b := a)
        rw [ha.2, hF1.2, hS1.2] at this
        exact this
  | S, .check_proven F, hS, hF => by
    cases S with
    | Stuck => simp only [k_invoke_cmd, KState.dec]; rw [__eo_invoke_cmd.eq_1]; exact SimR.pure hI trivial rfl
    | _ =>
      all_goals
        simp only [k_invoke_cmd, KState.dec, KCmd.dec]
        rw [__eo_invoke_cmd.eq_3] <;> try (intros; simp_all; done)
        exact k_invoke_cmd_check_proven_sim fuel hI _ hS hF
  | S, .step r args prems, hS, hargs => by
    have hΓ := Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.nil σ)
    cases S with
    | Stuck => simp only [k_invoke_cmd, KState.dec]; rw [__eo_invoke_cmd.eq_1]; exact SimR.pure hI trivial rfl
    | _ =>
      all_goals
        simp only [k_invoke_cmd, KState.dec, KCmd.dec]
        rw [__eo_invoke_cmd.eq_4] <;> try (intros; simp_all; done)
        refine SimR.step hΓ (simR_of (k__eo_cmd_step_proven_sim fuel hI hS r hargs prems))
          fun t σ1 hI1 hΓ1 => ?_
        have ht := hΓ1.term (.head _)
        have hS1 := Ctx.state hΓ1 (.tail _ (.head _))
        exact (k_push_proven_sim fuel hI1 ht.1 hS1.1).congr (by rw [ht.2, hS1.2] <;> rfl)
  | S, .step_pop r args prems, hS, hargs => by
    cases S with
    | Stuck => simp only [k_invoke_cmd, KState.dec]; rw [__eo_invoke_cmd.eq_1]; exact SimR.pure hI trivial rfl
    | _ =>
      all_goals
        simp only [k_invoke_cmd, KState.dec, KCmd.dec]
        rw [__eo_invoke_cmd.eq_5] <;> try (intros; simp_all; done)
        exact k_invoke_cmd_step_pop_sim fuel hI hS r hargs prems _ hS

theorem k_invoke_cmd_list_sim (fuel : Nat) :
    ∀ (cs : KCmdList) {σ : Store} {S : KState}, Inv sem σ → S.valid σ → cs.valid σ →
      SimR stateRep sem σ (k_invoke_cmd_list fuel S cs) (__eo_invoke_cmd_list (S.dec σ) (cs.dec σ))
  | .nil, σ, S, hI, hS, _ => by
    simp only [k_invoke_cmd_list, KCmdList.dec]
    rw [__eo_invoke_cmd_list.eq_1]
    exact SimR.pure hI hS rfl
  | .cons c cs, σ, S, hI, hS, ⟨hc, hcs⟩ => by
    have hΓ := Ctx.cons (f := ⟨cmdsRep, cs, cs.dec σ⟩) ⟨hcs, rfl⟩ (Ctx.nil σ)
    simp only [k_invoke_cmd_list, KCmdList.dec]
    rw [__eo_invoke_cmd_list.eq_2]
    refine SimR.step hΓ (k_invoke_cmd_sim fuel hI S c hS hc) fun S' σ1 hI1 hΓ1 => ?_
    have hS' := Ctx.state hΓ1 (.head _)
    have hcs1 : cs.valid σ1 ∧ cs.dec σ1 = cs.dec σ := hΓ1 _ (.tail _ (.head _))
    exact (k_invoke_cmd_list_sim fuel cs hI1 hS'.1 hcs1.1).congr (by rw [hS'.2, hcs1.2])

theorem k_state_is_refutation_sim (fuel : Nat) (hI : Inv sem σ) {s : KState} (hs : s.valid σ) :
    SimR (natRep Bool) sem σ (k_state_is_refutation fuel s) (__eo_state_is_refutation (s.dec σ)) := by
  have hΓ := Ctx.cons (f := Fact.state s (s.dec σ)) ⟨hs, rfl⟩ (Ctx.nil σ)
  rw [__eo_state_is_refutation]
  refine SimR.step hΓ (simR_of (intern_leaf hI rfl)) fun f σ1 hI1 hΓ1 => ?_
  have hf := hΓ1.term (.head _)
  have hs1 := Ctx.state hΓ1 (.tail _ (.head _))
  refine SimR.step hΓ1 ((k_invoke_cmd_check_proven_sim fuel hI1 s hs1.1 hf.1).congr
    (by rw [hs1.2, hf.2] <;> rfl)) fun s' σ2 hI2 hΓ2 => ?_
  have hs' := Ctx.state hΓ2 (.head _)
  exact (SimR.native hI2).congr (by rw [k_state_is_closed_eq (σ := σ2), hs'.2] <;> rfl)

theorem k_invoke_assume_list_sim (fuel : Nat) {S : KState} :
    ∀ (as : KArgList) {σ : Store}, Inv sem σ → S.valid σ → as.valid σ →
      SimR stateRep sem σ (k_invoke_assume_list fuel S as)
        (__eo_invoke_assume_list (S.dec σ) (as.dec σ))
  | .nil, σ, hI, hS, _ => by
    simp only [k_invoke_assume_list, KArgList.dec]
    rw [__eo_invoke_assume_list.eq_1]
    exact SimR.pure hI hS rfl
  | .cons F as, σ, hI, hS, ⟨hF, has⟩ => by
    have hΓ := Ctx.arg hF (Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.nil σ))
    simp only [k_invoke_assume_list, KArgList.dec]
    rw [__eo_invoke_assume_list.eq_2]
    refine SimR.step hΓ (k_invoke_assume_list_sim fuel as hI hS has) fun rest σ1 hI1 hΓ1 => ?_
    have hF1 := hΓ1.term (.tail _ (.head _))
    refine SimR.step hΓ1 (simR_of (k_assume_guard_sim fuel hI1 hF1.1)) fun a σ2 hI2 hΓ2 => ?_
    have ha := hΓ2.term (.head _)
    have hrest := Ctx.state hΓ2 (.tail _ (.head _))
    have hF2 := hΓ2.term (.tail _ (.tail _ (.head _)))
    have := k_push_check_sim (mk := .assume) (lmk := .assume) (fun _ _ => rfl) (fun _ => rfl)
      __eo_push_input_assume_check.eq_1
      (fun b F S h => by rw [__eo_push_input_assume_check.eq_2]; exact h) hI2 hF2.1 hrest.1 (b := a)
    rw [ha.2, hF2.2, hrest.2, hF1.2] at this
    exact this

theorem k_checker_is_refutation_sim (fuel : Nat) (hI : Inv sem σ) {as : KArgList} {cs : KCmdList}
    (has : as.valid σ) (hcs : cs.valid σ) :
    SimR (natRep Bool) sem σ (k_checker_is_refutation fuel as cs)
      (__eo_checker_is_refutation (as.dec σ) (cs.dec σ)) := by
  have hΓ := Ctx.cons (f := ⟨cmdsRep, cs, cs.dec σ⟩) ⟨hcs, rfl⟩ (Ctx.nil σ)
  rw [__eo_checker_is_refutation]
  refine SimR.step hΓ (k_invoke_assume_list_sim fuel as hI trivial has) fun s σ1 hI1 hΓ1 => ?_
  have hs := Ctx.state hΓ1 (.head _)
  have hcs1 : cs.valid σ1 ∧ cs.dec σ1 = cs.dec σ := hΓ1 _ (.tail _ (.head _))
  refine SimR.step hΓ1 ((k_invoke_cmd_list_sim fuel cs hI1 hs.1 hcs1.1).congr
    (by rw [hs.2, hcs1.2] <;> rfl)) fun s' σ2 hI2 hΓ2 => ?_
  have hs' := Ctx.state hΓ2 (.head _)
  exact (k_state_is_refutation_sim fuel hI2 hs'.1).congr (by rw [hs'.2] <;> rfl)

/-! ## The theorem -/
/-- If Kairos says the commands refute the assumptions, so does Logos's
checker. With Logos's `correct___eo_is_refutation`, the assumptions are then
unsatisfiable. -/
theorem kairos_refines_logos (fuel : Nat) (σ : Store) (hI : Inv sem σ) {as : KArgList}
    {cs : KCmdList} (has : as.valid σ) (hcs : cs.valid σ) :
    Ok (k_checker_is_refutation fuel as cs) σ (fun b _ =>
      b = true → __eo_checker_is_refutation (as.dec σ) (cs.dec σ) = true) :=
  Ok.mono (k_checker_is_refutation_sim fuel hI has hcs) fun b _ p h => p.dec ▸ h

end Kairos.Checker
