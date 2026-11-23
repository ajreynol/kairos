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
theorem findPush_some {a : Array KStateObj} :
    ∀ {i j : Nat} {A : Id}, findPush a i = some (j, A) → a[j]? = some (.assume_push A)
  | 0, _, _, h => by simp [findPush] at h
  | i + 1, j, A, h => by
    simp only [findPush] at h
    split at h
    · rename_i A' h'
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact h'
    · exact findPush_some h

/-- Logos's walk down to the most recent `assume_push`, from the top `i`
objects of a state, as `findPush`. -/
theorem step_pop_decL (S : CState) (r : CRule) (args : CArgList) (prems : CIndexList)
    (a : Array KStateObj) (b : Bool) : ∀ i, i ≤ a.size →
    __eo_invoke_cmd_step_pop S (KState.decL σ b (a.toList.take i).reverse) r args prems =
      match findPush a i with
      | some (j, A) => __eo_push_proven (__eo_cmd_step_pop_proven S r args (σ.decode A) prems)
          (KState.decL σ b (a.toList.take j).reverse)
      | none => .Stuck
  | 0, _ => by
    simp only [List.take_zero, List.reverse_nil, findPush, KState.decL]
    rw [__eo_invoke_cmd_step_pop.eq_3] <;> cases b <;> simp
  | i + 1, hi => by
    have hget : a.toList[i]? = some a[i] := by simp
    rw [List.take_add_one, hget]
    simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, KState.decL, findPush,
      show a[i]? = some a[i] from by simp]
    cases h : a[i] with
    | assume_push A => simp only [KStateObj.dec]; rw [__eo_invoke_cmd_step_pop.eq_1]
    | assume F =>
      simp only [KStateObj.dec]
      rw [__eo_invoke_cmd_step_pop.eq_2]; kside
      exact step_pop_decL S r args prems a b i (by omega)
    | proven F =>
      simp only [KStateObj.dec]
      rw [__eo_invoke_cmd_step_pop.eq_2]; kside
      exact step_pop_decL S r args prems a b i (by omega)

theorem k_invoke_cmd_step_pop_sim (fuel : Nat) (hI : Inv sem σ) {s : KState} (hs : s.valid σ)
    (r : CRule) {args : KArgList} (hargs : args.valid σ) (prems : CIndexList) :
    SimR stateRep sem σ (k_invoke_cmd_step_pop fuel s r args prems)
      (__eo_invoke_cmd_step_pop (s.dec σ) (s.dec σ) r (args.dec σ) prems) := by
  have e : KState.decL σ s.stuck (s.objs.toList.take s.objs.size).reverse = s.dec σ := by
    simp only [KState.dec]; rw [List.take_of_length_le (by simp)]
  have := step_pop_decL (σ := σ) (s.dec σ) r (args.dec σ) prems s.objs s.stuck s.objs.size (Nat.le_refl _)
  rw [e] at this
  rw [this]
  unfold k_invoke_cmd_step_pop
  match hf : findPush s.objs s.objs.size with
  | some (j, A) =>
    have hA : A < σ.size :=
      hs (.assume_push A) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? (findPush_some hf)))
    have hs2 : ({ s with objs := s.objs.shrink j } : KState).valid σ :=
      fun x hx => hs x (List.mem_of_mem_take (by simpa [Array.toList_shrink] using hx))
    have hd2 : ({ s with objs := s.objs.shrink j } : KState).dec σ =
        KState.decL σ s.stuck (s.objs.toList.take j).reverse := by
      simp [KState.dec]
    have hΓ := Ctx.cons (f := Fact.state ({ s with objs := s.objs.shrink j } : KState)
      (({ s with objs := s.objs.shrink j } : KState).dec σ)) ⟨hs2, rfl⟩ (Ctx.nil σ)
    refine SimR.step hΓ (simR_of (k__eo_cmd_step_pop_proven_sim fuel hI hs r hargs hA prems))
      fun t σ1 hI1 hΓ1 => ?_
    have ht := hΓ1.term (.head _)
    have hs21 := Ctx.state hΓ1 (.tail _ (.head _))
    exact (k_push_proven_sim fuel hI1 ht.1 hs21.1).congr (by rw [ht.2, hs21.2, hd2])
  | none => exact SimR.pure hI (KState.valid_Stuck σ) rfl

theorem k_assume_guard_sim (fuel : Nat) (hI : Inv sem σ) {F : Id} (hF : F < σ.size) :
    Sim sem σ (k_assume_guard fuel F)
      (__eo_and (__eo_is_bool_type (σ.decode F)) (__eo_is_closed (σ.decode F))) := by
  have hΓ := Ctx.arg hF (Ctx.nil σ)
  refine Sim.step hΓ ((allS__eo_is_bool_type fuel) hI hF) fun b σ1 hI1 hΓ1 => ?_
  refine Sim.step hΓ1 (C__eo_is_closed (allS__eo_is_closed fuel) hI1 hΓ1 (.tail _ (.head _)))
    fun c σ2 hI2 hΓ2 => ?_
  exact C__eo_and (allS__eo_and fuel) hI2 hΓ2 (.tail _ (.head _)) (.head _)

theorem k_invoke_cmd_sim (fuel : Nat) (hI : Inv sem σ) (S : KState) (c : KCmd) (hS : S.valid σ)
    (hc : c.valid σ) :
    SimR stateRep sem σ (k_invoke_cmd fuel S c) (__eo_invoke_cmd (S.dec σ) (c.dec σ)) := by
  unfold k_invoke_cmd
  by_cases hst : (S.stuck && S.objs.isEmpty) = true
  · simp only [hst, ↓reduceIte]
    rw [KState.dec_eq_Stuck.mpr hst, __eo_invoke_cmd.eq_1]
    exact SimR.pure hI (KState.valid_Stuck σ) rfl
  · have hne : S.dec σ = .Stuck → False := fun h => hst (KState.dec_eq_Stuck.mp h)
    simp only [hst, Bool.false_eq_true, ↓reduceIte]
    cases c with
    | assume_push F =>
      have hΓ := Ctx.arg (show F < σ.size from hc)
        (Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.nil σ))
      simp only [KCmd.dec]
      rw [__eo_invoke_cmd.eq_2 _ _ hne]
      refine SimR.step hΓ (simR_of (k_assume_guard_sim fuel hI hc)) fun a σ1 hI1 hΓ1 => ?_
      have ha := hΓ1.term (.head _)
      have hF1 := hΓ1.term (.tail _ (.head _))
      have hS1 := Ctx.state hΓ1 (.tail _ (.tail _ (.head _)))
      have := k_push_check_sim (mk := .assume_push) (lmk := .assume_push) (fun _ _ => rfl)
        (fun _ => rfl) __eo_push_assume_check.eq_1
        (fun b F S h => by rw [__eo_push_assume_check.eq_2]; exact h) hI1 hF1.1 hS1.1 (b := a)
      rw [ha.2, hF1.2, hS1.2] at this
      exact this
    | check_proven F =>
      simp only [KCmd.dec]
      rw [__eo_invoke_cmd.eq_3 _ _ hne]
      exact k_invoke_cmd_check_proven_sim fuel hI _ hS hc
    | step r args prems =>
      have hΓ := Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.nil σ)
      simp only [KCmd.dec]
      rw [__eo_invoke_cmd.eq_4 _ _ _ _ hne]
      refine SimR.step hΓ (simR_of (k__eo_cmd_step_proven_sim fuel hI hS r hc prems))
        fun t σ1 hI1 hΓ1 => ?_
      have ht := hΓ1.term (.head _)
      have hS1 := Ctx.state hΓ1 (.tail _ (.head _))
      exact (k_push_proven_sim fuel hI1 ht.1 hS1.1).congr (by rw [ht.2, hS1.2])
    | step_pop r args prems =>
      simp only [KCmd.dec]
      rw [__eo_invoke_cmd.eq_5 _ _ _ _ hne]
      exact k_invoke_cmd_step_pop_sim fuel hI hS r hc prems

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
  refine SimR.step hΓ (k_invoke_assume_list_sim fuel as hI (KState.valid_nil σ) has) fun s σ1 hI1 hΓ1 => ?_
  have hs := Ctx.state hΓ1 (.head _)
  have hcs1 : cs.valid σ1 ∧ cs.dec σ1 = cs.dec σ := hΓ1 _ (.tail _ (.head _))
  refine SimR.step hΓ1 ((k_invoke_cmd_list_sim fuel cs hI1 hs.1 hcs1.1).congr
    (by rw [hs.2, hcs1.2] <;> rfl)) fun s' σ2 hI2 hΓ2 => ?_
  have hs' := Ctx.state hΓ2 (.head _)
  exact (k_state_is_refutation_sim fuel hI2 hs'.1).congr (by rw [hs'.2] <;> rfl)

/-! ## The theorem -/
/-- On a store: if Kairos's checker accepts ids standing for assumptions and
commands, Logos's checker accepts what they stand for. The central theorem,
`kairos_refines_logos` (Checker/Api), is stated on Logos's values instead. -/
theorem kairos_refines_logos_store (fuel : Nat) (σ : Store) (hI : Inv sem σ) {as : KArgList}
    {cs : KCmdList} (has : as.valid σ) (hcs : cs.valid σ) :
    Ok (k_checker_is_refutation fuel as cs) σ (fun b _ =>
      b = true → __eo_checker_is_refutation (as.dec σ) (cs.dec σ) = true) :=
  Ok.mono (k_checker_is_refutation_sim fuel hI has hcs) fun b _ p h => p.dec ▸ h

end Kairos.Checker
