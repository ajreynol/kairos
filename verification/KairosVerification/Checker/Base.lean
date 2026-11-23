/-
The checker, below the rule dispatch: Kairos versions of the functions of
lean-meta's checker template that the dispatch uses, and their proofs.

The template is the same for every signature; only the rule dispatch
(`Kairos/Gen/Dispatch.lean`, generated) depends on the rules. None of these
functions needs fuel of its own: each recurses structurally on a checker
list, and calls generated programs, which are proven at every fuel
(`Gen.spec`).
-/
import Kairos.Checker.Base
import KairosVerification.Checker.Types
import KairosVerification.Gen.Programs

set_option linter.unusedVariables false

namespace Kairos.Checker
open Eo Kairos Store SmtEval Kairos.Gen

variable {σ : Store} {Γ : List Fact}

abbrev Fact.state (s : KState) (S : CState) : Fact := ⟨stateRep, s, S⟩

theorem Ctx.state {s : KState} {S : CState} (hΓ : Ctx σ Γ) (h : Fact.state s S ∈ Γ) :
    s.valid σ ∧ s.dec σ = S := hΓ _ h

/-- Run a term program of `Gen` with the facts its arguments are known by. -/
theorem simR_of {m : K Id} {t : Term} (h : Sim sem σ m t) : SimR termRep sem σ m t := SimR.of_sim h

/-! ## Inversion of decoded argument lists -/
@[simp] theorem KArgList.dec_eq_nil {a : KArgList} : a.dec σ = .nil ↔ a = .nil := by
  cases a <;> simp [KArgList.dec]

@[simp] theorem KArgList.dec_eq_cons {a : KArgList} {X : Term} {L : CArgList} :
    a.dec σ = .cons X L ↔ ∃ x l, a = .cons x l ∧ σ.decode x = X ∧ l.dec σ = L := by
  cases a with
  | nil => simp [KArgList.dec]
  | cons x l =>
    simp only [KArgList.dec, CArgList.cons.injEq, KArgList.cons.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x, l, ⟨rfl, rfl⟩, h1, h2⟩
    · rintro ⟨x', l', ⟨rfl, rfl⟩, h1, h2⟩; exact ⟨h1, h2⟩

theorem StateObj_proven_dec (so : KStateObj) : __eo_StateObj_proven (so.dec σ) = σ.decode so.id := by
  cases so <;> rfl

/-- Logos's walk down a state, as indexing the list it decodes. -/
theorem proven_nth_decL (b : Bool) : ∀ (l : List KStateObj) (n : Int),
    __eo_state_proven_nth (KState.decL σ b l) n =
      if 0 ≤ n then (match l[n.toNat]? with
        | some so => σ.decode so.id
        | none => .Boolean true) else .Boolean true
  | [], n => by
    rw [__eo_state_proven_nth.eq_3] <;> (try (cases b <;> simp [KState.decL])) <;> split <;> rfl
  | so :: l, n => by
    by_cases h0 : n = 0
    · subst h0
      simp [KState.decL, __eo_state_proven_nth, StateObj_proven_dec]
    · simp only [KState.decL]
      rw [__eo_state_proven_nth.eq_2 _ _ _ h0, proven_nth_decL b l]
      simp only [native_zplus, native_zneg]
      rcases Int.lt_or_gt_of_ne h0 with h | h
      · simp [show ¬ (0 ≤ n + -1) by omega, show ¬ (0 ≤ n) by omega]
      · have e : n.toNat = (n + -1).toNat + 1 := by omega
        simp [show 0 ≤ n + -1 by omega, show 0 ≤ n by omega, e]

theorem k_state_proven_nth_sim (hI : Inv sem σ) (s : KState) (n : Int) (hs : s.valid σ) :
    Sim sem σ (k_state_proven_nth s n) (__eo_state_proven_nth (s.dec σ) n) := by
  rw [KState.dec, proven_nth_decL]
  unfold k_state_proven_nth
  by_cases h : 0 ≤ n ∧ n.toNat < s.objs.size
  · have e : s.objs.toList.reverse[n.toNat]? = s.objs[s.objs.size - 1 - n.toNat]? := by
      rw [List.getElem?_reverse (by simpa using h.2)]; simp
    simp only [h, and_self, ↓reduceIte, e]
    match hm : s.objs[s.objs.size - 1 - n.toNat]? with
    | some so =>
      exact Sim.pure hI (hs so (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm))) rfl
    | none => exact intern_leaf hI rfl
  · simp only [h, ↓reduceIte]
    have : (if 0 ≤ n then (match s.objs.toList.reverse[n.toNat]? with
        | some so => σ.decode so.id
        | none => Term.Boolean true) else Term.Boolean true) = Term.Boolean true := by
      split
      · rw [List.getElem?_eq_none (by simp; omega)]
      · rfl
    rw [this]
    exact intern_leaf hI rfl

theorem is_closed_decL (b : Bool) : ∀ l : List KStateObj,
    __eo_state_is_closed (KState.decL σ b l) = (!b && l.all (fun so => !so.isPush))
  | [] => by
    cases b
    · simp [KState.decL, __eo_state_is_closed]
    · simp only [KState.decL]; rw [__eo_state_is_closed.eq_4] <;> simp
  | so :: l => by
    cases so with
    | assume_push F => simp [KState.decL, KStateObj.dec, __eo_state_is_closed, KStateObj.isPush]
    | assume F =>
      simp only [KState.decL, KStateObj.dec]
      rw [__eo_state_is_closed.eq_2]; kside
      rw [is_closed_decL b l]; simp [KStateObj.isPush]
    | proven F =>
      simp only [KState.decL, KStateObj.dec]
      rw [__eo_state_is_closed.eq_2]; kside
      rw [is_closed_decL b l]; simp [KStateObj.isPush]

theorem k_state_is_closed_eq (s : KState) : k_state_is_closed s = __eo_state_is_closed (s.dec σ) := by
  rw [KState.dec, is_closed_decL]
  simp [k_state_is_closed, List.all_reverse, Array.all_toList]

/-! ## Pushing onto a state -/
theorem k_push_check_sim {mk : Id → KStateObj} {lmk : Term → CStateObj}
    (hmk : ∀ σ F, (mk F).dec σ = lmk (σ.decode F)) (hid : ∀ F, (mk F).id = F)
    {g : Term → Term → CState → CState}
    (g1 : ∀ F S, g (.Boolean true) F S = .cons (lmk F) S)
    (g2 : ∀ b F S, (b = .Boolean true → False) → g b F S = .Stuck)
    (hI : Inv sem σ) {b F : Id} {s : KState} (hF : F < σ.size) (hs : s.valid σ) :
    SimR stateRep sem σ (k_push_check mk b F s) (g (σ.decode b) (σ.decode F) (s.dec σ)) := by
  apply SimR.withStore
  by_cases hv : σ.view b = .Boolean true
  · simp only [hv, ↓reduceIte]
    rw [decode_of_view hI hv]
    refine SimR.pure hI (KState.valid_push hs (by simp [KStateObj.valid, hid, hF])) ?_
    show KState.dec σ (s.push (mk F)) = _
    simp [hmk, Node.toTerm, g1]
  · simp only [hv, ↓reduceIte]
    refine SimR.pure hI (KState.valid_Stuck σ) ?_
    show KState.dec σ .Stuck = _
    rw [g2]
    · rfl
    · exact fun e => hv (decode_Boolean_inv hI e)

theorem k_push_proven_sim (fuel : Nat) (hI : Inv sem σ) {F : Id} {s : KState} (hF : F < σ.size)
    (hs : s.valid σ) :
    SimR stateRep sem σ (k_push_proven fuel F s) (__eo_push_proven (σ.decode F) (s.dec σ)) := by
  have hΓ := Ctx.arg hF (Ctx.cons (f := Fact.state s (s.dec σ)) ⟨hs, rfl⟩ (Ctx.nil σ))
  rw [__eo_push_proven.eq_1]
  refine SimR.step hΓ (simR_of ((allS__eo_is_bool_type fuel) hI hF)) fun b σ1 hI1 hΓ1 => ?_
  have hb := hΓ1.term (.head _)
  have hF1 := hΓ1.term (.tail _ (.head _))
  have hs1 := Ctx.state hΓ1 (.tail _ (.tail _ (.head _)))
  have := k_push_check_sim (mk := .proven) (lmk := .proven) (fun _ _ => rfl) (fun _ => rfl)
    __eo_push_proven_check.eq_1 (fun b F S h => by rw [__eo_push_proven_check.eq_2]; exact h)
    hI1 hF1.1 hs1.1 (b := b)
  rw [hb.2, hF1.2, hs1.2] at this
  exact this

theorem k_mk_premise_list_sim (fuel : Nat) {f : Id} :
    ∀ (pl : CIndexList) {σ : Store} {S : KState}, Inv sem σ → f < σ.size → S.valid σ →
      Sim sem σ (k_mk_premise_list fuel f pl S)
        (__eo_mk_premise_list (σ.decode f) pl (S.dec σ))
  | .nil, σ, S, hI, hf, hS => by
    have hΓ := Ctx.arg hf (Ctx.nil σ)
    simp only [k_mk_premise_list]
    rw [__eo_mk_premise_list.eq_1]
    refine Sim.step hΓ (intern_leaf hI rfl) fun b σ1 hI1 hΓ1 => ?_
    exact C__eo_nil (allS__eo_nil fuel) hI1 hΓ1 (.tail _ (.head _)) (.head _)
  | .cons n pl, σ, S, hI, hf, hS => by
    have hΓ := Ctx.arg hf (Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.nil σ))
    simp only [k_mk_premise_list]
    rw [__eo_mk_premise_list.eq_2]
    refine Sim.step hΓ (k_state_proven_nth_sim hI S n hS) fun x σ1 hI1 hΓ1 => ?_
    have hS1 := Ctx.state hΓ1 (.tail _ (.tail _ (.head _)))
    have hf1 := hΓ1.term (.tail _ (.head _))
    refine Sim.step hΓ1 ((k_mk_premise_list_sim fuel pl hI1 hf1.1 hS1.1).congr
      (by rw [hf1.2, hS1.2])) fun r σ2 hI2 hΓ2 => ?_
    exact C__eo_cons (allS__eo_cons fuel) hI2 hΓ2 (.tail _ (.tail _ (.head _))) (.tail _ (.head _)) (.head _)

theorem k_invoke_cmd_check_proven_sim (fuel : Nat) (hI : Inv sem σ)
    (s : KState) {p : Id} (hs : s.valid σ) (hp : p < σ.size) :
    SimR stateRep sem σ (k_invoke_cmd_check_proven fuel s p)
      (__eo_invoke_cmd_check_proven (s.dec σ) (σ.decode p)) := by
  unfold k_invoke_cmd_check_proven
  match hb : s.objs.back? with
  | some (.proven F) =>
    have e := KState.back_view hb
    obtain ⟨hS, hF⟩ := KState.valid_push_inv (e ▸ hs)
    rw [show s.dec σ = _ from congrArg (KState.dec σ) e, KState.dec_push]
    simp only [KStateObj.dec]
    generalize ({ s with objs := s.objs.pop } : KState) = S at hS ⊢
    have hΓ := Ctx.arg hp (Ctx.arg (show F < σ.size from hF)
      (Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.nil σ)))
    rw [__eo_invoke_cmd_check_proven.eq_1]
    refine SimR.step hΓ (simR_of (C__eo_eq (allS__eo_eq fuel) hI hΓ (.tail _ (.head _)) (.head _)))
      fun e σ1 hI1 hΓ1 => ?_
    have he := hΓ1.term (.head _)
    have hF1 := hΓ1.term (.tail _ (.tail _ (.head _)))
    have hS1 := Ctx.state hΓ1 (.tail _ (.tail _ (.tail _ (.head _))))
    have := k_push_check_sim (mk := .proven) (lmk := .proven) (fun _ _ => rfl) (fun _ => rfl)
      __eo_push_proven_check.eq_1 (fun b F S h => by rw [__eo_push_proven_check.eq_2]; exact h)
      hI1 hF1.1 hS1.1 (b := e)
    rw [he.2, hF1.2, hS1.2] at this
    exact this
  | some (.assume F) =>
    rw [KState.back_view hb, KState.dec_push]
    simp only [KStateObj.dec]
    rw [__eo_invoke_cmd_check_proven.eq_2]; kside
    exact SimR.pure hI (KState.valid_Stuck σ) rfl
  | some (.assume_push F) =>
    rw [KState.back_view hb, KState.dec_push]
    simp only [KStateObj.dec]
    rw [__eo_invoke_cmd_check_proven.eq_2]; kside
    exact SimR.pure hI (KState.valid_Stuck σ) rfl
  | none =>
    have hz : s.objs.size = 0 := by simp [Array.back?_eq_getElem?] at hb; omega
    have h0 : s.objs.toList.reverse = [] := by simp [Array.size_eq_zero_iff.mp hz]
    simp only [KState.dec, h0, KState.decL]
    rw [__eo_invoke_cmd_check_proven.eq_2] <;> (try split) <;> (try simp) <;>
      exact SimR.pure hI (KState.valid_Stuck σ) rfl

/-! ## Call lemmas, for the generated dispatch -/
theorem C_state_proven_nth (hI : Inv sem σ) (hΓ : Ctx σ Γ) {S : KState} {S' : CState}
    (hS : Fact.state S S' ∈ Γ) (n : Int) :
    Sim sem σ (k_state_proven_nth S n) (__eo_state_proven_nth S' n) :=
  (k_state_proven_nth_sim hI S n (Ctx.state hΓ hS).1).congr (by rw [(Ctx.state hΓ hS).2])

theorem C_mk_premise_list (fuel : Nat) (hI : Inv sem σ) (hΓ : Ctx σ Γ) {f : Id} {F : Term}
    (hf : Fact.term f F ∈ Γ) {S : KState} {S' : CState} (hS : Fact.state S S' ∈ Γ)
    (pl : CIndexList) :
    Sim sem σ (k_mk_premise_list fuel f pl S) (__eo_mk_premise_list F pl S') :=
  (k_mk_premise_list_sim fuel pl hI (hΓ.valid hf) (Ctx.state hΓ hS).1).congr
    (by rw [hΓ.dec hf, (Ctx.state hΓ hS).2])

end Kairos.Checker
