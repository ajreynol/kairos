/-
The checker, below the rule dispatch: Kairos versions of the functions of
lean-meta's checker template that the dispatch uses, and their proofs.

The template is the same for every signature; only the rule dispatch
(`Kairos/Gen/Dispatch.lean`, generated) depends on the rules. None of these
functions needs fuel of its own: each recurses structurally on a checker
list, and calls generated programs, which are proven at every fuel
(`Gen.spec`).
-/
import Kairos.Checker.Types
import Kairos.Gen.Programs

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

/-! ## Proven formulas of a state -/

def k_state_proven_nth : KState → Int → K Id
  | .cons so s, n => if n = 0 then pure so.id else k_state_proven_nth s (native_zplus n (native_zneg 1))
  | _, _ => intern (.Boolean true)

theorem k_state_proven_nth_sim (hI : Inv sem σ) :
    ∀ (s : KState) (n : Int), s.valid σ →
      Sim sem σ (k_state_proven_nth s n) (__eo_state_proven_nth (s.dec σ) n)
  | .cons so s, n, ⟨hso, hs⟩ => by
    simp only [k_state_proven_nth, KState.dec]
    by_cases h : n = 0
    · subst h
      simp only [↓reduceIte]
      rw [__eo_state_proven_nth.eq_1]
      exact Sim.pure hI hso (by cases so <;> rfl)
    · simp only [h, ↓reduceIte]
      rw [__eo_state_proven_nth.eq_2]; kside
      exact k_state_proven_nth_sim hI s _ hs
  | .nil, n, _ => by
    simp only [k_state_proven_nth, KState.dec]
    rw [__eo_state_proven_nth.eq_3]; kside
    exact intern_leaf hI rfl
  | .Stuck, n, _ => by
    simp only [k_state_proven_nth, KState.dec]
    rw [__eo_state_proven_nth.eq_3]; kside
    exact intern_leaf hI rfl

def k_state_is_closed : KState → Bool
  | .cons (.assume_push _) _ => false
  | .cons _ s => k_state_is_closed s
  | .nil => true
  | .Stuck => false

theorem k_state_is_closed_eq : ∀ s : KState, k_state_is_closed s = __eo_state_is_closed (s.dec σ)
  | .cons (.assume_push F) s => by simp [k_state_is_closed, KState.dec, KStateObj.dec, __eo_state_is_closed]
  | .cons (.assume F) s => by
    simp only [k_state_is_closed, KState.dec, KStateObj.dec]
    rw [__eo_state_is_closed.eq_2]; kside
    exact k_state_is_closed_eq s
  | .cons (.proven F) s => by
    simp only [k_state_is_closed, KState.dec, KStateObj.dec]
    rw [__eo_state_is_closed.eq_2]; kside
    exact k_state_is_closed_eq s
  | .nil => by simp [k_state_is_closed, KState.dec, __eo_state_is_closed]
  | .Stuck => by
    simp only [k_state_is_closed, KState.dec]
    rw [__eo_state_is_closed.eq_4]; kside

/-! ## Pushing onto a state -/

/-- `(Boolean true), F, s => cons (mk F) s | _ => Stuck`, the shape of the three
`__eo_push_*_check` functions. -/
@[inline] def k_push_check (mk : Id → KStateObj) (b F : Id) (s : KState) : K KState :=
  withStore fun σ => pure (if σ.view b = .Boolean true then .cons (mk F) s else .Stuck)

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
    refine SimR.pure hI ⟨by simp [KStateObj.valid, hid, hF], hs⟩ ?_
    show KState.dec σ (.cons (mk F) s) = _
    simp [KState.dec, hmk, Node.toTerm, g1]
  · simp only [hv, ↓reduceIte]
    refine SimR.pure hI trivial ?_
    show KState.dec σ .Stuck = _
    rw [g2]
    · rfl
    · exact fun e => hv (decode_boolean_inv hI e)

def k_push_proven (fuel : Nat) (F : Id) (s : KState) : K KState := do
  let b ← k__eo_is_bool_type fuel F
  k_push_check .proven b F s

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

/-! ## Premise lists -/

def k_mk_premise_list (fuel : Nat) (f : Id) : CIndexList → KState → K Id
  | .nil, _ => do
    let b ← intern .Bool
    k__eo_nil fuel f b
  | .cons n pl, S => do
    let x ← k_state_proven_nth S n
    let r ← k_mk_premise_list fuel f pl S
    k__eo_cons fuel f x r

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

/-! ## Checking what a step proves -/

def k_invoke_cmd_check_proven (fuel : Nat) : KState → Id → K KState
  | .cons (.proven F) S, p => do
    let e ← k__eo_eq fuel F p
    k_push_check .proven e F S
  | _, _ => pure .Stuck

theorem k_invoke_cmd_check_proven_sim (fuel : Nat) (hI : Inv sem σ) :
    ∀ (s : KState) {p : Id}, s.valid σ → p < σ.size →
      SimR stateRep sem σ (k_invoke_cmd_check_proven fuel s p)
        (__eo_invoke_cmd_check_proven (s.dec σ) (σ.decode p))
  | .cons (.proven F) S, p, ⟨hF, hS⟩, hp => by
    have hΓ := Ctx.arg hp (Ctx.arg hF (Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.nil σ)))
    simp only [k_invoke_cmd_check_proven, KState.dec, KStateObj.dec]
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
  | .cons (.assume F) S, p, _, _ => by
    simp only [k_invoke_cmd_check_proven, KState.dec, KStateObj.dec]
    rw [__eo_invoke_cmd_check_proven.eq_2]; kside
    exact SimR.pure hI trivial rfl
  | .cons (.assume_push F) S, p, _, _ => by
    simp only [k_invoke_cmd_check_proven, KState.dec, KStateObj.dec]
    rw [__eo_invoke_cmd_check_proven.eq_2]; kside
    exact SimR.pure hI trivial rfl
  | .nil, p, _, _ => by
    simp only [k_invoke_cmd_check_proven, KState.dec]
    rw [__eo_invoke_cmd_check_proven.eq_2]; kside
    exact SimR.pure hI trivial rfl
  | .Stuck, p, _, _ => by
    simp only [k_invoke_cmd_check_proven, KState.dec]
    rw [__eo_invoke_cmd_check_proven.eq_2]; kside
    exact SimR.pure hI trivial rfl

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
