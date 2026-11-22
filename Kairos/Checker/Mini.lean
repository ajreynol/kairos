/-
The checker for CpcMini: Kairos versions of Logos's checker functions, and
the proofs that they compute them.

Everything here but the rule dispatch (`k_cmd_step_proven`,
`k_cmd_step_pop_proven`) mirrors lean-meta's checker template, which is the
same for every signature. The dispatch depends on the rules; it is written by
hand here as the golden output for generating it. None of these functions
needs fuel of its own: each recurses structurally on a checker list, and
calls generated programs, which are proven at every fuel (`Gen.spec`).
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
  refine SimR.step hΓ (simR_of ((spec fuel).s__eo_is_bool_type hI hF)) fun b σ1 hI1 hΓ1 => ?_
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
    exact C__eo_nil (spec fuel) hI1 hΓ1 (.tail _ (.head _)) (.head _)
  | .cons n pl, σ, S, hI, hf, hS => by
    have hΓ := Ctx.arg hf (Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.nil σ))
    simp only [k_mk_premise_list]
    rw [__eo_mk_premise_list.eq_2]
    refine Sim.step hΓ (k_state_proven_nth_sim hI S n hS) fun x σ1 hI1 hΓ1 => ?_
    have hS1 := Ctx.state hΓ1 (.tail _ (.tail _ (.head _)))
    have hf1 := hΓ1.term (.tail _ (.head _))
    refine Sim.step hΓ1 ((k_mk_premise_list_sim fuel pl hI1 hf1.1 hS1.1).congr
      (by rw [hf1.2, hS1.2])) fun r σ2 hI2 hΓ2 => ?_
    exact C__eo_cons (spec fuel) hI2 hΓ2 (.tail _ (.tail _ (.head _))) (.tail _ (.head _)) (.head _)

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
    refine SimR.step hΓ (simR_of (C__eo_eq (spec fuel) hI hΓ (.tail _ (.head _)) (.head _)))
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

/-! ## The rule dispatch (CpcMini's rules; to be generated) -/

def k_cmd_step_proven (fuel : Nat) (S : KState) : CRule → KArgList → CIndexList → K Id
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

theorem k_cmd_step_proven_sim (fuel : Nat) (hI : Inv sem σ) {S : KState} (hS : S.valid σ)
    (r : CRule) {args : KArgList} (hargs : args.valid σ) (prems : CIndexList) :
    Sim sem σ (k_cmd_step_proven fuel S r args prems)
      (__eo_cmd_step_proven (S.dec σ) r (args.dec σ) prems) := by
  have hΓ := Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.stuck hI)
  unfold k_cmd_step_proven
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

def k_cmd_step_pop_proven (fuel : Nat) (S : KState) : CRule → KArgList → Id → CIndexList → K Id
  | .scope, .nil, A, .cons n1 .nil => do
    let p1 ← k_state_proven_nth S n1
    k__eo_prog_scope fuel A p1
  | _, _, _, _ => pure 0

theorem k_cmd_step_pop_proven_sim (fuel : Nat) (hI : Inv sem σ) {S : KState} (hS : S.valid σ)
    (r : CRule) {args : KArgList} (hargs : args.valid σ) {A : Id} (hA : A < σ.size)
    (prems : CIndexList) :
    Sim sem σ (k_cmd_step_pop_proven fuel S r args A prems)
      (__eo_cmd_step_pop_proven (S.dec σ) r (args.dec σ) (σ.decode A) prems) := by
  have hΓ := Ctx.arg hA (Ctx.cons (f := Fact.state S (S.dec σ)) ⟨hS, rfl⟩ (Ctx.stuck hI))
  unfold k_cmd_step_pop_proven
  split
  · rw [KArgList.dec, __eo_cmd_step_pop_proven.eq_1]
    refine Sim.step hΓ (k_state_proven_nth_sim hI S _ hS) fun p1 σ1 hI1 hΓ1 => ?_
    exact C__eo_prog_scope (spec fuel) hI1 hΓ1 (.tail _ (.head _)) (.head _)
  · rw [__eo_cmd_step_pop_proven.eq_2]
    · exact Sim.stuck hI
    all_goals (intros; simp_all)

/-! ## Commands -/

def k_invoke_cmd_step_pop (fuel : Nat) (s : KState) :
    KState → CRule → KArgList → CIndexList → K KState
  | .cons (.assume_push A) s2, r, args, prems => do
    let t ← k_cmd_step_pop_proven fuel s r args A prems
    k_push_proven fuel t s2
  | .cons _ s2, r, args, prems => k_invoke_cmd_step_pop fuel s s2 r args prems
  | _, _, _, _ => pure .Stuck

theorem k_invoke_cmd_step_pop_sim (fuel : Nat) (hI : Inv sem σ) {s : KState} (hs : s.valid σ)
    (r : CRule) {args : KArgList} (hargs : args.valid σ) (prems : CIndexList) :
    ∀ s2 : KState, s2.valid σ →
      SimR stateRep sem σ (k_invoke_cmd_step_pop fuel s s2 r args prems)
        (__eo_invoke_cmd_step_pop (s.dec σ) (s2.dec σ) r (args.dec σ) prems)
  | .cons (.assume_push A) s2, ⟨hA, hs2⟩ => by
    have hΓ := Ctx.cons (f := Fact.state s2 (s2.dec σ)) ⟨hs2, rfl⟩ (Ctx.nil σ)
    simp only [k_invoke_cmd_step_pop, KState.dec, KStateObj.dec]
    rw [__eo_invoke_cmd_step_pop.eq_1]
    refine SimR.step hΓ (simR_of (k_cmd_step_pop_proven_sim fuel hI hs r hargs hA prems))
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

/-- `__eo_and (__eo_is_bool_type F) (__eo_is_closed F)`, the guard of an
assumption. -/
def k_assume_guard (fuel : Nat) (F : Id) : K Id := do
  let b ← k__eo_is_bool_type fuel F
  let c ← k__eo_is_closed fuel F
  k__eo_and fuel b c

theorem k_assume_guard_sim (fuel : Nat) (hI : Inv sem σ) {F : Id} (hF : F < σ.size) :
    Sim sem σ (k_assume_guard fuel F)
      (__eo_and (__eo_is_bool_type (σ.decode F)) (__eo_is_closed (σ.decode F))) := by
  have hΓ := Ctx.arg hF (Ctx.nil σ)
  refine Sim.step hΓ ((spec fuel).s__eo_is_bool_type hI hF) fun b σ1 hI1 hΓ1 => ?_
  refine Sim.step hΓ1 (C__eo_is_closed (spec fuel) hI1 hΓ1 (.tail _ (.head _)))
    fun c σ2 hI2 hΓ2 => ?_
  exact C__eo_and (spec fuel) hI2 hΓ2 (.tail _ (.head _)) (.head _)

def k_invoke_cmd (fuel : Nat) : KState → KCmd → K KState
  | .Stuck, _ => pure .Stuck
  | S, .assume_push F => do
    let a ← k_assume_guard fuel F
    k_push_check .assume_push a F S
  | S, .check_proven F => k_invoke_cmd_check_proven fuel S F
  | S, .step r args prems => do
    let t ← k_cmd_step_proven fuel S r args prems
    k_push_proven fuel t S
  | S, .step_pop r args prems => k_invoke_cmd_step_pop fuel S S r args prems

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
        refine SimR.step hΓ (simR_of (k_cmd_step_proven_sim fuel hI hS r hargs prems))
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

def k_invoke_cmd_list (fuel : Nat) : KState → KCmdList → K KState
  | S, .nil => pure S
  | S, .cons c cs => do
    let S' ← k_invoke_cmd fuel S c
    k_invoke_cmd_list fuel S' cs

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

/-! ## Refutations -/

def k_state_is_refutation (fuel : Nat) (s : KState) : K Bool := do
  let f ← intern (.Boolean false)
  let s' ← k_invoke_cmd_check_proven fuel s f
  pure (k_state_is_closed s')

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

def k_invoke_assume_list (fuel : Nat) (S : KState) : KArgList → K KState
  | .nil => pure S
  | .cons F as => do
    let rest ← k_invoke_assume_list fuel S as
    let a ← k_assume_guard fuel F
    k_push_check .assume a F rest

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

def k_checker_is_refutation (fuel : Nat) (as : KArgList) (cs : KCmdList) : K Bool := do
  let s ← k_invoke_assume_list fuel .nil as
  let s' ← k_invoke_cmd_list fuel s cs
  k_state_is_refutation fuel s'

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
