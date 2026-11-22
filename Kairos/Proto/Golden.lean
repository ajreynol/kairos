/-
Golden output for kairos-eoc (milestone 2b): four CpcMini programs written by
hand exactly as the generator will print them. These are `__eo_requires`
(natives, nested `native_ite`), `__eo_eq` (stuck guards), `__eo_and` (native
payload patterns, a call), and `__eo_is_closed_rec` (cached, recursive, `Var`
and list patterns, `__eo_ite`, a call into `__eo_eq`).

Conventions the generator follows:
* every program takes fuel first; all calls pass the predecessor;
* case `k` has a matcher `m_<f>_<k>` over all arguments, returning the ids and
  natives bound inside constructor patterns, with a `_some` lemma (decoded
  shapes, validity) and a `_none` lemma (the case does not match);
* the proof context `Γ` lists facts newest first: bound ids, arguments, then
  `Stuck`; membership is proven by position;
* a case's Logos side is `rw [<shapes>, f.eq_k]`, then `kside` for the
  equation's hypotheses.
-/
import Kairos.Runtime.Prog

set_option linter.unusedVariables false

namespace Kairos.Golden
open Eo Kairos Store SmtEval

/-- Cached programs, by id, with their Logos meaning. -/
def sem : Sem
  | 0, [a, b] => some (__eo_is_closed_rec a b)
  | _, _ => none

/-- Discharge the hypotheses `rw [f.eq_k]` leaves, and only those. -/
macro "kside" : tactic => `(tactic| all_goals try (kdis; done))

/-! ## Matchers -/

-- __eo_eq
def m__eo_eq_1 (σ : Store) (x1 x2 : Id) : Option Unit := Store.stuck x1 (some ())
def m__eo_eq_2 (σ : Store) (x1 x2 : Id) : Option Unit := Store.stuck x2 (some ())

theorem m__eo_eq_1_some {σ : Store} (hI : Inv sem σ) {x1 x2 : Id}
    (h : m__eo_eq_1 σ x1 x2 = some ()) : σ.decode x1 = .Stuck := by
  obtain ⟨e, -⟩ := stuck_some h; subst e; exact decode_zero hI

theorem m__eo_eq_1_none {σ : Store} (hI : Inv sem σ) {x1 x2 : Id} (h1 : x1 < σ.size)
    (h : m__eo_eq_1 σ x1 x2 = none) : σ.decode x1 = .Stuck → False := by
  intro e; have := decode_stuck_inv hI h1 e; subst this
  simp [m__eo_eq_1, stuck_of_zero] at h

theorem m__eo_eq_2_some {σ : Store} (hI : Inv sem σ) {x1 x2 : Id}
    (h : m__eo_eq_2 σ x1 x2 = some ()) : σ.decode x2 = .Stuck := by
  obtain ⟨e, -⟩ := stuck_some h; subst e; exact decode_zero hI

theorem m__eo_eq_2_none {σ : Store} (hI : Inv sem σ) {x1 x2 : Id} (h2 : x2 < σ.size)
    (h : m__eo_eq_2 σ x1 x2 = none) : σ.decode x2 = .Stuck → False := by
  intro e; have := decode_stuck_inv hI h2 e; subst this
  simp [m__eo_eq_2, stuck_of_zero] at h

-- __eo_and
def m__eo_and_1 (σ : Store) (x1 x2 : Id) : Option (Bool × Bool) :=
  σ.boolean x1 fun b1 => σ.boolean x2 fun b2 => some (b1, b2)

def m__eo_and_2 (σ : Store) (x1 x2 : Id) : Option (Int × Int × Int × Int) :=
  σ.binary x1 fun w1 n1 => σ.binary x2 fun w2 n2 => some (w1, n1, w2, n2)

theorem m__eo_and_1_some {σ : Store} (hI : Inv sem σ) {x1 x2 : Id} {b1 b2 : Bool}
    (h : m__eo_and_1 σ x1 x2 = some (b1, b2)) :
    σ.decode x1 = .Boolean b1 ∧ σ.decode x2 = .Boolean b2 := by
  unfold m__eo_and_1 at h
  obtain ⟨_b1, v0, h⟩ := boolean_some h
  obtain ⟨_b2, v1, h⟩ := boolean_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨decode_of_view hI v0, decode_of_view hI v1⟩

theorem m__eo_and_1_none {σ : Store} (hI : Inv sem σ) {x1 x2 : Id}
    (h : m__eo_and_1 σ x1 x2 = none) :
    ∀ b1 b2, σ.decode x1 = .Boolean b1 → σ.decode x2 = .Boolean b2 → False := by
  intro b1 b2 e0 e1
  have v0 := decode_boolean_inv hI e0
  have v1 := decode_boolean_inv hI e1
  simp [m__eo_and_1, boolean_of_view v0, boolean_of_view v1] at h

theorem m__eo_and_2_some {σ : Store} (hI : Inv sem σ) {x1 x2 : Id} {w1 n1 w2 n2 : Int}
    (h : m__eo_and_2 σ x1 x2 = some (w1, n1, w2, n2)) :
    σ.decode x1 = .Binary w1 n1 ∧ σ.decode x2 = .Binary w2 n2 := by
  unfold m__eo_and_2 at h
  obtain ⟨_w1, _n1, v0, h⟩ := binary_some h
  obtain ⟨_w2, _n2, v1, h⟩ := binary_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  exact ⟨decode_of_view hI v0, decode_of_view hI v1⟩

theorem m__eo_and_2_none {σ : Store} (hI : Inv sem σ) {x1 x2 : Id}
    (h : m__eo_and_2 σ x1 x2 = none) :
    ∀ w1 n1 w2 n2, σ.decode x1 = .Binary w1 n1 → σ.decode x2 = .Binary w2 n2 → False := by
  intro w1 n1 w2 n2 e0 e1
  have v0 := decode_binary_inv hI e0
  have v1 := decode_binary_inv hI e1
  simp [m__eo_and_2, binary_of_view v0, binary_of_view v1] at h

-- __eo_is_closed_rec
def m__eo_is_closed_rec_1 (σ : Store) (x1 x2 : Id) : Option Unit := Store.stuck x1 (some ())
def m__eo_is_closed_rec_2 (σ : Store) (x1 x2 : Id) : Option Unit := Store.stuck x2 (some ())

def m__eo_is_closed_rec_3 (σ : Store) (x1 x2 : Id) : Option (Id × Id) :=
  σ.var x1 fun s T => σ.leaf x2 .listNil (some (s, T))

def m__eo_is_closed_rec_4 (σ : Store) (x1 x2 : Id) : Option (Id × Id × Id × Id) :=
  σ.var x1 fun s T => σ.app x2 fun p0 vs => σ.app p0 fun p1 x => σ.leaf p1 .listCons
    (some (s, T, x, vs))

def m__eo_is_closed_rec_5 (σ : Store) (x1 x2 : Id) : Option (Id × Id) :=
  σ.app x1 fun f x => some (f, x)

theorem m__eo_is_closed_rec_1_some {σ : Store} (hI : Inv sem σ) {x1 x2 : Id}
    (h : m__eo_is_closed_rec_1 σ x1 x2 = some ()) : σ.decode x1 = .Stuck := by
  obtain ⟨e, -⟩ := stuck_some h; subst e; exact decode_zero hI

theorem m__eo_is_closed_rec_1_none {σ : Store} (hI : Inv sem σ) {x1 x2 : Id} (h1 : x1 < σ.size)
    (h : m__eo_is_closed_rec_1 σ x1 x2 = none) : σ.decode x1 = .Stuck → False := by
  intro e; have := decode_stuck_inv hI h1 e; subst this
  simp [m__eo_is_closed_rec_1, stuck_of_zero] at h

theorem m__eo_is_closed_rec_2_some {σ : Store} (hI : Inv sem σ) {x1 x2 : Id}
    (h : m__eo_is_closed_rec_2 σ x1 x2 = some ()) : σ.decode x2 = .Stuck := by
  obtain ⟨e, -⟩ := stuck_some h; subst e; exact decode_zero hI

theorem m__eo_is_closed_rec_2_none {σ : Store} (hI : Inv sem σ) {x1 x2 : Id} (h2 : x2 < σ.size)
    (h : m__eo_is_closed_rec_2 σ x1 x2 = none) : σ.decode x2 = .Stuck → False := by
  intro e; have := decode_stuck_inv hI h2 e; subst this
  simp [m__eo_is_closed_rec_2, stuck_of_zero] at h

theorem m__eo_is_closed_rec_3_some {σ : Store} (hI : Inv sem σ) {x1 x2 s T : Id}
    (h1 : x1 < σ.size) (h2 : x2 < σ.size)
    (h : m__eo_is_closed_rec_3 σ x1 x2 = some (s, T)) :
    s < σ.size ∧ T < σ.size ∧
      σ.decode x1 = .Var (σ.decode s) (σ.decode T) ∧ σ.decode x2 = .__eo_List_nil := by
  unfold m__eo_is_closed_rec_3 at h
  obtain ⟨_s, _T, v0, h⟩ := var_some h
  obtain ⟨v1, h⟩ := leaf_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨valid_of_view hI h1 v0 (by simp [Node.children]),
    valid_of_view hI h1 v0 (by simp [Node.children]),
    decode_of_view hI v0, decode_of_view hI v1⟩

theorem m__eo_is_closed_rec_3_none {σ : Store} (hI : Inv sem σ) {x1 x2 : Id}
    (h : m__eo_is_closed_rec_3 σ x1 x2 = none) :
    ∀ s T, σ.decode x1 = .Var s T → σ.decode x2 = .__eo_List_nil → False := by
  intro s T e0 e1
  obtain ⟨_s, _T, v0, -, -⟩ := decode_var_inv hI e0
  have v1 := decode_leaf_inv (n := .listNil) (d := σ.decode) hI rfl e1
  simp [m__eo_is_closed_rec_3, var_of_view v0, leaf_of_view v1] at h

theorem m__eo_is_closed_rec_4_some {σ : Store} (hI : Inv sem σ) {x1 x2 s T x vs : Id}
    (h1 : x1 < σ.size) (h2 : x2 < σ.size)
    (h : m__eo_is_closed_rec_4 σ x1 x2 = some (s, T, x, vs)) :
    s < σ.size ∧ T < σ.size ∧ x < σ.size ∧ vs < σ.size ∧
      σ.decode x1 = .Var (σ.decode s) (σ.decode T) ∧
      σ.decode x2 = .Apply (.Apply .__eo_List_cons (σ.decode x)) (σ.decode vs) := by
  unfold m__eo_is_closed_rec_4 at h
  obtain ⟨_s, _T, v0, h⟩ := var_some h
  obtain ⟨p0, _vs, v1, h⟩ := app_some h
  obtain ⟨w0, w1⟩ := valid_of_app hI h2 v1
  obtain ⟨p1, _x, v2, h⟩ := app_some h
  obtain ⟨w2, w3⟩ := valid_of_app hI w0 v2
  obtain ⟨v3, h⟩ := leaf_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  refine ⟨valid_of_view hI h1 v0 (by simp [Node.children]),
    valid_of_view hI h1 v0 (by simp [Node.children]), w3, w1, decode_of_view hI v0, ?_⟩
  simp only [decode_of_view hI v1, decode_of_view hI v2, decode_of_view hI v3, Node.toTerm]

theorem m__eo_is_closed_rec_4_none {σ : Store} (hI : Inv sem σ) {x1 x2 : Id}
    (h : m__eo_is_closed_rec_4 σ x1 x2 = none) :
    ∀ s T x vs, σ.decode x1 = .Var s T →
      σ.decode x2 = .Apply (.Apply .__eo_List_cons x) vs → False := by
  intro s T x vs e0 e1
  obtain ⟨_s, _T, v0, -, -⟩ := decode_var_inv hI e0
  obtain ⟨p0, _vs, v1, e2, -⟩ := decode_apply_inv hI e1
  obtain ⟨p1, _x, v2, e3, -⟩ := decode_apply_inv hI e2
  have v3 := decode_leaf_inv (n := .listCons) (d := σ.decode) hI rfl e3
  simp [m__eo_is_closed_rec_4, var_of_view v0, app_of_view v1, app_of_view v2,
    leaf_of_view v3] at h

theorem m__eo_is_closed_rec_5_some {σ : Store} (hI : Inv sem σ) {x1 x2 f x : Id}
    (h1 : x1 < σ.size) (h2 : x2 < σ.size)
    (h : m__eo_is_closed_rec_5 σ x1 x2 = some (f, x)) :
    f < σ.size ∧ x < σ.size ∧ σ.decode x1 = .Apply (σ.decode f) (σ.decode x) := by
  unfold m__eo_is_closed_rec_5 at h
  obtain ⟨_f, _x, v0, h⟩ := app_some h
  obtain ⟨w0, w1⟩ := valid_of_app hI h1 v0
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨w0, w1, decode_of_view hI v0⟩

theorem m__eo_is_closed_rec_5_none {σ : Store} (hI : Inv sem σ) {x1 x2 : Id}
    (h : m__eo_is_closed_rec_5 σ x1 x2 = none) :
    ∀ f x, σ.decode x1 = .Apply f x → False := by
  intro f x e0
  obtain ⟨_f, _x, v0, -, -⟩ := decode_apply_inv hI e0
  simp [m__eo_is_closed_rec_5, app_of_view v0] at h

/-! ## Programs -/

mutual

def k__eo_requires : Nat → Id → Id → Id → K Id
  | 0, _, _, _ => throw .fuel
  | n + 1, x1, x2, x3 =>
    if knative_teq x1 x2 then
      (if native_not (knative_teq x1 0) then pure x3 else pure 0)
    else pure 0

def k__eo_eq : Nat → Id → Id → K Id
  | 0, _, _ => throw .fuel
  | n + 1, x1, x2 => withStore fun σ =>
    match m__eo_eq_1 σ x1 x2 with
    | some () => pure 0
    | none =>
    match m__eo_eq_2 σ x1 x2 with
    | some () => pure 0
    | none =>
    intern (.boolean (knative_teq x2 x1))

def k__eo_and : Nat → Id → Id → K Id
  | 0, _, _ => throw .fuel
  | n + 1, x1, x2 => withStore fun σ =>
    match m__eo_and_1 σ x1 x2 with
    | some (b1, b2) => intern (.boolean (native_and b1 b2))
    | none =>
    match m__eo_and_2 σ x1 x2 with
    | some (w1, n1, w2, n2) => do
      let _t0 ← intern (.numeral w1)
      let _t1 ← intern (.numeral w2)
      let _t2 ← intern (.binary w1 (native_mod_total (native_binary_and w1 n1 n2) (native_int_pow2 w1)))
      k__eo_requires n _t0 _t1 _t2
    | none => pure 0

def k__eo_is_closed_rec : Nat → Id → Id → K Id
  | 0, _, _ => throw .fuel
  | n + 1, x1, x2 => cached 0 [x1, x2] <| withStore fun σ =>
    match m__eo_is_closed_rec_1 σ x1 x2 with
    | some () => pure 0
    | none =>
    match m__eo_is_closed_rec_2 σ x1 x2 with
    | some () => pure 0
    | none =>
    match m__eo_is_closed_rec_3 σ x1 x2 with
    | some (s, T) => intern (.boolean false)
    | none =>
    match m__eo_is_closed_rec_4 σ x1 x2 with
    | some (s, T, x, vs) => do
      let _t0 ← intern (.var s T)
      let _t1 ← k__eo_eq n _t0 x
      k_ite _t1 (intern (.boolean true)) (k__eo_is_closed_rec n _t0 vs)
    | none =>
    match m__eo_is_closed_rec_5 σ x1 x2 with
    | some (f, x) => do
      let _t0 ← k__eo_is_closed_rec n f x2
      let _t1 ← k__eo_is_closed_rec n x x2
      k__eo_and n _t0 _t1
    | none =>
    intern (.boolean true)

end

/-! ## Specs -/

abbrev S__eo_requires (n : Nat) : Prop :=
  ∀ {σ : Store} {x1 x2 x3 : Id}, Inv sem σ → x1 < σ.size → x2 < σ.size → x3 < σ.size →
    Sim sem σ (k__eo_requires n x1 x2 x3)
      (__eo_requires (σ.decode x1) (σ.decode x2) (σ.decode x3))

abbrev S__eo_eq (n : Nat) : Prop :=
  ∀ {σ : Store} {x1 x2 : Id}, Inv sem σ → x1 < σ.size → x2 < σ.size →
    Sim sem σ (k__eo_eq n x1 x2) (__eo_eq (σ.decode x1) (σ.decode x2))

abbrev S__eo_and (n : Nat) : Prop :=
  ∀ {σ : Store} {x1 x2 : Id}, Inv sem σ → x1 < σ.size → x2 < σ.size →
    Sim sem σ (k__eo_and n x1 x2) (__eo_and (σ.decode x1) (σ.decode x2))

abbrev S__eo_is_closed_rec (n : Nat) : Prop :=
  ∀ {σ : Store} {x1 x2 : Id}, Inv sem σ → x1 < σ.size → x2 < σ.size →
    Sim sem σ (k__eo_is_closed_rec n x1 x2) (__eo_is_closed_rec (σ.decode x1) (σ.decode x2))

structure Spec (n : Nat) : Prop where
  eo_requires : S__eo_requires n
  eo_eq : S__eo_eq n
  eo_and : S__eo_and n
  eo_is_closed_rec : S__eo_is_closed_rec n

/-! ## Steps: fuel `n + 1` from fuel `n` -/

theorem step__eo_requires {n : Nat} (ih : Spec n) : S__eo_requires (n + 1) := by
  intro σ x1 x2 x3 hI h1 h2 h3
  have hΓ := Ctx.arg h3 (Ctx.arg h2 (Ctx.arg h1 (Ctx.stuck hI)))
  simp only [k__eo_requires]
  rw [__eo_requires.eq_1]
  rw [knative_teq_ctx hI hΓ (.tail _ (.tail _ (.head _))) (.tail _ (.head _)),
    knative_teq_ctx hI hΓ (.tail _ (.tail _ (.head _))) (.tail _ (.tail _ (.tail _ (.head _))))]
  apply Sim.nite
  · intro _
    apply Sim.nite
    · intro _; exact Sim.ret hI hΓ (.head _)
    · intro _; exact Sim.ret hI hΓ (.tail _ (.tail _ (.tail _ (.head _))))
  · intro _; exact Sim.ret hI hΓ (.tail _ (.tail _ (.tail _ (.head _))))

theorem step__eo_eq {n : Nat} (ih : Spec n) : S__eo_eq (n + 1) := by
  intro σ x1 x2 hI h1 h2
  have hΓ := Ctx.arg h2 (Ctx.arg h1 (Ctx.stuck hI))
  simp only [k__eo_eq]
  apply Sim.withStore
  cases hm1 : m__eo_eq_1 σ x1 x2 with
  | some v =>
    have d1 := m__eo_eq_1_some hI hm1
    dsimp only
    rw [d1, __eo_eq.eq_1]; kside
    exact Sim.stuck hI
  | none =>
  have n1 := m__eo_eq_1_none hI h1 hm1
  dsimp only
  cases hm2 : m__eo_eq_2 σ x1 x2 with
  | some v =>
    have d2 := m__eo_eq_2_some hI hm2
    dsimp only
    rw [d2, __eo_eq.eq_2]; kside
    exact Sim.stuck hI
  | none =>
  have n2 := m__eo_eq_2_none hI h2 hm2
  dsimp only
  rw [__eo_eq.eq_3]; kside
  rw [knative_teq_ctx hI hΓ (.head _) (.tail _ (.head _))]
  exact intern_leaf hI rfl

theorem step__eo_and {n : Nat} (ih : Spec n) : S__eo_and (n + 1) := by
  intro σ x1 x2 hI h1 h2
  have hΓ := Ctx.arg h2 (Ctx.arg h1 (Ctx.stuck hI))
  simp only [k__eo_and]
  apply Sim.withStore
  cases hm1 : m__eo_and_1 σ x1 x2 with
  | some v =>
    obtain ⟨b1, b2⟩ := v
    obtain ⟨d1, d2⟩ := m__eo_and_1_some hI hm1
    dsimp only
    rw [d1, d2, __eo_and.eq_1]; kside
    exact intern_leaf hI rfl
  | none =>
  have n1 := m__eo_and_1_none hI hm1
  dsimp only
  cases hm2 : m__eo_and_2 σ x1 x2 with
  | some v =>
    obtain ⟨w1, n1, w2, n2⟩ := v
    obtain ⟨d1, d2⟩ := m__eo_and_2_some hI hm2
    dsimp only
    rw [d1, d2, __eo_and.eq_2]; kside
    refine Sim.step hΓ (intern_leaf hI rfl) fun _t0 σ1 hI1 hΓ1 => ?_
    refine Sim.step hΓ1 (intern_leaf hI1 rfl) fun _t1 σ2 hI2 hΓ2 => ?_
    refine Sim.step hΓ2 (intern_leaf hI2 rfl) fun _t2 σ3 hI3 hΓ3 => ?_
    exact Sim.call3 ih.eo_requires hI3 hΓ3 (.tail _ (.tail _ (.head _))) (.tail _ (.head _)) (.head _)
  | none =>
  have n2 := m__eo_and_2_none hI hm2
  dsimp only
  rw [__eo_and.eq_3]; kside
  exact Sim.stuck hI

theorem step__eo_is_closed_rec {n : Nat} (ih : Spec n) : S__eo_is_closed_rec (n + 1) := by
  intro σ x1 x2 hI h1 h2
  have hΓ := Ctx.arg h2 (Ctx.arg h1 (Ctx.stuck hI))
  simp only [k__eo_is_closed_rec]
  apply cached_ctx hI (by simp [h1, h2]) (by simp [sem])
  apply Sim.withStore
  cases hm1 : m__eo_is_closed_rec_1 σ x1 x2 with
  | some v =>
    have d1 := m__eo_is_closed_rec_1_some hI hm1
    dsimp only
    rw [d1, __eo_is_closed_rec.eq_1]; kside
    exact Sim.stuck hI
  | none =>
  have n1 := m__eo_is_closed_rec_1_none hI h1 hm1
  dsimp only
  cases hm2 : m__eo_is_closed_rec_2 σ x1 x2 with
  | some v =>
    have d2 := m__eo_is_closed_rec_2_some hI hm2
    dsimp only
    rw [d2, __eo_is_closed_rec.eq_2]; kside
    exact Sim.stuck hI
  | none =>
  have n2 := m__eo_is_closed_rec_2_none hI h2 hm2
  dsimp only
  cases hm3 : m__eo_is_closed_rec_3 σ x1 x2 with
  | some v =>
    obtain ⟨s, T⟩ := v
    obtain ⟨hs, hT, d1, d2⟩ := m__eo_is_closed_rec_3_some hI h1 h2 hm3
    dsimp only
    rw [d1, d2, __eo_is_closed_rec.eq_3]; kside
    exact intern_leaf hI rfl
  | none =>
  have n3 := m__eo_is_closed_rec_3_none hI hm3
  dsimp only
  cases hm4 : m__eo_is_closed_rec_4 σ x1 x2 with
  | some v =>
    obtain ⟨s, T, x, vs⟩ := v
    obtain ⟨hs, hT, hx, hvs, d1, d2⟩ := m__eo_is_closed_rec_4_some hI h1 h2 hm4
    have hΓ := Ctx.arg hvs (Ctx.arg hx (Ctx.arg hT (Ctx.arg hs hΓ)))
    dsimp only
    rw [d1, d2, __eo_is_closed_rec.eq_4]; kside
    -- Γ: vs, x, T, s, x2, x1, Stuck
    refine Sim.step hΓ (intern_var hI hΓ (.tail _ (.tail _ (.tail _ (.head _))))
      (.tail _ (.tail _ (.head _)))) fun _t0 σ1 hI1 hΓ1 => ?_
    -- Γ1: _t0, vs, x, T, s, ...
    refine Sim.step hΓ1 (Sim.call2 ih.eo_eq hI1 hΓ1 (.head _) (.tail _ (.tail _ (.head _))))
      fun _t1 σ2 hI2 hΓ2 => ?_
    -- Γ2: _t1, _t0, vs, ...
    exact k_ite_sim hI2 hΓ2 (.head _) (intern_leaf hI2 rfl)
      (Sim.call2 ih.eo_is_closed_rec hI2 hΓ2 (.tail _ (.head _)) (.tail _ (.tail _ (.head _))))
  | none =>
  have n4 := m__eo_is_closed_rec_4_none hI hm4
  dsimp only
  cases hm5 : m__eo_is_closed_rec_5 σ x1 x2 with
  | some v =>
    obtain ⟨f, x⟩ := v
    obtain ⟨hf, hx, d1⟩ := m__eo_is_closed_rec_5_some hI h1 h2 hm5
    have hΓ := Ctx.arg hx (Ctx.arg hf hΓ)
    dsimp only
    rw [d1, __eo_is_closed_rec.eq_5]; kside
    -- Γ: x, f, x2, x1, Stuck
    refine Sim.step hΓ (Sim.call2 ih.eo_is_closed_rec hI hΓ (.tail _ (.head _))
      (.tail _ (.tail _ (.head _)))) fun _t0 σ1 hI1 hΓ1 => ?_
    refine Sim.step hΓ1 (Sim.call2 ih.eo_is_closed_rec hI1 hΓ1 (.tail _ (.head _))
      (.tail _ (.tail _ (.tail _ (.head _))))) fun _t1 σ2 hI2 hΓ2 => ?_
    exact Sim.call2 ih.eo_and hI2 hΓ2 (.tail _ (.head _)) (.head _)
  | none =>
  have n5 := m__eo_is_closed_rec_5_none hI hm5
  dsimp only
  rw [__eo_is_closed_rec.eq_6]; kside
  exact intern_leaf hI rfl

/-! ## Assembly -/

theorem spec : ∀ n, Spec n
  | 0 => {
      eo_requires := fun _ _ _ _ => by simp only [k__eo_requires]; exact Ok.throw
      eo_eq := fun _ _ _ => by simp only [k__eo_eq]; exact Ok.throw
      eo_and := fun _ _ _ => by simp only [k__eo_and]; exact Ok.throw
      eo_is_closed_rec := fun _ _ _ => by simp only [k__eo_is_closed_rec]; exact Ok.throw }
  | n + 1 =>
    have ih := spec n
    { eo_requires := step__eo_requires ih
      eo_eq := step__eo_eq ih
      eo_and := step__eo_and ih
      eo_is_closed_rec := step__eo_is_closed_rec ih }

end Kairos.Golden
