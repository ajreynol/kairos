/-
Hand-written Kairos versions of CpcMini programs with their simulation proofs
(prototype, milestone 2a). This is the shape kairos-eoc will generate.
-/
import Kairos.Runtime.Monad

namespace Kairos
open Eo Store SmtEval

variable {sem : Sem} {σ : Store}

/-! ## Inversion: what a decoded id looks like -/

theorem decode_eq_apply_iff (hI : Inv sem σ) {x : Id} (hx : x < σ.size) {A B : Term} :
    σ.decode x = .Apply A B ↔
      ∃ f y, σ.view x = .apply f y ∧ σ.decode f = A ∧ σ.decode y = B := by
  rw [decode_view hI hx]
  constructor
  · intro h
    cases hv : σ.view x <;> simp [hv, Node.toTerm] at h
    exact ⟨_, _, rfl, h.1, h.2⟩
  · rintro ⟨f, y, hv, rfl, rfl⟩; simp [hv, Node.toTerm]

theorem decode_eq_uop_iff (hI : Inv sem σ) {x : Id} (hx : x < σ.size) {o : UserOp} :
    σ.decode x = .UOp o ↔ σ.view x = .uop o := by
  rw [decode_view hI hx]
  constructor
  · intro h; cases hv : σ.view x <;> simp [hv, Node.toTerm] at h; simp [h]
  · intro hv; simp [hv, Node.toTerm]

theorem view_apply_valid (hI : Inv sem σ) {x : Id} (hx : x < σ.size) {f y : Id}
    (hv : σ.view x = .apply f y) : f < σ.size ∧ y < σ.size :=
  ⟨child_valid hI hx (by simp [hv, Node.children]),
   child_valid hI hx (by simp [hv, Node.children])⟩

theorem decode_of_view_apply (hI : Inv sem σ) {x : Id} (hx : x < σ.size) {f y : Id}
    (hv : σ.view x = .apply f y) : σ.decode x = .Apply (σ.decode f) (σ.decode y) := by
  rw [decode_view hI hx, hv]; rfl

theorem decode_of_view_uop (hI : Inv sem σ) {x : Id} (hx : x < σ.size) {o : UserOp}
    (hv : σ.view x = .uop o) : σ.decode x = .UOp o := by
  rw [decode_view hI hx, hv]; rfl

/-! ## Builders -/

def mkApply (f x : Id) : K Id := intern (.apply f x)
def mkUOp (o : UserOp) : K Id := intern (.uop o)

/-- `((o a) b)`. -/
def mkBin (o : UserOp) (a b : Id) : K Id := do
  let e ← mkUOp o
  let f ← mkApply e a
  mkApply f b

theorem mkApply_sim (hI : Inv sem σ) {f x : Id} (hf : f < σ.size) (hx : x < σ.size) :
    Sim sem σ (mkApply f x) (.Apply (σ.decode f) (σ.decode x)) :=
  intern_sim hI (by simp [Node.children, hf, hx])

theorem mkUOp_sim (hI : Inv sem σ) (o : UserOp) : Sim sem σ (mkUOp o) (.UOp o) :=
  intern_sim hI (by simp [Node.children])

theorem mkBin_sim (hI : Inv sem σ) (o : UserOp) {a b : Id} (ha : a < σ.size) (hb : b < σ.size) :
    Sim sem σ (mkBin o a b) (.Apply (.Apply (.UOp o) (σ.decode a)) (σ.decode b)) := by
  apply Sim.bind (mkUOp_sim hI o)
  intro e σ₁ h₁
  have ha₁ := Nat.lt_of_lt_of_le ha h₁.ext.size_le
  apply Sim.bind (mkApply_sim h₁.inv h₁.valid ha₁)
  intro f σ₂ h₂
  have hb₂ := Nat.lt_of_lt_of_le hb (h₁.ext.trans h₂.ext).size_le
  apply (mkApply_sim h₂.inv h₂.valid hb₂).congr
  rw [h₂.dec, h₁.dec, decode_extends (h₁.ext.trans h₂.ext) b hb,
    decode_extends h₁.ext a ha]

/-! ## Matchers -/

/-- `(o a b)`, i.e. `Apply (Apply (UOp o) a) b`. -/
def matchBin (o : UserOp) (σ : Store) (x : Id) : Option (Id × Id) :=
  match σ.view x with
  | .apply g b =>
    match σ.view g with
    | .apply e a => if σ.view e = .uop o then some (a, b) else none
    | _ => none
  | _ => none

/-- `(o a)`, i.e. `Apply (UOp o) a`. -/
def matchUn (o : UserOp) (σ : Store) (x : Id) : Option Id :=
  match σ.view x with
  | .apply e a => if σ.view e = .uop o then some a else none
  | _ => none

theorem matchBin_some (hI : Inv sem σ) {o : UserOp} {x a b : Id} (hx : x < σ.size)
    (h : matchBin o σ x = some (a, b)) :
    a < σ.size ∧ b < σ.size ∧
      σ.decode x = .Apply (.Apply (.UOp o) (σ.decode a)) (σ.decode b) := by
  unfold matchBin at h
  split at h <;> try contradiction
  rename_i g b' hv
  obtain ⟨hg, hb'⟩ := view_apply_valid hI hx hv
  split at h <;> try contradiction
  rename_i e a' hvg
  obtain ⟨he, ha'⟩ := view_apply_valid hI hg hvg
  split at h <;> try contradiction
  rename_i hve
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨ha', hb', ?_⟩
  rw [decode_of_view_apply hI hx hv, decode_of_view_apply hI hg hvg,
    decode_of_view_uop hI he hve]

theorem matchBin_none (hI : Inv sem σ) {o : UserOp} {x : Id} (hx : x < σ.size)
    (h : matchBin o σ x = none) :
    ∀ A B, σ.decode x ≠ .Apply (.Apply (.UOp o) A) B := by
  intro A B hd
  obtain ⟨g, b, hv, hg, -⟩ := (decode_eq_apply_iff hI hx).mp hd
  obtain ⟨hgv, -⟩ := view_apply_valid hI hx hv
  obtain ⟨e, a, hvg, he, -⟩ := (decode_eq_apply_iff hI hgv).mp hg
  obtain ⟨hev, -⟩ := view_apply_valid hI hgv hvg
  have hve := (decode_eq_uop_iff hI hev).mp he
  simp [matchBin, hv, hvg, hve] at h

theorem matchUn_some (hI : Inv sem σ) {o : UserOp} {x a : Id} (hx : x < σ.size)
    (h : matchUn o σ x = some a) :
    a < σ.size ∧ σ.decode x = .Apply (.UOp o) (σ.decode a) := by
  unfold matchUn at h
  split at h <;> try contradiction
  rename_i e a' hv
  obtain ⟨he, ha'⟩ := view_apply_valid hI hx hv
  split at h <;> try contradiction
  rename_i hve
  simp only [Option.some.injEq] at h; subst h
  exact ⟨ha', by rw [decode_of_view_apply hI hx hv, decode_of_view_uop hI he hve]⟩

theorem matchUn_none (hI : Inv sem σ) {o : UserOp} {x : Id} (hx : x < σ.size)
    (h : matchUn o σ x = none) :
    ∀ A, σ.decode x ≠ .Apply (.UOp o) A := by
  intro A hd
  obtain ⟨e, a, hv, he, -⟩ := (decode_eq_apply_iff hI hx).mp hd
  obtain ⟨hev, -⟩ := view_apply_valid hI hx hv
  have hve := (decode_eq_uop_iff hI hev).mp he
  simp [matchUn, hv, hve] at h

/-! ## `__mk_symm` -/

/-- Run `f` on the current store, without changing it. -/
@[inline] def withStore {α : Type} (f : Store → K α) : K α := fun σ => f σ σ

def k_mk_symm (x : Id) : K Id := withStore fun σ =>
  match matchBin .eq σ x with
  | some (t1, t2) => mkBin .eq t2 t1
  | none =>
    match matchUn .not σ x >>= matchBin .eq σ with
    | some (t1, t2) => do
      let e ← mkBin .eq t2 t1
      let n ← mkUOp .not
      mkApply n e
    | none => pure 0

theorem k_mk_symm_sim (hI : Inv sem σ) {x : Id} (hx : x < σ.size) :
    Sim sem σ (k_mk_symm x) (__mk_symm (σ.decode x)) := by
  show Sim sem σ (match matchBin .eq σ x with
    | some (t1, t2) => mkBin .eq t2 t1
    | none =>
      match matchUn .not σ x >>= matchBin .eq σ with
      | some (t1, t2) => do
        let e ← mkBin .eq t2 t1
        let n ← mkUOp .not
        mkApply n e
      | none => pure 0) _
  cases h1 : matchBin .eq σ x with
  | some p =>
    obtain ⟨t1, t2⟩ := p
    obtain ⟨h1a, h1b, hd⟩ := matchBin_some hI hx h1
    simp only
    rw [hd]
    exact (mkBin_sim hI .eq h1b h1a).congr (by simp [__mk_symm])
  | none =>
    simp only
    have hn1 := matchBin_none hI hx h1
    cases h2u : matchUn .not σ x with
    | some y =>
      obtain ⟨hy, hdy⟩ := matchUn_some hI hx h2u
      cases h2 : matchBin .eq σ y with
      | some p =>
        obtain ⟨t1, t2⟩ := p
        obtain ⟨ha, hb, hd⟩ := matchBin_some hI hy h2
        simp only [Option.bind_eq_bind, Option.bind_some, h2]
        rw [hdy, hd]
        apply Sim.bind (mkBin_sim hI .eq hb ha)
        intro e σ₁ h₁
        apply Sim.bind (mkUOp_sim h₁.inv .not)
        intro n σ₂ h₂
        apply (mkApply_sim h₂.inv h₂.valid (Nat.lt_of_lt_of_le h₁.valid h₂.ext.size_le)).congr
        rw [h₂.dec, decode_extends h₂.ext e h₁.valid, h₁.dec]
        simp [__mk_symm]
      | none =>
        have hn2 := matchBin_none hI hy h2
        simp only [Option.bind_eq_bind, Option.bind_some, h2]
        apply (Sim.pure hI (size_pos hI) (decode_zero hI)).congr
        rw [hdy]
        rw [__mk_symm.eq_def]
        split
        · rename_i heq; simp at heq
        · rename_i t1 t2 heq
          simp only [Term.Apply.injEq] at heq
          exact absurd heq.2 (hn2 t1 t2)
        · rfl
    | none =>
      have hn2 := matchUn_none hI hx h2u
      simp only [Option.bind_eq_bind, Option.bind_none]
      apply (Sim.pure hI (size_pos hI) (decode_zero hI)).congr
      rw [__mk_symm.eq_def]
      split
      · rename_i t1 t2 heq; exact absurd heq (hn1 _ _)
      · rename_i t1 t2 heq; exact absurd heq (hn2 _)
      · rfl

/-! ## `__eo_requires`: lazy in its body -/

/-- Logos evaluates the body strictly; Kairos only when the guard holds. Both
are pure, so the result is the same; Kairos does less work. -/
@[inline] def k_requires (a b : Id) (k : K Id) : K Id :=
  if a = b ∧ a ≠ 0 then k else pure 0

theorem k_requires_sim (hI : Inv sem σ) {a b : Id} (ha : a < σ.size) (hb : b < σ.size)
    {k : K Id} {t : Term} (hk : a = b ∧ a ≠ 0 → Sim sem σ k t) :
    Sim sem σ (k_requires a b k) (__eo_requires (σ.decode a) (σ.decode b) t) := by
  unfold k_requires
  split
  · rename_i h
    obtain ⟨rfl, h0⟩ := h
    apply (hk ⟨rfl, h0⟩).congr
    have : σ.decode a ≠ .Stuck := fun e => h0 ((decode_eq_stuck_iff hI ha).mp e)
    simp [__eo_requires, native_ite, native_teq, native_not, this]
  · rename_i h
    apply (Sim.pure hI (size_pos hI) (decode_zero hI)).congr
    simp only [__eo_requires, native_ite, native_teq, native_not]
    by_cases hab : a = b
    · subst hab
      have : a = 0 := by simpa using h
      subst this; simp [decode_zero hI]
    · have : σ.decode a ≠ σ.decode b := fun e => hab ((decode_eq_iff hI ha hb).mp e)
      simp [this]

/-! ## `__mk_trans`: recursive, cached -/

/-- The programs whose results are cached, by id, with their Logos meaning. -/
def miniSem : Sem
  | 0, [a, b, c] => some (__mk_trans a b c)
  | _, _ => none

/-- `(and (= t3 t4) tail)`. -/
def matchTransCons (σ : Store) (x : Id) : Option (Id × Id × Id) :=
  match matchBin .and σ x with
  | some (h, tail) =>
    match matchBin .eq σ h with
    | some (t3, t4) => some (t3, t4, tail)
    | none => none
  | none => none

def k_mk_trans : Nat → Id → Id → Id → K Id
  | 0, _, _, _ => throw .fuel
  | n + 1, t1, t2, x => cached 0 [t1, t2, x] <| withStore fun σ =>
    if t1 = 0 then pure 0 else if t2 = 0 then pure 0 else
    match matchTransCons σ x with
    | some (t3, t4, tail) => k_requires t2 t3 (k_mk_trans n t1 t4 tail)
    | none => if σ.view x = .boolean true then mkBin .eq t1 t2 else pure 0

theorem decode_eq_boolean_iff (hI : Inv sem σ) {x : Id} (hx : x < σ.size) {b : Bool} :
    σ.decode x = .Boolean b ↔ σ.view x = .boolean b := by
  rw [decode_view hI hx]
  constructor
  · intro h; cases hv : σ.view x <;> simp [hv, Node.toTerm] at h; simp [h]
  · intro hv; simp [hv, Node.toTerm]

theorem k_mk_trans_sim (n : Nat) :
    ∀ {σ : Store} {t1 t2 x : Id}, Inv miniSem σ → t1 < σ.size → t2 < σ.size → x < σ.size →
    Sim miniSem σ (k_mk_trans n t1 t2 x)
      (__mk_trans (σ.decode t1) (σ.decode t2) (σ.decode x)) := by
  induction n with
  | zero => intro σ t1 t2 x _ _ _ _; exact Ok.throw
  | succ n ih =>
    intro σ t1 t2 x hI h1 h2 hx
    apply cached_sim hI (by simp [h1, h2, hx]) (by simp [miniSem])
    show Sim miniSem σ (if t1 = 0 then pure 0 else if t2 = 0 then pure 0 else
      match matchTransCons σ x with
      | some (t3, t4, tail) => k_requires t2 t3 (k_mk_trans n t1 t4 tail)
      | none => if σ.view x = .boolean true then mkBin .eq t1 t2 else pure 0) _
    have stuck0 := Sim.pure (sem := miniSem) hI (size_pos hI) (decode_zero hI)
    -- case 1: t1 is Stuck
    by_cases z1 : t1 = 0
    · subst z1; simp only [↓reduceIte]
      exact stuck0.congr (by rw [decode_zero hI, __mk_trans.eq_1])
    simp only [z1, ↓reduceIte]
    have d1 : σ.decode t1 = .Stuck → False := fun e => z1 ((decode_eq_stuck_iff hI h1).mp e)
    -- case 2: t2 is Stuck
    by_cases z2 : t2 = 0
    · subst z2; simp only [↓reduceIte]
      exact stuck0.congr (by rw [decode_zero hI, __mk_trans.eq_2 _ _ d1])
    simp only [z2, ↓reduceIte]
    have d2 : σ.decode t2 = .Stuck → False := fun e => z2 ((decode_eq_stuck_iff hI h2).mp e)
    cases hm : matchTransCons σ x with
    | some p =>
      -- case 3: (and (= t3 t4) tail)
      obtain ⟨t3, t4, tail⟩ := p
      unfold matchTransCons at hm
      split at hm <;> try contradiction
      rename_i h tl hm1
      split at hm <;> try contradiction
      rename_i a b hm2
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      obtain ⟨hh, htail, hdx⟩ := matchBin_some hI hx hm1
      obtain ⟨h3, h4, hdh⟩ := matchBin_some hI hh hm2
      simp only
      apply (k_requires_sim hI h2 h3 (fun _ => ih hI h1 h4 htail)).congr
      rw [hdx, hdh, __mk_trans.eq_3 _ _ _ _ _ d1 d2]
    | none =>
      have n3 : ∀ t3 t4 tail : Term, σ.decode x =
          .Apply (.Apply (.UOp .and) (.Apply (.Apply (.UOp .eq) t3) t4)) tail → False := by
        intro t3 t4 tail hd
        unfold matchTransCons at hm
        split at hm
        · rename_i h tl hm1
          split at hm
          · contradiction
          · rename_i hm2
            obtain ⟨hh, -, hdx⟩ := matchBin_some hI hx hm1
            rw [hdx] at hd
            simp only [Term.Apply.injEq] at hd
            exact matchBin_none hI hh hm2 _ _ hd.1.2
        · rename_i hm1; exact matchBin_none hI hx hm1 _ _ hd
      simp only
      by_cases hb : σ.view x = .boolean true
      · -- case 4: true
        simp only [hb, ↓reduceIte]
        apply (mkBin_sim hI .eq h1 h2).congr
        rw [(decode_eq_boolean_iff hI hx).mpr hb, __mk_trans.eq_4 _ _ d1 d2]
      · -- case 5: fall-through
        simp only [hb, ↓reduceIte]
        apply stuck0.congr
        rw [__mk_trans.eq_5 _ _ _ d1 d2 n3
          (fun e => hb ((decode_eq_boolean_iff hI hx).mp e))]

end Kairos
