/-
Proofs of the native list operations (`Kairos/Runtime/Lists.lean`): each
computes Logos's function on the decoded arguments. They are stated against
Logos's definitions (`__eo_list_erase_rec` and the others), so a change to
those breaks this file, not the checker.
-/
import Kairos.Runtime.Lists
import KairosVerification.Gen.Intern

namespace Kairos.Native
open Eo Kairos Store SmtEval

variable {sem : Sem}

/-! ## Facts about ids -/
theorem Ok.withStore' {α : Type} {f : Store → K α} {σ : Store} {Q : α → Store → Prop}
    (h : Ok (f σ) σ Q) : Ok (Kairos.withStore f) σ Q := h

theorem view_zero {σ : Store} (hI : Inv sem σ) : σ.view 0 = .Stuck := by
  simp [Store.view, hI.stuck0]

theorem ne_zero_of_app {σ : Store} (hI : Inv sem σ) {l a b : Id} (hv : σ.view l = .Apply a b) :
    l ≠ 0 := by
  rintro rfl; rw [view_zero hI] at hv; cases hv

theorem dec_stuck_iff {σ : Store} (hI : Inv sem σ) {x : Id} (hx : x < σ.size) :
    σ.decode x = .Stuck ↔ x = 0 := by
  constructor
  · intro h
    exact decode_inj hI x 0 hx (size_pos hI) (by rw [h, decode_zero hI])
  · rintro rfl; exact decode_zero hI

theorem dec_eq_iff {σ : Store} (hI : Inv sem σ) {x y : Id} (hx : x < σ.size) (hy : y < σ.size) :
    σ.decode x = σ.decode y ↔ x = y :=
  ⟨decode_inj hI x y hx hy, fun h => h ▸ rfl⟩

/-- A cell `Apply (Apply f x) y`, read back. -/
theorem cell_dec {σ : Store} (hI : Inv sem σ) {l fx y f x : Id}
    (hl : σ.view l = .Apply fx y) (hfx : σ.view fx = .Apply f x) :
    σ.decode l = .Apply (.Apply (σ.decode f) (σ.decode x)) (σ.decode y) := by
  rw [decode_of_view hI hl]
  simp only [Node.toTerm]
  rw [decode_of_view hI hfx]
  rfl

theorem cell_valid {σ : Store} (hI : Inv sem σ) {l fx y f x : Id} (hlv : l < σ.size)
    (hl : σ.view l = .Apply fx y) (hfx : σ.view fx = .Apply f x) :
    fx < σ.size ∧ y < σ.size ∧ f < σ.size ∧ x < σ.size := by
  obtain ⟨h1, h2⟩ := valid_of_app hI hlv hl
  obtain ⟨h3, h4⟩ := valid_of_app hI h1 hfx
  exact ⟨h1, h2, h3, h4⟩

/-- An id that is not a cell does not read as one. -/
theorem not_cell {σ : Store} (hI : Inv sem σ) {l : Id}
    (h : ∀ fx y, σ.view l = .Apply fx y → ∀ f x, σ.view fx = .Apply f x → False) :
    ∀ F X Y, σ.decode l = .Apply (.Apply F X) Y → False := by
  intro F X Y hd
  obtain ⟨fx, y, hl, hfx, _⟩ := decode_Apply_inv hI hd
  obtain ⟨f, x, hfx', _, _⟩ := decode_Apply_inv hI hfx
  exact h fx y hl f x hfx'

theorem not_cell_of_view {σ : Store} (hI : Inv sem σ) {l : Id}
    (h : ∀ fx y, σ.view l = .Apply fx y → False) :
    ∀ F X Y, σ.decode l = .Apply (.Apply F X) Y → False :=
  not_cell hI fun fx y hl _ _ _ => h fx y hl

theorem not_cell_of_head {σ : Store} (hI : Inv sem σ) {l fx y : Id} (hl : σ.view l = .Apply fx y)
    (h : ∀ f x, σ.view fx = .Apply f x → False) :
    ∀ F X Y, σ.decode l = .Apply (.Apply F X) Y → False :=
  not_cell hI fun fx' y' hl' f x hfx => by
    rw [hl] at hl'; cases hl'; exact h f x hfx

@[simp] theorem ite_true' (a b : Term) : __eo_ite (.Boolean true) a b = a := by
  simp [__eo_ite, native_ite, native_teq]
@[simp] theorem ite_false' (a b : Term) : __eo_ite (.Boolean false) a b = b := by
  simp [__eo_ite, native_ite, native_teq]
@[simp] theorem ite_stuck' (a b : Term) : __eo_ite .Stuck a b = .Stuck := by
  simp [__eo_ite, native_ite, native_teq]

theorem eo_eq_ids {σ : Store} (hI : Inv sem σ) {x z : Id} (hx : x < σ.size) (hz : z < σ.size)
    (hx0 : x ≠ 0) (hz0 : z ≠ 0) :
    __eo_eq (σ.decode x) (σ.decode z) = .Boolean (decide (x = z)) := by
  rw [__eo_eq.eq_3 _ _ (fun h => hx0 ((dec_stuck_iff hI hx).mp h))
    (fun h => hz0 ((dec_stuck_iff hI hz).mp h))]
  simp only [native_teq, Term.Boolean.injEq]
  by_cases h : x = z
  · subst h; simp
  · have : ¬ σ.decode z = σ.decode x := fun e => h ((dec_eq_iff hI hz hx).mp e).symm
    simp [h, this]

/-- The answer of a list walk: `none` is the list itself (not `Stuck`). -/
def OPost (sem : Sem) (σ : Store) (l : Id) (t : Term) (r? : Option Id) (σ' : Store) : Prop :=
  Inv sem σ' ∧ Extends σ σ' ∧
    match r? with
    | none => σ.decode l = t ∧ l ≠ 0
    | some r => r < σ'.size ∧ σ'.decode r = t

theorem OPost.some_zero {σ : Store} (hI : Inv sem σ) {l : Id} :
    OPost sem σ l .Stuck (some 0) σ :=
  ⟨hI, Extends.refl σ, size_pos hI, decode_zero hI⟩

theorem OPost.none_of {σ : Store} (hI : Inv sem σ) {l : Id} {t : Term} (h : σ.decode l = t)
    (hl : l ≠ 0) : OPost sem σ l t none σ :=
  ⟨hI, Extends.refl σ, h, hl⟩

/-- The value of a walk, as an id: `none` is the list. -/
theorem OPost.sim {σ σ' : Store} {l : Id} {t : Term} {r? : Option Id} (hl : l < σ.size)
    (h : OPost sem σ l t r? σ') :
    Post sem σ t (match r? with | none => l | some r => r) σ' := by
  obtain ⟨hI', hE, h⟩ := h
  cases r? with
  | none => exact ⟨hI', hE, Nat.lt_of_lt_of_le hl hE.size_le, by rw [decode_extends hE l hl]; exact h.1⟩
  | some r => exact ⟨hI', hE, h.1, h.2⟩

/-- Interning a cell onto a walked tail. -/
theorem intern_cell {σ σ1 : Store} (hI1 : Inv sem σ1) (hE : Extends σ σ1) {fx r : Id}
    (hfx : fx < σ.size) (hr : r < σ1.size) {l : Id} {t : Term}
    (ht : Term.Apply (σ.decode fx) (σ1.decode r) = t) :
    Ok (do let c ← intern (.Apply fx r); pure (some c) : K (Option Id)) σ1 (OPost sem σ l t) := by
  apply Ok.bind
  apply Ok.mono (intern_sim hI1 (n := .Apply fx r)
    (by simp [Node.children, Nat.lt_of_lt_of_le hfx hE.size_le, hr]))
  intro c σ2 ⟨hI2, hE2, hc, hd⟩
  refine Ok.pure ⟨hI2, hE.trans hE2, hc, ?_⟩
  rw [hd]; simp only [Node.toTerm]; rw [decode_extends hE fx hfx]; exact ht

theorem OPost.getD {σ σ' : Store} {l : Id} {t : Term} {r? : Option Id} (hl : l < σ.size)
    (h : OPost sem σ l t r? σ') :
    Inv sem σ' ∧ Extends σ σ' ∧ r?.getD l < σ'.size ∧ σ'.decode (r?.getD l) = t := by
  have := h.sim hl
  cases r? <;> exact ⟨this.inv, this.ext, this.valid, this.dec⟩

/-- A valid id other than 0 is not `Stuck`. -/
theorem ns {σ : Store} (hI : Inv sem σ) {x : Id} (hx : x < σ.size) (h0 : x ≠ 0) :
    σ.decode x = .Stuck → False := fun e => h0 ((dec_stuck_iff hI hx).mp e)

/-! ## `__eo_list_erase_rec` -/
theorem eraseR_spec {z : Id} :
    ∀ (n : Nat) {σ : Store} {l : Id}, Inv sem σ → l < σ.size → z < σ.size → z ≠ 0 →
      Ok (eraseR z n l) σ (OPost sem σ l (__eo_list_erase_rec (σ.decode l) (σ.decode z)))
  | 0, _, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, hI, hl, hz, hz0 => by
    have hZ : σ.decode z = .Stuck → False := fun h => hz0 ((dec_stuck_iff hI hz).mp h)
    unfold eraseR
    apply Ok.withStore'
    split
    · rename_i fx y hv
      split
      · rename_i f x hfx
        obtain ⟨hfxv, hy, hf, hx⟩ := cell_valid hI hl hv hfx
        rw [cell_dec hI hv hfx, __eo_list_erase_rec.eq_3 _ _ _ _ hZ]
        by_cases hx0 : x = 0
        · simp only [hx0, ↓reduceIte]
          subst hx0
          rw [decode_zero hI, __eo_eq.eq_1, ite_stuck']
          exact Ok.pure (OPost.some_zero hI)
        · simp only [hx0, ↓reduceIte]
          rw [eo_eq_ids hI hx hz hx0 hz0]
          by_cases hxz : x = z
          · simp only [hxz, ↓reduceIte, decide_true, ite_true']
            exact Ok.pure ⟨hI, Extends.refl σ, hy, rfl⟩
          · simp only [hxz, ↓reduceIte, decide_false, ite_false']
            apply Ok.bind
            apply Ok.mono (eraseR_spec n hI hy hz hz0)
            intro r? σ1 ⟨hI1, hE1, hr⟩
            have hFX : Term.Apply (σ.decode f) (σ.decode x) ≠ .Stuck := by simp
            cases r? with
            | none =>
              obtain ⟨hd, hy0⟩ := hr
              refine Ok.pure ⟨hI1, hE1, ?_, ne_zero_of_app hI hv⟩
              rw [← hd, __eo_mk_apply.eq_3 _ _ (fun h => hFX h)
                (fun h => hy0 ((dec_stuck_iff hI hy).mp h))]
              exact (cell_dec hI hv hfx)
            | some r =>
              obtain ⟨hrv, hrd⟩ := hr
              simp only
              by_cases hr0 : r = 0
              · simp only [hr0, ↓reduceIte]
                subst hr0
                rw [decode_zero hI1] at hrd
                rw [← hrd, __eo_mk_apply.eq_2 _ (fun h => hFX h)]
                exact Ok.pure ⟨hI1, hE1, size_pos hI1, decode_zero hI1⟩
              · simp only [hr0, ↓reduceIte]
                refine intern_cell hI1 hE1 hfxv hrv ?_
                rw [decode_of_view hI hfx, hrd]
                simp only [Node.toTerm]
                rw [__eo_mk_apply.eq_3 _ _ (fun h => hFX h) (fun h => hr0 ((dec_stuck_iff hI1 hrv).mp
                  (hrd.trans h)))]
      · rename_i hfx
        have hl0 := ne_zero_of_app hI hv
        simp only [hl0, ↓reduceIte]
        refine Ok.pure (OPost.none_of hI ?_ hl0)
        rw [__eo_list_erase_rec.eq_4 _ _ (fun h => hl0 ((dec_stuck_iff hI hl).mp h))
          (not_cell_of_head hI hv fun f x h => hfx f x h) hZ]
    · rename_i hv
      by_cases hl0 : l = 0
      · simp only [hl0, ↓reduceIte]
        subst hl0
        rw [decode_zero hI, __eo_list_erase_rec.eq_1]
        exact Ok.pure (OPost.some_zero hI)
      · simp only [hl0, ↓reduceIte]
        refine Ok.pure (OPost.none_of hI ?_ hl0)
        rw [__eo_list_erase_rec.eq_4 _ _ (fun h => hl0 ((dec_stuck_iff hI hl).mp h))
          (not_cell_of_view hI fun fx y h => hv fx y h) hZ]

theorem erase_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {l z : Id} (hl : l < σ.size)
    (hz : z < σ.size) :
    Sim sem σ (erase n l z) (__eo_list_erase_rec (σ.decode l) (σ.decode z)) := by
  unfold erase
  by_cases h : l = 0 ∨ z = 0
  · simp only [h, ↓reduceIte]
    refine Ok.pure ⟨hI, Extends.refl σ, size_pos hI, ?_⟩
    rw [decode_zero hI]
    by_cases hl0 : l = 0
    · subst hl0; rw [decode_zero hI, __eo_list_erase_rec.eq_1]
    · have hz0 : z = 0 := h.resolve_left hl0
      subst hz0
      rw [decode_zero hI, __eo_list_erase_rec.eq_2 _ (fun e => hl0 ((dec_stuck_iff hI hl).mp e))]
  · simp only [h, ↓reduceIte]
    have hz0 : z ≠ 0 := fun e => h (.inr e)
    apply Ok.bind
    apply Ok.mono (eraseR_spec n hI hl hz hz0)
    intro r? σ1 hp
    have := hp.sim hl
    cases r? <;> exact Ok.pure this

/-! ## `__eo_list_erase_all_rec` -/
theorem eraseAllR_spec {z : Id} :
    ∀ (n : Nat) {σ : Store} {l : Id}, Inv sem σ → l < σ.size → z < σ.size → z ≠ 0 →
      Ok (eraseAllR z n l) σ (OPost sem σ l (__eo_list_erase_all_rec (σ.decode l) (σ.decode z)))
  | 0, _, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, hI, hl, hz, hz0 => by
    have hZ := ns hI hz hz0
    unfold eraseAllR
    apply Ok.withStore'
    split
    · rename_i fx y hv
      split
      · rename_i f x hfx
        obtain ⟨hfxv, hy, hf, hx⟩ := cell_valid hI hl hv hfx
        rw [cell_dec hI hv hfx, __eo_list_erase_all_rec.eq_3 _ _ _ _ hZ]
        by_cases hfx0 : f = 0 ∨ x = 0
        · simp only [hfx0, ↓reduceIte]
          by_cases hf0 : f = 0
          · subst hf0; rw [decode_zero hI, __eo_prepend_if.eq_1]
            exact Ok.pure (OPost.some_zero hI)
          · have hx0 : x = 0 := hfx0.resolve_left hf0
            subst hx0; rw [decode_zero hI, __eo_prepend_if.eq_2 _ _ _ (ns hI hf hf0)]
            exact Ok.pure (OPost.some_zero hI)
        · simp only [hfx0, ↓reduceIte]
          have hf0 : f ≠ 0 := fun e => hfx0 (.inl e)
          have hx0 : x ≠ 0 := fun e => hfx0 (.inr e)
          apply Ok.bind
          apply Ok.mono (eraseAllR_spec n hI hy hz hz0)
          intro r? σ1 hp
          obtain ⟨hI1, hE1, hresv, hresd⟩ := hp.getD hy
          rw [eo_eq_ids hI hz hx hz0 hx0, __eo_not.eq_1]
          have hF := ns hI hf hf0
          have hX := ns hI hx hx0
          by_cases hres0 : r?.getD y = 0
          · simp only [hres0, ↓reduceIte]
            rw [hres0, decode_zero hI1] at hresd
            rw [← hresd, __eo_prepend_if.eq_3 _ _ _ hF hX]
            exact Ok.pure ⟨hI1, hE1, size_pos hI1, decode_zero hI1⟩
          · simp only [hres0, ↓reduceIte]
            have hR : σ1.decode (r?.getD y) = .Stuck → False := ns hI1 hresv hres0
            by_cases hxz : x = z
            · subst hxz
              simp only [↓reduceIte, decide_true, native_not, Bool.not_true]
              rw [← hresd, __eo_prepend_if.eq_5 _ _ _ hF hX hR]
              exact Ok.pure ⟨hI1, hE1, hresv, rfl⟩
            · have hzx : ¬ z = x := fun e => hxz e.symm
              simp only [hxz, ↓reduceIte, hzx, decide_false, native_not, Bool.not_false]
              rw [← hresd, __eo_prepend_if.eq_4 _ _ _ hF hX hR]
              cases r? with
              | none =>
                obtain ⟨hd, _⟩ := hp.2.2
                refine Ok.pure ⟨hI1, hE1, ?_, ne_zero_of_app hI hv⟩
                simp only [Option.getD_none] at hresd ⊢
                rw [cell_dec hI hv hfx, decode_extends hE1 y hy]
              | some r =>
                simp only [Option.getD_some] at hresv ⊢
                refine intern_cell hI1 hE1 hfxv hresv ?_
                rw [decode_of_view hI hfx]; rfl
      · rename_i hfx
        have hl0 := ne_zero_of_app hI hv
        simp only [hl0, ↓reduceIte]
        refine Ok.pure (OPost.none_of hI ?_ hl0)
        rw [__eo_list_erase_all_rec.eq_4 _ _ (ns hI hl hl0)
          (not_cell_of_head hI hv fun f x h => hfx f x h) hZ]
    · rename_i hv
      by_cases hl0 : l = 0
      · simp only [hl0, ↓reduceIte]
        subst hl0
        rw [decode_zero hI, __eo_list_erase_all_rec.eq_1]
        exact Ok.pure (OPost.some_zero hI)
      · simp only [hl0, ↓reduceIte]
        refine Ok.pure (OPost.none_of hI ?_ hl0)
        rw [__eo_list_erase_all_rec.eq_4 _ _ (ns hI hl hl0)
          (not_cell_of_view hI fun fx y h => hv fx y h) hZ]

theorem eraseAll_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {l z : Id} (hl : l < σ.size)
    (hz : z < σ.size) :
    Sim sem σ (eraseAll n l z) (__eo_list_erase_all_rec (σ.decode l) (σ.decode z)) := by
  unfold eraseAll
  by_cases h : l = 0 ∨ z = 0
  · simp only [h, ↓reduceIte]
    refine Ok.pure ⟨hI, Extends.refl σ, size_pos hI, ?_⟩
    rw [decode_zero hI]
    by_cases hl0 : l = 0
    · subst hl0; rw [decode_zero hI, __eo_list_erase_all_rec.eq_1]
    · have hz0 : z = 0 := h.resolve_left hl0
      subst hz0
      rw [decode_zero hI, __eo_list_erase_all_rec.eq_2 _ (ns hI hl hl0)]
  · simp only [h, ↓reduceIte]
    have hz0 : z ≠ 0 := fun e => h (.inr e)
    apply Ok.bind
    apply Ok.mono (eraseAllR_spec n hI hl hz hz0)
    intro r? σ1 hp
    have := hp.sim hl
    cases r? <;> exact Ok.pure this

/-! ## `__eo_list_setof_rec` -/
theorem setofR_spec :
    ∀ (n : Nat) {σ : Store} {l : Id}, Inv sem σ → l < σ.size →
      Ok (setofR n l) σ (OPost sem σ l (__eo_list_setof_rec (σ.decode l)))
  | 0, _, _, _, _ => Ok.throw
  | n + 1, σ, l, hI, hl => by
    unfold setofR
    apply Ok.withStore'
    split
    · rename_i fx y hv
      split
      · rename_i f x hfx
        obtain ⟨hfxv, hy, hf, hx⟩ := cell_valid hI hl hv hfx
        rw [cell_dec hI hv hfx, __eo_list_setof_rec.eq_2]
        have hFX : Term.Apply (σ.decode f) (σ.decode x) = .Stuck → False := by simp
        apply Ok.bind
        apply Ok.mono (setofR_spec n hI hy)
        intro s? σ1 hp
        obtain ⟨hI1, hE1, hsv, hsd⟩ := hp.getD hy
        apply Ok.bind
        apply Ok.mono (eraseAll_sim (n := n) hI1 hsv (Nat.lt_of_lt_of_le hx hE1.size_le))
        intro e σ2 ⟨hI2, hE2, hev, hed⟩
        rw [hsd, decode_extends hE1 x hx] at hed
        have hE12 := hE1.trans hE2
        by_cases he0 : e = 0
        · simp only [he0, ↓reduceIte]
          rw [he0, decode_zero hI2] at hed
          rw [← hed, __eo_mk_apply.eq_2 _ hFX]
          exact Ok.pure ⟨hI2, hE12, size_pos hI2, decode_zero hI2⟩
        · simp only [he0, ↓reduceIte]
          have hEs := ns hI2 hev he0
          rw [← hed, __eo_mk_apply.eq_3 _ _ hFX hEs]
          by_cases hey : e = y
          · simp only [hey, ↓reduceIte]
            subst hey
            refine Ok.pure ⟨hI2, hE12, ?_, ne_zero_of_app hI hv⟩
            rw [cell_dec hI hv hfx, decode_extends hE12 e hy]
          · simp only [hey, ↓reduceIte]
            refine intern_cell hI2 hE12 hfxv hev ?_
            rw [decode_of_view hI hfx]; rfl
      · rename_i hfx
        have hl0 := ne_zero_of_app hI hv
        simp only [hl0, ↓reduceIte]
        refine Ok.pure (OPost.none_of hI ?_ hl0)
        rw [__eo_list_setof_rec.eq_3 _ (ns hI hl hl0) (not_cell_of_head hI hv fun f x h => hfx f x h)]
    · rename_i hv
      by_cases hl0 : l = 0
      · simp only [hl0, ↓reduceIte]
        subst hl0
        rw [decode_zero hI, __eo_list_setof_rec.eq_1]
        exact Ok.pure (OPost.some_zero hI)
      · simp only [hl0, ↓reduceIte]
        refine Ok.pure (OPost.none_of hI ?_ hl0)
        rw [__eo_list_setof_rec.eq_3 _ (ns hI hl hl0) (not_cell_of_view hI fun fx y h => hv fx y h)]

theorem setof_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {l : Id} (hl : l < σ.size) :
    Sim sem σ (setof n l) (__eo_list_setof_rec (σ.decode l)) := by
  unfold setof
  apply Ok.bind
  apply Ok.mono (setofR_spec n hI hl)
  intro r? σ1 hp
  have := hp.sim hl
  cases r? <;> exact Ok.pure this

/-! ## `__eo_list_diff_rec` -/
theorem diffR_spec :
    ∀ (n : Nat) {σ : Store} {l b : Id}, Inv sem σ → l < σ.size → b < σ.size →
      Ok (diffR n l b) σ (OPost sem σ l (__eo_list_diff_rec (σ.decode l) (σ.decode b)))
  | 0, _, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, b, hI, hl, hb => by
    unfold diffR
    apply Ok.withStore'
    by_cases hb0 : b = 0
    · simp only [hb0, ↓reduceIte]
      subst hb0
      rw [decode_zero hI]
      by_cases hl0 : l = 0
      · subst hl0; rw [decode_zero hI, __eo_list_diff_rec.eq_1]
        exact Ok.pure (OPost.some_zero hI)
      · rw [__eo_list_diff_rec.eq_2 _ (ns hI hl hl0)]
        exact Ok.pure (OPost.some_zero hI)
    simp only [hb0, ↓reduceIte]
    have hB := ns hI hb hb0
    split
    · rename_i fx y hv
      split
      · rename_i f x hfx
        obtain ⟨hfxv, hy, hf, hx⟩ := cell_valid hI hl hv hfx
        rw [cell_dec hI hv hfx, __eo_list_diff_rec.eq_3 _ _ _ _ hB]
        by_cases hfx0 : f = 0 ∨ x = 0
        · simp only [hfx0, ↓reduceIte]
          by_cases hf0 : f = 0
          · subst hf0; rw [decode_zero hI, __eo_prepend_if.eq_1]
            exact Ok.pure (OPost.some_zero hI)
          · have hx0 : x = 0 := hfx0.resolve_left hf0
            subst hx0; rw [decode_zero hI, __eo_prepend_if.eq_2 _ _ _ (ns hI hf hf0)]
            exact Ok.pure (OPost.some_zero hI)
        · simp only [hfx0, ↓reduceIte]
          have hf0 : f ≠ 0 := fun e => hfx0 (.inl e)
          have hx0 : x ≠ 0 := fun e => hfx0 (.inr e)
          have hF := ns hI hf hf0
          have hX := ns hI hx hx0
          apply Ok.bind
          apply Ok.mono (erase_sim (n := n) hI hb hx)
          intro v σ1 ⟨hI1, hE1, hvv, hvd⟩
          rw [← hvd]
          by_cases hv0 : v = 0
          · simp only [hv0, ↓reduceIte]
            subst hv0
            rw [decode_zero hI1, __eo_eq.eq_1]
            have : __eo_list_diff_rec (σ.decode y) .Stuck = .Stuck := by
              by_cases hy0 : y = 0
              · subst hy0; rw [decode_zero hI, __eo_list_diff_rec.eq_1]
              · rw [__eo_list_diff_rec.eq_2 _ (ns hI hy hy0)]
            rw [this, __eo_prepend_if.eq_3 _ _ _ hF hX]
            exact Ok.pure ⟨hI1, hE1, size_pos hI1, decode_zero hI1⟩
          · simp only [hv0, ↓reduceIte]
            have hy1 := Nat.lt_of_lt_of_le hy hE1.size_le
            have hb1 := Nat.lt_of_lt_of_le hb hE1.size_le
            apply Ok.bind
            apply Ok.mono (diffR_spec n hI1 hy1 hvv)
            intro r? σ2 hp
            obtain ⟨hI2, hE2, hresv, hresd⟩ := hp.getD hy1
            rw [decode_extends hE1 y hy] at hresd
            have hE12 := hE1.trans hE2
            rw [← decode_extends hE1 b hb, eo_eq_ids hI1 hvv hb1 hv0 hb0]
            by_cases hres0 : r?.getD y = 0
            · simp only [hres0, ↓reduceIte]
              rw [hres0, decode_zero hI2] at hresd
              rw [← hresd, __eo_prepend_if.eq_3 _ _ _ hF hX]
              exact Ok.pure ⟨hI2, hE12, size_pos hI2, decode_zero hI2⟩
            · simp only [hres0, ↓reduceIte]
              have hR := ns hI2 hresv hres0
              by_cases hvb : v = b
              · simp only [hvb, ↓reduceIte, decide_true]
                rw [hvb] at hresd
                rw [← hresd, __eo_prepend_if.eq_4 _ _ _ hF hX hR]
                cases r? with
                | none =>
                  refine Ok.pure ⟨hI2, hE12, ?_, ne_zero_of_app hI hv⟩
                  simp only [Option.getD_none] at hresd ⊢
                  rw [cell_dec hI hv hfx, decode_extends hE12 y hy]
                | some r =>
                  simp only [Option.getD_some] at hresv ⊢
                  refine intern_cell hI2 hE12 hfxv hresv ?_
                  rw [decode_of_view hI hfx]; rfl
              · simp only [hvb, ↓reduceIte, decide_false]
                rw [← hresd, __eo_prepend_if.eq_5 _ _ _ hF hX hR]
                exact Ok.pure ⟨hI2, hE12, hresv, rfl⟩
      · rename_i hfx
        have hl0 := ne_zero_of_app hI hv
        simp only [hl0, ↓reduceIte]
        refine Ok.pure (OPost.none_of hI ?_ hl0)
        rw [__eo_list_diff_rec.eq_4 _ _ (ns hI hl hl0)
          (not_cell_of_head hI hv fun f x h => hfx f x h) hB]
    · rename_i hv
      by_cases hl0 : l = 0
      · simp only [hl0, ↓reduceIte]
        subst hl0
        rw [decode_zero hI, __eo_list_diff_rec.eq_1]
        exact Ok.pure (OPost.some_zero hI)
      · simp only [hl0, ↓reduceIte]
        refine Ok.pure (OPost.none_of hI ?_ hl0)
        rw [__eo_list_diff_rec.eq_4 _ _ (ns hI hl hl0)
          (not_cell_of_view hI fun fx y h => hv fx y h) hB]

theorem diff_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {l b : Id} (hl : l < σ.size)
    (hb : b < σ.size) :
    Sim sem σ (diff n l b) (__eo_list_diff_rec (σ.decode l) (σ.decode b)) := by
  unfold diff
  apply Ok.bind
  apply Ok.mono (diffR_spec n hI hl hb)
  intro r? σ1 hp
  have := hp.sim hl
  cases r? <;> exact Ok.pure this

/-! ## `__eo_get_nil_rec` -/
theorem requires_self {F t : Term} (hF : F = .Stuck → False) : __eo_requires F F t = t := by
  simp only [__eo_requires, native_ite, native_teq, native_not, decide_true, ↓reduceIte]
  have : decide (F = .Stuck) = false := decide_eq_false hF
  simp [this]

theorem requires_ne {F G t : Term} (h : F = G → False) : __eo_requires F G t = .Stuck := by
  simp only [__eo_requires, native_ite, native_teq]
  have : decide (F = G) = false := decide_eq_false h
  simp [this]

theorem requires_true {X t : Term} :
    __eo_requires X (.Boolean true) t = if X = .Boolean true then t else .Stuck := by
  by_cases h : X = .Boolean true <;> simp [__eo_requires, native_ite, native_teq, native_not, h]

theorem getNilR_spec {isNil : Id → Id → K Id}
    (hNil : ∀ {σ : Store} {a b : Id}, Inv sem σ → a < σ.size → b < σ.size →
      Sim sem σ (isNil a b) (__eo_is_list_nil (σ.decode a) (σ.decode b))) {f : Id} :
    ∀ (n : Nat) {σ : Store} {l : Id}, Inv sem σ → l < σ.size → f < σ.size → f ≠ 0 →
      Sim sem σ (getNilR isNil f n l) (__eo_get_nil_rec (σ.decode f) (σ.decode l))
  | 0, _, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, hI, hl, hf, hf0 => by
    have hF := ns hI hf hf0
    unfold getNilR
    apply Ok.withStore'
    by_cases hl0 : l = 0
    · simp only [hl0, ↓reduceIte]
      subst hl0
      rw [decode_zero hI, __eo_get_nil_rec.eq_2 _ hF]
      exact Sim.pure hI (size_pos hI) (decode_zero hI)
    simp only [hl0, ↓reduceIte]
    have hL := ns hI hl hl0
    -- the end of the list
    have atNil : (∀ F X Y, σ.decode l = .Apply (.Apply F X) Y → False) →
        Sim sem σ (do
          let b ← isNil f l
          Kairos.withStore fun σ => pure (if σ.view b = .Boolean true then l else 0))
          (__eo_get_nil_rec (σ.decode f) (σ.decode l)) := by
      intro hnc
      rw [__eo_get_nil_rec.eq_4 _ _ hF hL (fun g x y h => hnc g x y h), requires_true]
      apply Ok.bind
      apply Ok.mono (hNil hI hf hl)
      intro b σ1 ⟨hI1, hE1, hbv, hbd⟩
      apply Ok.withStore'
      rw [← hbd]
      by_cases hvb : σ1.view b = .Boolean true
      · have : σ1.decode b = .Boolean true := by rw [decode_of_view hI1 hvb]; rfl
        simp only [hvb, ↓reduceIte, this]
        exact Ok.pure ⟨hI1, hE1, Nat.lt_of_lt_of_le hl hE1.size_le, decode_extends hE1 l hl⟩
      · have : ¬ σ1.decode b = .Boolean true := fun e =>
          hvb (decode_leaf_inv hI1 (n := .Boolean true) rfl (d := fun _ => .Stuck) e)
        simp only [hvb, ↓reduceIte, this]
        exact Ok.pure ⟨hI1, hE1, size_pos hI1, decode_zero hI1⟩
    split
    · rename_i gx y hv
      split
      · rename_i g x hgx
        obtain ⟨_, hy, hg, _⟩ := cell_valid hI hl hv hgx
        rw [cell_dec hI hv hgx, __eo_get_nil_rec.eq_3 _ _ _ _ hF]
        by_cases hgf : g = f
        · simp only [hgf, ↓reduceIte]
          subst hgf
          rw [requires_self hF]
          exact getNilR_spec hNil n hI hy hg hf0
        · simp only [hgf, ↓reduceIte]
          rw [requires_ne (fun e => hgf ((dec_eq_iff hI hf hg).mp e).symm)]
          exact Sim.pure hI (size_pos hI) (decode_zero hI)
      · rename_i hgx
        exact atNil (not_cell_of_head hI hv fun g x h => hgx g x h)
    · rename_i hv
      exact atNil (not_cell_of_view hI fun gx y h => hv gx y h)

theorem getNil_sim {isNil : Id → Id → K Id} {n : Nat}
    (hNil : ∀ {σ : Store} {a b : Id}, Inv sem σ → a < σ.size → b < σ.size →
      Sim sem σ (isNil a b) (__eo_is_list_nil (σ.decode a) (σ.decode b)))
    {σ : Store} (hI : Inv sem σ) {f l : Id} (hf : f < σ.size) (hl : l < σ.size) :
    Sim sem σ (getNil isNil n f l) (__eo_get_nil_rec (σ.decode f) (σ.decode l)) := by
  unfold getNil
  by_cases hf0 : f = 0
  · simp only [hf0, ↓reduceIte]
    subst hf0
    rw [decode_zero hI, __eo_get_nil_rec.eq_1]
    exact Sim.pure hI (size_pos hI) (decode_zero hI)
  · simp only [hf0, ↓reduceIte]
    exact getNilR_spec hNil n hI hl hf hf0

/-! ## `__eo_is_list` -/
theorem bool_sim {σ : Store} (hI : Inv sem σ) {t : Term} (b : Bool) (h : t = .Boolean b) :
    Sim sem σ (pure (if b then 1 else 2)) t := by
  obtain ⟨_, _, hv, hb⟩ := bool_interned hI b
  exact Sim.pure hI hv (by rw [decode_of_view hI hb, h]; rfl)

theorem is_ok_stuck : __eo_is_ok .Stuck = .Boolean false := by
  simp [__eo_is_ok, native_teq, native_not]

theorem is_ok_of {t : Term} (h : t ≠ .Stuck) : __eo_is_ok t = .Boolean true := by
  simp [__eo_is_ok, native_teq, native_not, h]

theorem isListR_spec {isNil : Id → Id → K Id}
    (hNil : ∀ {σ : Store} {a b : Id}, Inv sem σ → a < σ.size → b < σ.size →
      Sim sem σ (isNil a b) (__eo_is_list_nil (σ.decode a) (σ.decode b))) {f : Id} :
    ∀ (n : Nat) {σ : Store} {l : Id}, Inv sem σ → l < σ.size → f < σ.size → f ≠ 0 →
      Sim sem σ (isListR isNil f n l) (__eo_is_ok (__eo_get_nil_rec (σ.decode f) (σ.decode l)))
  | 0, _, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, hI, hl, hf, hf0 => by
    have hF := ns hI hf hf0
    unfold isListR
    apply Ok.withStore'
    have atNil : (∀ F X Y, σ.decode l = .Apply (.Apply F X) Y → False) →
        Sim sem σ (isListR.isNilB isNil f l)
          (__eo_is_ok (__eo_get_nil_rec (σ.decode f) (σ.decode l))) := by
      intro hnc
      unfold isListR.isNilB
      by_cases hl0 : l = 0
      · simp only [hl0, ↓reduceIte]
        refine bool_sim hI false ?_
        rw [decode_zero hI, __eo_get_nil_rec.eq_2 _ hF, is_ok_stuck]
      simp only [hl0, ↓reduceIte]
      have hL := ns hI hl hl0
      rw [__eo_get_nil_rec.eq_4 _ _ hF hL (fun g x y h => hnc g x y h), requires_true]
      apply Ok.bind
      apply Ok.mono (hNil hI hf hl)
      intro b σ1 ⟨hI1, hE1, hbv, hbd⟩
      rw [← hbd]
      apply Ok.mono (P := Post sem σ1 _) (Q := Post sem σ _) ?_ (fun _ _ h => h.weaken hE1)
      by_cases hb1 : b = 1
      · have hv : σ1.view b = .Boolean true := (view_bool_iff (b := true) hI1).mpr hb1
        have : σ1.decode b = .Boolean true := by rw [decode_of_view hI1 hv]; rfl
        rw [ite_eq_left this, ite_eq_left hb1]
        exact bool_sim hI1 true (is_ok_of hL)
      · have : ¬ σ1.decode b = .Boolean true := fun e =>
          hb1 ((view_bool_iff (b := true) hI1).mp
            (decode_leaf_inv hI1 (n := .Boolean true) rfl (d := fun _ => .Stuck) e))
        rw [ite_eq_right this, ite_eq_right hb1]
        exact bool_sim hI1 false is_ok_stuck
    split
    · rename_i gx y hv
      split
      · rename_i g x hgx
        obtain ⟨_, hy, hg, _⟩ := cell_valid hI hl hv hgx
        rw [cell_dec hI hv hgx, __eo_get_nil_rec.eq_3 _ _ _ _ hF]
        by_cases hgf : g = f
        · simp only [hgf, ↓reduceIte]
          rw [requires_self hF]
          exact isListR_spec hNil n hI hy hf hf0
        · simp only [hgf, ↓reduceIte]
          rw [requires_ne (fun e => hgf ((dec_eq_iff hI hf hg).mp e).symm)]
          exact bool_sim hI false is_ok_stuck
      · rename_i hgx
        exact atNil (not_cell_of_head hI hv fun g x h => hgx g x h)
    · rename_i hv
      exact atNil (not_cell_of_view hI fun gx y h => hv gx y h)

theorem isList_sim {isNil : Id → Id → K Id} {n : Nat}
    (hNil : ∀ {σ : Store} {a b : Id}, Inv sem σ → a < σ.size → b < σ.size →
      Sim sem σ (isNil a b) (__eo_is_list_nil (σ.decode a) (σ.decode b)))
    {σ : Store} (hI : Inv sem σ) {f l : Id} (hf : f < σ.size) (hl : l < σ.size) :
    Sim sem σ (isList isNil n f l) (__eo_is_list (σ.decode f) (σ.decode l)) := by
  unfold isList
  by_cases hf0 : f = 0
  · simp only [hf0, true_or, ↓reduceIte]
    rw [decode_zero hI, __eo_is_list.eq_1]
    exact Sim.pure hI (size_pos hI) (decode_zero hI)
  by_cases hl0 : l = 0
  · simp only [hl0, or_true, ↓reduceIte]
    rw [decode_zero hI, __eo_is_list.eq_2 _ (ns hI hf hf0)]
    exact Sim.pure hI (size_pos hI) (decode_zero hI)
  simp only [hf0, hl0, or_self, ↓reduceIte]
  rw [__eo_is_list.eq_3 _ _ (ns hI hf hf0) (ns hI hl hl0)]
  exact isListR_spec hNil n hI hl hf hf0

/-! ## `__eo_cmp` -/
theorem natCmp_refl (a : Nat) : natCmp a a = .eq := by simp [natCmp]
theorem intCmp_refl (a : Int) : intCmp a a = .eq := by simp [intCmp]
theorem boolCmp_refl (a : Bool) : boolCmp a a = .eq := by cases a <;> rfl
theorem ratCmp_refl (a : native_Rat) : ratCmp a a = .eq := by
  simp [ratCmp, intCmp_refl, natCmp_refl]
theorem stringCmp_refl : ∀ a : native_String, stringCmp a a = .eq
  | [] => rfl
  | c :: s => by simp [stringCmp, natCmp_refl, stringCmp_refl s]

mutual
theorem termCmp_refl : ∀ t : Term, termCmp t t = .eq := by
  intro t
  cases t <;> simp only [termCmp, natCmp_refl, intCmp_refl, boolCmp_refl, ratCmp_refl,
    stringCmp_refl, userOpCmp, userOp1Cmp, userOp2Cmp, userOp3Cmp, termCmp_refl,
    datatypeDeclCmp_refl]
theorem datatypeDeclCmp_refl : ∀ t : DatatypeDecl, datatypeDeclCmp t t = .eq := by
  intro t
  cases t <;> simp only [datatypeDeclCmp, natCmp_refl, stringCmp_refl, datatypeCmp_refl,
    datatypeDeclCmp_refl]
theorem datatypeCmp_refl : ∀ t : Datatype, datatypeCmp t t = .eq := by
  intro t
  cases t <;> simp only [datatypeCmp, natCmp_refl, datatypeConsCmp_refl, datatypeCmp_refl]
theorem datatypeConsCmp_refl : ∀ t : DatatypeCons, datatypeConsCmp t t = .eq := by
  intro t
  cases t <;> simp only [datatypeConsCmp, natCmp_refl, termCmp_refl, datatypeConsCmp_refl]
end

theorem termCmp_of_ctor {s t : Term} (h : s.ctorIdx ≠ t.ctorIdx) :
    termCmp s t = natCmp s.ctorIdx t.ctorIdx := by
  cases s <;> first | rfl | (cases t <;> first | rfl | exact absurd rfl h)

theorem ctorIdx_toTerm (d : Id → Term) (n : Node) : (n.toTerm d).ctorIdx = n.ctorIdx := by
  cases n <;> rfl

theorem child_lt {σ : Store} (hI : Inv sem σ) {a : Id} {n : Node} (hv : σ.view a = n)
    (hn : n ≠ .Stuck) {j : Id} (hj : j ∈ n.children) : j < a := by
  have ha : a < σ.size := Classical.byContradiction fun h => hn (hv ▸ view_out h)
  exact lt_of_child hI ha (hv ▸ hj)

theorem cmpId_spec {σ : Store} (hI : Inv sem σ) :
    ∀ a b : Id, cmpId σ a b = termCmp (σ.decode a) (σ.decode b) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b
    rw [cmpId]
    by_cases hab : a = b
    · subst hab; simp only [↓reduceIte, termCmp_refl]
    simp only [hab, ↓reduceIte]
    split
    · rename_i f x g y ha hb
      have hf := child_lt hI ha (by simp) (j := f) (by simp [Node.children])
      have hx := child_lt hI ha (by simp) (j := x) (by simp [Node.children])
      rw [decode_of_view hI ha, decode_of_view hI hb]
      simp only [hf, hx, and_self, ↓reduceDIte, Node.toTerm, termCmp, ih f hf, ih x hx]
      cases termCmp (σ.decode f) (σ.decode g) <;> rfl
    · rename_i i x j y ha hb
      have hx := child_lt hI ha (by simp) (j := x) (by simp [Node.children])
      rw [decode_of_view hI ha, decode_of_view hI hb]
      simp only [hx, ↓reduceDIte, Node.toTerm, termCmp, ih x hx]
      cases natCmp i j <;> rfl
    · rename_i ha hb
      rw [decode_of_view hI ha, decode_of_view hI hb]
      simp only [Node.toTerm, termCmp]
    · split
      · rfl
      · rename_i h
        rw [decode_view' hI a, decode_view' hI b, termCmp_of_ctor] <;>
          simp only [ctorIdx_toTerm]
        exact h

theorem cmp_sim {σ : Store} (hI : Inv sem σ) {a b : Id} (ha : a < σ.size) (hb : b < σ.size) :
    Sim sem σ (cmp a b) (__eo_cmp (σ.decode a) (σ.decode b)) := by
  unfold cmp
  by_cases ha0 : a = 0
  · simp only [ha0, true_or, ↓reduceIte]
    rw [decode_zero hI, __eo_cmp.eq_1]
    exact Sim.pure hI (size_pos hI) (decode_zero hI)
  by_cases hb0 : b = 0
  · simp only [hb0, or_true, ↓reduceIte]
    rw [decode_zero hI, __eo_cmp.eq_2 _ (ns hI ha ha0)]
    exact Sim.pure hI (size_pos hI) (decode_zero hI)
  simp only [ha0, hb0, or_self, ↓reduceIte]
  rw [__eo_cmp.eq_3 _ _ (ns hI ha ha0) (ns hI hb hb0)]
  apply Ok.withStore'
  refine (intern_sim hI (n := .Boolean _) (by simp [Node.children])).congr ?_
  simp only [Node.toTerm, cmpId_spec hI, native_tcmp]
  cases termCmp (σ.decode a) (σ.decode b) <;> rfl

/-! ## `__eo_list_concat_rec` -/
theorem sim_zero {σ : Store} (hI : Inv sem σ) {t : Term} (h : t = .Stuck) :
    Sim sem σ (pure 0) t :=
  Sim.pure hI (size_pos hI) (by rw [decode_zero hI, h])

theorem intern_app {σ σ1 : Store} (hI1 : Inv sem σ1) (hE : Extends σ σ1) {fx r : Id}
    (hfx : fx < σ.size) (hr : r < σ1.size) {t : Term}
    (ht : Term.Apply (σ.decode fx) (σ1.decode r) = t) :
    Sim sem σ1 (intern (.Apply fx r)) t := by
  refine (intern_sim hI1 (n := .Apply fx r)
    (by simp [Node.children, Nat.lt_of_lt_of_le hfx hE.size_le, hr])).congr ?_
  simp only [Node.toTerm]; rw [decode_extends hE fx hfx]; exact ht

theorem cell_head {σ : Store} (hI : Inv sem σ) {fx f x : Id} (hfx : σ.view fx = .Apply f x) :
    σ.decode fx = .Apply (σ.decode f) (σ.decode x) := by
  rw [decode_of_view hI hfx]; rfl

theorem app_ns {f x : Term} : Term.Apply f x = .Stuck → False := fun h => by cases h

/-- The end of a list walk: `Stuck` if the list is, or `r`. -/
theorem end_sim {σ : Store} (hI : Inv sem σ) {l r : Id} {t : Term} (hr : r < σ.size)
    (h0 : l = 0 → t = .Stuck) (h1 : l ≠ 0 → σ.decode r = t) :
    Sim sem σ (pure (if l = 0 then 0 else r)) t := by
  by_cases hl : l = 0
  · simp only [hl, ↓reduceIte]; exact sim_zero hI (h0 hl)
  · simp only [hl, ↓reduceIte]; exact Sim.pure hI hr (h1 hl)

theorem concatR_spec {z : Id} :
    ∀ (n : Nat) {σ : Store} {l : Id}, Inv sem σ → l < σ.size → z < σ.size → z ≠ 0 →
      Sim sem σ (concatR z n l) (__eo_list_concat_rec (σ.decode l) (σ.decode z))
  | 0, _, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, hI, hl, hz, hz0 => by
    have hZ := ns hI hz hz0
    unfold concatR
    apply Ok.withStore'
    have fin : (∀ F X Y, σ.decode l = .Apply (.Apply F X) Y → False) →
        Sim sem σ (pure (if l = 0 then 0 else z))
          (__eo_list_concat_rec (σ.decode l) (σ.decode z)) := fun hnc =>
      end_sim hI hz (fun h => by rw [h, decode_zero hI, __eo_list_concat_rec.eq_1]) fun h => by
        have hL := ns hI hl h
        symm; apply __eo_list_concat_rec.eq_4 <;> assumption
    split
    · rename_i fx y hv
      split
      · rename_i f x hfx
        obtain ⟨hfxv, hy, _, _⟩ := cell_valid hI hl hv hfx
        rw [cell_dec hI hv hfx, __eo_list_concat_rec.eq_3 _ _ _ _ hZ]
        apply Ok.bind
        apply Ok.mono (concatR_spec n hI hy hz hz0)
        intro r σ1 hp
        rw [← hp.dec]
        refine Ok.mono (P := Post sem σ1 _) ?_ (fun _ _ h => h.weaken hp.ext)
        by_cases hr0 : r = 0
        · simp only [hr0, ↓reduceIte]
          exact sim_zero hp.inv (by rw [decode_zero hp.inv, __eo_mk_apply.eq_2 _ app_ns])
        · simp only [hr0, ↓reduceIte]
          rw [__eo_mk_apply.eq_3 _ _ app_ns (ns hp.inv hp.valid hr0)]
          exact intern_app hp.inv hp.ext hfxv hp.valid (by rw [cell_head hI hfx])
      · rename_i hfx
        exact fin (not_cell_of_head hI hv fun f x h => hfx f x h)
    · rename_i hv
      exact fin (not_cell_of_view hI fun fx y h => hv fx y h)

theorem concat_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {l z : Id} (hl : l < σ.size)
    (hz : z < σ.size) :
    Sim sem σ (concat n l z) (__eo_list_concat_rec (σ.decode l) (σ.decode z)) := by
  unfold concat
  by_cases hz0 : z = 0
  · simp only [hz0, ↓reduceIte]
    refine sim_zero hI ?_
    rw [decode_zero hI]
    by_cases hl0 : l = 0
    · rw [hl0, decode_zero hI, __eo_list_concat_rec.eq_1]
    · rw [__eo_list_concat_rec.eq_2 _ (ns hI hl hl0)]
  · simp only [hz0, ↓reduceIte]
    exact concatR_spec n hI hl hz hz0

/-! ## `__eo_list_rev_rec` -/
theorem revR_spec :
    ∀ (n : Nat) {σ : Store} {l acc : Id}, Inv sem σ → l < σ.size → acc < σ.size → acc ≠ 0 →
      Sim sem σ (revR n l acc) (__eo_list_rev_rec (σ.decode l) (σ.decode acc))
  | 0, _, _, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, acc, hI, hl, hz, hz0 => by
    have hZ := ns hI hz hz0
    unfold revR
    apply Ok.withStore'
    have fin : (∀ F X Y, σ.decode l = .Apply (.Apply F X) Y → False) →
        Sim sem σ (pure (if l = 0 then 0 else acc))
          (__eo_list_rev_rec (σ.decode l) (σ.decode acc)) := fun hnc =>
      end_sim hI hz (fun h => by rw [h, decode_zero hI, __eo_list_rev_rec.eq_1]) fun h => by
        have hL := ns hI hl h
        symm; apply __eo_list_rev_rec.eq_4 <;> assumption
    split
    · rename_i fx y hv
      split
      · rename_i f x hfx
        obtain ⟨hfxv, hy, _, _⟩ := cell_valid hI hl hv hfx
        rw [cell_dec hI hv hfx, __eo_list_rev_rec.eq_3 _ _ _ _ hZ]
        apply Ok.bind
        apply Ok.mono (intern_app hI (Extends.refl σ) hfxv hz rfl)
        intro c σ1 hp
        refine Ok.mono (P := Post sem σ1 _) ?_ (fun _ _ h => h.weaken hp.ext)
        have hd := hp.dec
        rw [cell_head hI hfx] at hd
        rw [← hd, ← decode_extends hp.ext y hy]
        refine revR_spec n hp.inv (Nat.lt_of_lt_of_le hy hp.ext.size_le) hp.valid ?_
        intro h0
        rw [h0, decode_zero hp.inv] at hd; cases hd
      · rename_i hfx
        exact fin (not_cell_of_head hI hv fun f x h => hfx f x h)
    · rename_i hv
      exact fin (not_cell_of_view hI fun fx y h => hv fx y h)

theorem rev_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {l z : Id} (hl : l < σ.size)
    (hz : z < σ.size) :
    Sim sem σ (rev n l z) (__eo_list_rev_rec (σ.decode l) (σ.decode z)) := by
  unfold rev
  by_cases hz0 : z = 0
  · simp only [hz0, ↓reduceIte]
    refine sim_zero hI ?_
    rw [decode_zero hI]
    by_cases hl0 : l = 0
    · rw [hl0, decode_zero hI, __eo_list_rev_rec.eq_1]
    · rw [__eo_list_rev_rec.eq_2 _ (ns hI hl hl0)]
  · simp only [hz0, ↓reduceIte]
    exact revR_spec n hI hl hz hz0

/-! ## `__eo_get_elements_rec` -/
theorem elementsR_spec {k e : Id} :
    ∀ (n : Nat) {σ : Store} {l : Id}, Inv sem σ → l < σ.size → k < σ.size → e < σ.size →
      σ.decode k = .__eo_List_cons → σ.decode e = .__eo_List_nil →
      Sim sem σ (elementsR k e n l) (__eo_get_elements_rec (σ.decode l))
  | 0, _, _, _, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, hI, hl, hk, he, dk, de => by
    unfold elementsR
    apply Ok.withStore'
    have fin : (∀ F X Y, σ.decode l = .Apply (.Apply F X) Y → False) →
        Sim sem σ (pure (if l = 0 then 0 else e))
          (__eo_get_elements_rec (σ.decode l)) := fun hnc =>
      end_sim hI he (fun h => by rw [h, decode_zero hI, __eo_get_elements_rec.eq_1]) fun h => by
        have hL := ns hI hl h
        rw [de]; symm; apply __eo_get_elements_rec.eq_3 <;> assumption
    split
    · rename_i fx y hv
      split
      · rename_i f x hfx
        obtain ⟨_, hy, _, hx⟩ := cell_valid hI hl hv hfx
        rw [cell_dec hI hv hfx, __eo_get_elements_rec.eq_2]
        apply Ok.bind
        apply Ok.mono (elementsR_spec n hI hy hk he dk de)
        intro r σ1 hp
        rw [← hp.dec]
        refine Ok.mono (P := Post sem σ1 _) ?_ (fun _ _ h => h.weaken hp.ext)
        by_cases hr0 : r = 0
        · simp only [hr0, ↓reduceIte]
          exact sim_zero hp.inv (by rw [decode_zero hp.inv, __eo_mk_apply.eq_2 _ app_ns])
        · simp only [hr0, ↓reduceIte]
          rw [__eo_mk_apply.eq_3 _ _ app_ns (ns hp.inv hp.valid hr0)]
          apply Ok.bind
          apply Ok.mono (intern_app hp.inv hp.ext hk (Nat.lt_of_lt_of_le hx hp.ext.size_le) rfl)
          intro c σ2 hq
          refine Ok.mono (P := Post sem σ2 _) ?_ (fun _ _ h => h.weaken hq.ext)
          refine intern_app hq.inv (Extends.refl σ2) hq.valid
            (Nat.lt_of_lt_of_le hp.valid hq.ext.size_le) ?_
          rw [hq.dec, decode_extends hq.ext r hp.valid, dk, decode_extends hp.ext x hx]
      · rename_i hfx
        exact fin (not_cell_of_head hI hv fun f x h => hfx f x h)
    · rename_i hv
      exact fin (not_cell_of_view hI fun fx y h => hv fx y h)

theorem elements_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {l : Id} (hl : l < σ.size) :
    Sim sem σ (elements n l) (__eo_get_elements_rec (σ.decode l)) := by
  unfold elements
  apply Ok.bind
  apply Ok.mono (intern_sim hI (n := .__eo_List_cons) (by simp [Node.children]))
  intro k σ1 hp
  apply Ok.bind
  apply Ok.mono (intern_sim hp.inv (n := .__eo_List_nil) (by simp [Node.children]))
  intro e σ2 hq
  have hE := hp.ext.trans hq.ext
  refine Ok.mono (P := Post sem σ2 _) ?_ (fun _ _ h => h.weaken hE)
  rw [← decode_extends hE l hl]
  refine elementsR_spec n hq.inv (Nat.lt_of_lt_of_le hl hE.size_le)
    (Nat.lt_of_lt_of_le hp.valid hq.ext.size_le) hq.valid ?_ hq.dec
  rw [decode_extends hq.ext k hp.valid]; exact hp.dec

/-! ## `__eo_list_len_rec` -/
theorem lenR_spec :
    ∀ (n : Nat) {σ : Store} {l : Id} {i : Nat}, Inv sem σ → l < σ.size →
      Ok (lenR n l i) σ (fun r? σ' => σ' = σ ∧ match r? with
        | none => __eo_list_len_rec (σ.decode l) = .Stuck
        | some k => __eo_list_len_rec (σ.decode l) = .Numeral ((k : Int) - (i : Int)))
  | 0, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, i, hI, hl => by
    unfold lenR
    apply Ok.withStore'
    have fin : (∀ F X Y, σ.decode l = .Apply (.Apply F X) Y → False) →
        Ok (pure (if l = 0 then none else some i) : K (Option Nat)) σ (fun r? σ' => σ' = σ ∧ match r? with
        | none => __eo_list_len_rec (σ.decode l) = .Stuck
        | some k => __eo_list_len_rec (σ.decode l) = .Numeral ((k : Int) - (i : Int))) := fun hnc => by
      refine Ok.pure ⟨rfl, ?_⟩
      by_cases h : l = 0
      · simp only [h, ↓reduceIte]
        rw [decode_zero hI, __eo_list_len_rec.eq_1]
      · simp only [h, ↓reduceIte]
        have hL := ns hI hl h
        rw [Int.sub_self]
        apply __eo_list_len_rec.eq_3 <;> assumption
    split
    · rename_i fx y hv
      split
      · rename_i f x hfx
        obtain ⟨_, hy, _, _⟩ := cell_valid hI hl hv hfx
        apply Ok.mono (lenR_spec n (i := i + 1) hI hy)
        rintro r? σ' ⟨rfl, h⟩
        refine ⟨rfl, ?_⟩
        rw [cell_dec hI hv hfx, __eo_list_len_rec.eq_2]
        cases r? with
        | none => simp only at h ⊢; rw [h]; rfl
        | some k =>
          simp only at h ⊢
          rw [h, __eo_add.eq_1]
          have e : (1 : Int) + ((k : Int) - ((i + 1 : Nat) : Int)) = (k : Int) - (i : Int) := by omega
          exact congrArg Term.Numeral e
      · rename_i hfx
        exact fin (not_cell_of_head hI hv fun f x h => hfx f x h)
    · rename_i hv
      exact fin (not_cell_of_view hI fun fx y h => hv fx y h)

theorem intern_num {σ : Store} (hI : Inv sem σ) {i : Int} {t : Term} (h : t = .Numeral i) :
    Sim sem σ (intern (.Numeral i)) t :=
  (intern_sim hI (n := .Numeral i) (by simp [Node.children])).congr (by rw [h]; rfl)

theorem len_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {l : Id} (hl : l < σ.size) :
    Sim sem σ (len n l) (__eo_list_len_rec (σ.decode l)) := by
  unfold len
  apply Ok.bind
  apply Ok.mono (lenR_spec n (i := 0) hI hl)
  rintro r? σ' ⟨rfl, h⟩
  cases r? with
  | none => exact sim_zero hI h
  | some k => exact intern_num hI (by simpa using h)

/-! ## `__eo_list_nth_rec` -/
theorem nthR_spec :
    ∀ (n : Nat) {σ : Store} {l : Id} {i : Int}, Inv sem σ → l < σ.size →
      Sim sem σ (nthR n l i) (__eo_list_nth_rec (σ.decode l) (.Numeral i))
  | 0, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, i, hI, hl => by
    unfold nthR
    apply Ok.withStore'
    have hN : Term.Numeral i = .Stuck → False := fun h => by cases h
    have fin : (∀ F X Y, σ.decode l = .Apply (.Apply F X) Y → False) →
        Sim sem σ (pure 0) (__eo_list_nth_rec (σ.decode l) (.Numeral i)) := fun hnc =>
      sim_zero hI (by
        apply __eo_list_nth_rec.eq_4 <;>
          first | assumption | (intros; first | exact hnc _ _ _ (by assumption) | contradiction))
    split
    · rename_i fx y hv
      split
      · rename_i f x hfx
        obtain ⟨_, hy, _, hx⟩ := cell_valid hI hl hv hfx
        rw [cell_dec hI hv hfx]
        by_cases hi : i = 0
        · simp only [hi, ↓reduceIte]
          rw [__eo_list_nth_rec.eq_2]
          exact Sim.pure hI hx rfl
        · simp only [hi, ↓reduceIte]
          rw [__eo_list_nth_rec.eq_3 _ _ _ _ hN (fun h => by cases h; exact hi rfl),
            __eo_add.eq_1]
          exact nthR_spec n hI hy
      · rename_i hfx
        exact fin (not_cell_of_head hI hv fun f x h => hfx f x h)
    · rename_i hv
      exact fin (not_cell_of_view hI fun fx y h => hv fx y h)

theorem nth_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {l i : Id} (hl : l < σ.size) :
    Sim sem σ (nth n l i) (__eo_list_nth_rec (σ.decode l) (σ.decode i)) := by
  unfold nth
  apply Ok.withStore'
  split
  · rename_i j hj
    rw [decode_of_view hI hj]
    exact nthR_spec n hI hl
  · exact Sim.lift hI

/-! ## `__eo_list_find_rec` -/
theorem findR_spec {z : Id} :
    ∀ (n : Nat) {σ : Store} {l : Id} {i : Int}, Inv sem σ → l < σ.size → z < σ.size → z ≠ 0 →
      Ok (findR z n l i) σ (fun r? σ' => σ' = σ ∧ match r? with
        | none => __eo_list_find_rec (σ.decode l) (σ.decode z) (.Numeral i) = .Stuck
        | some k => __eo_list_find_rec (σ.decode l) (σ.decode z) (.Numeral i) = .Numeral k)
  | 0, _, _, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, i, hI, hl, hz, hz0 => by
    have hZ := ns hI hz hz0
    have hN : Term.Numeral i = .Stuck → False := fun h => by cases h
    unfold findR
    apply Ok.withStore'
    have fin : (∀ F X Y, σ.decode l = .Apply (.Apply F X) Y → False) →
        Ok (pure (if l = 0 then none else some (-1)) : K (Option Int)) σ (fun r? σ' => σ' = σ ∧ match r? with
        | none => __eo_list_find_rec (σ.decode l) (σ.decode z) (.Numeral i) = .Stuck
        | some k => __eo_list_find_rec (σ.decode l) (σ.decode z) (.Numeral i) = .Numeral k) := fun hnc => by
      refine Ok.pure ⟨rfl, ?_⟩
      by_cases h : l = 0
      · simp only [h, ↓reduceIte]
        rw [decode_zero hI, __eo_list_find_rec.eq_1]
      · simp only [h, ↓reduceIte]
        have hL := ns hI hl h
        apply __eo_list_find_rec.eq_5 <;> assumption
    split
    · rename_i fx y hv
      split
      · rename_i f x hfx
        obtain ⟨_, hy, _, hx⟩ := cell_valid hI hl hv hfx
        rw [cell_dec hI hv hfx, __eo_list_find_rec.eq_4 _ _ _ _ _ hZ hN]
        by_cases hx0 : x = 0
        · simp only [hx0, ↓reduceIte]
          refine Ok.pure ⟨rfl, ?_⟩
          simp only
          rw [decode_zero hI, __eo_eq.eq_1, ite_stuck']
        simp only [hx0, ↓reduceIte]
        rw [eo_eq_ids hI hx hz hx0 hz0]
        by_cases hxz : x = z
        · simp only [hxz, ↓reduceIte, decide_true, ite_true']
          exact Ok.pure ⟨rfl, rfl⟩
        · simp only [hxz, ↓reduceIte, decide_false, ite_false', __eo_add.eq_1]
          exact findR_spec n hI hy hz hz0
      · rename_i hfx
        exact fin (not_cell_of_head hI hv fun f x h => hfx f x h)
    · rename_i hv
      exact fin (not_cell_of_view hI fun fx y h => hv fx y h)

theorem findIdx_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {l z i : Id} (hl : l < σ.size)
    (hz : z < σ.size) :
    Sim sem σ (findIdx n l z i) (__eo_list_find_rec (σ.decode l) (σ.decode z) (σ.decode i)) := by
  unfold findIdx
  apply Ok.withStore'
  split
  · rename_i j hj
    rw [decode_of_view hI hj]
    by_cases hz0 : z = 0
    · simp only [hz0, ↓reduceIte]
      refine sim_zero hI ?_
      rw [decode_zero hI]
      by_cases hl0 : l = 0
      · rw [hl0, decode_zero hI, __eo_list_find_rec.eq_1]
      · rw [__eo_list_find_rec.eq_2 _ _ (ns hI hl hl0)]
    · simp only [hz0, ↓reduceIte]
      apply Ok.bind
      apply Ok.mono (findR_spec n (i := j) hI hl hz hz0)
      rintro r? σ' ⟨rfl, h⟩
      cases r? with
      | none => exact sim_zero hI h
      | some k => exact intern_num hI h
  · exact Sim.lift hI

/-! ## `__eo_list_minclude_rec` -/
theorem not_bool (b : Bool) : __eo_not (.Boolean b) = .Boolean (!b) := by
  rw [__eo_not.eq_1]; rfl
theorem not_stuck : __eo_not .Stuck = .Stuck := by simp [__eo_not]

theorem mincludeR_spec :
    ∀ (n : Nat) {σ : Store} {y z : Id}, Inv sem σ → y < σ.size → z < σ.size → y ≠ 0 →
      Sim sem σ (mincludeR n y z)
        (__eo_list_minclude_rec (σ.decode y) (σ.decode z) (.Boolean true))
  | 0, _, _, _, _, _, _, _ => Ok.throw
  | n + 1, σ, y, z, hI, hy, hz, hy0 => by
    have hY := ns hI hy hy0
    unfold mincludeR
    apply Ok.withStore'
    have hT : Term.Boolean true = .Stuck → False := fun h => by cases h
    have fin : (∀ X Z, σ.decode z = .Apply (.Apply .__eo_List_cons X) Z → False) →
        (σ.decode z = .__eo_List_nil → False) →
        Sim sem σ (pure 0) (__eo_list_minclude_rec (σ.decode y) (σ.decode z) (.Boolean true)) := by
      intro h1 h2
      refine sim_zero hI ?_
      by_cases hz0 : z = 0
      · rw [hz0, decode_zero hI, __eo_list_minclude_rec.eq_2 _ _ hY]
      · have hZ := ns hI hz hz0
        apply __eo_list_minclude_rec.eq_6 <;>
          first
          | assumption
          | (intros; first
              | contradiction
              | exact h1 _ _ (by assumption)
              | exact h2 (by assumption))
    split
    · rename_i cx z' hv
      have hnil : σ.decode z = .__eo_List_nil → False := fun h => by
        rw [decode_of_view hI hv] at h; cases h
      split
      · rename_i c x hcx
        split
        · rename_i hc
          obtain ⟨_, hz', _, hx⟩ := cell_valid hI hz hv hcx
          have dc : σ.decode c = .__eo_List_cons := by rw [decode_of_view hI hc]; rfl
          rw [cell_dec hI hv hcx, dc, __eo_list_minclude_rec.eq_4 _ _ _ hY]
          apply Ok.bind
          apply Ok.mono (erase_sim (n := n) hI hy hx)
          intro v σ1 hp
          refine Ok.mono (P := Post sem σ1 _) ?_ (fun _ _ h => h.weaken hp.ext)
          rw [← hp.dec]
          by_cases hv0 : v = 0
          · simp only [hv0, true_or, ↓reduceIte]
            exact sim_zero hp.inv (by rw [decode_zero hp.inv, __eo_list_minclude_rec.eq_1])
          have hV := ns hp.inv hp.valid hv0
          by_cases hz0 : z' = 0
          · simp only [hz0, or_true, ↓reduceIte]
            exact sim_zero hp.inv (by rw [decode_zero hI, __eo_list_minclude_rec.eq_2 _ _ hV])
          simp only [hv0, hz0, or_self, ↓reduceIte]
          have hz1 := Nat.lt_of_lt_of_le hz' hp.ext.size_le
          have hy1 := Nat.lt_of_lt_of_le hy hp.ext.size_le
          rw [← decode_extends hp.ext y hy, ← decode_extends hp.ext z' hz',
            eo_eq_ids hp.inv hp.valid hy1 hv0 hy0, not_bool]
          by_cases hvy : v = y
          · simp only [hvy, ↓reduceIte, decide_true, Bool.not_true]
            refine bool_sim hp.inv false ?_
            rw [hvy] at hV
            exact __eo_list_minclude_rec.eq_3 _ _ hV (ns hp.inv hz1 hz0)
          · simp only [hvy, ↓reduceIte, decide_false, Bool.not_false]
            exact mincludeR_spec n hp.inv hp.valid hz1 hv0
        · rename_i hc
          refine fin (fun X Z h => ?_) hnil
          rw [cell_dec hI hv hcx] at h
          simp only [Term.Apply.injEq] at h
          exact hc (decode_leaf_inv hI (n := .__eo_List_cons) rfl (d := fun _ => .Stuck) h.1.1)
      · rename_i hcx
        exact fin (fun X Z h => not_cell_of_head hI hv (fun f x h => hcx f x h) _ _ _ h) hnil
    · rename_i hv
      have dz : σ.decode z = .__eo_List_nil := by rw [decode_of_view hI hv]; rfl
      rw [dz, __eo_list_minclude_rec.eq_5 _ hY]
      exact bool_sim hI true rfl
    · rename_i hv1 hv2
      refine fin (fun X Z h => not_cell_of_view hI (fun f x h => hv1 f x h) _ _ _ h) (fun h => ?_)
      exact hv2 (decode_leaf_inv hI (n := .__eo_List_nil) rfl (d := fun _ => .Stuck) h)

theorem minclude_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {y z b : Id} (hy : y < σ.size)
    (hz : z < σ.size) :
    Sim sem σ (minclude n y z b)
      (__eo_list_minclude_rec (σ.decode y) (σ.decode z) (σ.decode b)) := by
  unfold minclude
  by_cases hy0 : y = 0
  · simp only [hy0, true_or, ↓reduceIte]
    exact sim_zero hI (by rw [decode_zero hI, __eo_list_minclude_rec.eq_1])
  have hY := ns hI hy hy0
  by_cases hz0 : z = 0
  · simp only [hz0, or_true, ↓reduceIte]
    exact sim_zero hI (by rw [decode_zero hI, __eo_list_minclude_rec.eq_2 _ _ hY])
  have hZ := ns hI hz hz0
  simp only [hy0, hz0, or_self, ↓reduceIte]
  by_cases hb1 : b = 1
  · simp only [hb1, ↓reduceIte]
    have : σ.decode 1 = .Boolean true := by
      exact decode_of_view hI ((view_bool_iff (b := true) hI).mpr rfl)
    rw [this]
    exact mincludeR_spec n hI hy hz hy0
  by_cases hb2 : b = 2
  · simp only [hb2, ↓reduceIte]
    have : σ.decode 2 = .Boolean false := by
      exact decode_of_view hI ((view_bool_iff (b := false) hI).mpr rfl)
    rw [this]
    exact bool_sim hI false (__eo_list_minclude_rec.eq_3 _ _ hY hZ)
  simp only [hb1, hb2, ↓reduceIte]
  refine sim_zero hI ?_
  have h1 : σ.decode b = .Boolean true → False := fun h => hb1
    ((view_bool_iff (b := true) hI).mp
      (decode_leaf_inv hI (n := .Boolean true) rfl (d := fun _ => .Stuck) h))
  have h2 : σ.decode b = .Boolean false → False := fun h => hb2
    ((view_bool_iff (b := false) hI).mp
      (decode_leaf_inv hI (n := .Boolean false) rfl (d := fun _ => .Stuck) h))
  apply __eo_list_minclude_rec.eq_6 <;>
    first
    | assumption
    | (intros; first | exact h1 (by assumption) | exact h2 (by assumption))

/-! ## `__eo_list_inter_rec` -/
theorem interR_spec :
    ∀ (n : Nat) {σ : Store} {l b : Id}, Inv sem σ → l < σ.size → b < σ.size →
      Ok (interR n l b) σ (OPost sem σ l (__eo_list_inter_rec (σ.decode l) (σ.decode b)))
  | 0, _, _, _, _, _, _ => Ok.throw
  | n + 1, σ, l, b, hI, hl, hb => by
    unfold interR
    apply Ok.withStore'
    by_cases hb0 : b = 0
    · simp only [hb0, ↓reduceIte]
      subst hb0
      rw [decode_zero hI]
      by_cases hl0 : l = 0
      · subst hl0; rw [decode_zero hI, __eo_list_inter_rec.eq_1]
        exact Ok.pure (OPost.some_zero hI)
      · rw [__eo_list_inter_rec.eq_2 _ (ns hI hl hl0)]
        exact Ok.pure (OPost.some_zero hI)
    simp only [hb0, ↓reduceIte]
    have hB := ns hI hb hb0
    split
    · rename_i fx y hv
      split
      · rename_i f x hfx
        obtain ⟨hfxv, hy, hf, hx⟩ := cell_valid hI hl hv hfx
        rw [cell_dec hI hv hfx, __eo_list_inter_rec.eq_3 _ _ _ _ hB]
        by_cases hfx0 : f = 0 ∨ x = 0
        · simp only [hfx0, ↓reduceIte]
          by_cases hf0 : f = 0
          · subst hf0; rw [decode_zero hI, __eo_prepend_if.eq_1]
            exact Ok.pure (OPost.some_zero hI)
          · have hx0 : x = 0 := hfx0.resolve_left hf0
            subst hx0; rw [decode_zero hI, __eo_prepend_if.eq_2 _ _ _ (ns hI hf hf0)]
            exact Ok.pure (OPost.some_zero hI)
        · simp only [hfx0, ↓reduceIte]
          have hf0 : f ≠ 0 := fun e => hfx0 (.inl e)
          have hx0 : x ≠ 0 := fun e => hfx0 (.inr e)
          have hF := ns hI hf hf0
          have hX := ns hI hx hx0
          apply Ok.bind
          apply Ok.mono (erase_sim (n := n) hI hb hx)
          intro v σ1 ⟨hI1, hE1, hvv, hvd⟩
          rw [← hvd]
          by_cases hv0 : v = 0
          · simp only [hv0, ↓reduceIte]
            subst hv0
            rw [decode_zero hI1, __eo_eq.eq_1, not_stuck]
            have : __eo_list_inter_rec (σ.decode y) .Stuck = .Stuck := by
              by_cases hy0 : y = 0
              · subst hy0; rw [decode_zero hI, __eo_list_inter_rec.eq_1]
              · rw [__eo_list_inter_rec.eq_2 _ (ns hI hy hy0)]
            rw [this, __eo_prepend_if.eq_3 _ _ _ hF hX]
            exact Ok.pure ⟨hI1, hE1, size_pos hI1, decode_zero hI1⟩
          · simp only [hv0, ↓reduceIte]
            have hy1 := Nat.lt_of_lt_of_le hy hE1.size_le
            have hb1 := Nat.lt_of_lt_of_le hb hE1.size_le
            apply Ok.bind
            apply Ok.mono (interR_spec n hI1 hy1 hvv)
            intro r? σ2 hp
            obtain ⟨hI2, hE2, hresv, hresd⟩ := hp.getD hy1
            rw [decode_extends hE1 y hy] at hresd
            have hE12 := hE1.trans hE2
            rw [← decode_extends hE1 b hb, eo_eq_ids hI1 hvv hb1 hv0 hb0, not_bool]
            by_cases hres0 : r?.getD y = 0
            · simp only [hres0, ↓reduceIte]
              rw [hres0, decode_zero hI2] at hresd
              rw [← hresd, __eo_prepend_if.eq_3 _ _ _ hF hX]
              exact Ok.pure ⟨hI2, hE12, size_pos hI2, decode_zero hI2⟩
            · simp only [hres0, ↓reduceIte]
              have hR := ns hI2 hresv hres0
              by_cases hvb : v = b
              · simp only [hvb, ↓reduceIte, decide_true, Bool.not_true]
                rw [hvb] at hresd
                rw [← hresd, __eo_prepend_if.eq_5 _ _ _ hF hX hR]
                exact Ok.pure ⟨hI2, hE12, hresv, rfl⟩
              · simp only [hvb, ↓reduceIte, decide_false, Bool.not_false]
                rw [← hresd, __eo_prepend_if.eq_4 _ _ _ hF hX hR]
                cases r? with
                | none =>
                  refine Ok.pure ⟨hI2, hE12, ?_, ne_zero_of_app hI hv⟩
                  simp only [Option.getD_none] at hresd ⊢
                  rw [cell_dec hI hv hfx, decode_extends hE12 y hy]
                | some r =>
                  simp only [Option.getD_some] at hresv ⊢
                  refine intern_cell hI2 hE12 hfxv hresv ?_
                  rw [decode_of_view hI hfx]; rfl
      · rename_i hfx
        have hl0 := ne_zero_of_app hI hv
        simp only [hl0, ↓reduceIte]
        refine Ok.pure (OPost.none_of hI ?_ hl0)
        rw [__eo_list_inter_rec.eq_4 _ _ (ns hI hl hl0)
          (not_cell_of_head hI hv fun f x h => hfx f x h) hB]
    · rename_i hv
      by_cases hl0 : l = 0
      · simp only [hl0, ↓reduceIte]
        subst hl0
        rw [decode_zero hI, __eo_list_inter_rec.eq_1]
        exact Ok.pure (OPost.some_zero hI)
      · simp only [hl0, ↓reduceIte]
        refine Ok.pure (OPost.none_of hI ?_ hl0)
        rw [__eo_list_inter_rec.eq_4 _ _ (ns hI hl hl0)
          (not_cell_of_view hI fun fx y h => hv fx y h) hB]

theorem inter_sim {n : Nat} {σ : Store} (hI : Inv sem σ) {l b : Id} (hl : l < σ.size)
    (hb : b < σ.size) :
    Sim sem σ (inter n l b) (__eo_list_inter_rec (σ.decode l) (σ.decode b)) := by
  unfold inter
  apply Ok.bind
  apply Ok.mono (interR_spec n hI hl hb)
  intro r? σ1 hp
  have := hp.sim hl
  cases r? <;> exact Ok.pure this

/-! ## `__eo_list_repeat_rec` -/
theorem repeatR_spec {fa e : Id} {F A E : Term} (hF : F = .Stuck → False)
    (hA : A = .Stuck → False) (hE : __eo_nil F (__eo_typeof A) = E) :
    ∀ (i : Nat) {σ : Store}, Inv sem σ → fa < σ.size → e < σ.size →
      σ.decode fa = .Apply F A → σ.decode e = E →
      Sim sem σ (repeatR fa e i) (__eo_list_repeat_rec F A i)
  | 0, σ, hI, hfa, he, dfa, de => by
    have : __eo_list_repeat_rec F A 0 = E := by
      rw [← hE]
      apply __eo_list_repeat_rec.eq_4 <;>
        first | assumption | (intro n h; cases h)
    rw [this]
    exact Sim.pure hI he de
  | i + 1, σ, hI, hfa, he, dfa, de => by
    have : __eo_list_repeat_rec F A (i + 1)
        = __eo_mk_apply (.Apply F A) (__eo_list_repeat_rec F A i) :=
      __eo_list_repeat_rec.eq_3 _ _ _ hF hA
    rw [this]
    unfold repeatR
    apply Ok.bind
    apply Ok.mono (repeatR_spec hF hA hE i hI hfa he dfa de)
    intro r σ1 hp
    rw [← hp.dec]
    refine Ok.mono (P := Post sem σ1 _) ?_ (fun _ _ h => h.weaken hp.ext)
    by_cases hr0 : r = 0
    · simp only [hr0, ↓reduceIte]
      exact sim_zero hp.inv (by rw [decode_zero hp.inv, __eo_mk_apply.eq_2 _ app_ns])
    · simp only [hr0, ↓reduceIte]
      rw [__eo_mk_apply.eq_3 _ _ app_ns (ns hp.inv hp.valid hr0)]
      exact intern_app hp.inv hp.ext hfa hp.valid (by rw [dfa])

theorem rep_sim {typeOf : Id → K Id} {nilOf : Id → Id → K Id}
    (hT : ∀ {σ : Store} {a : Id}, Inv sem σ → a < σ.size →
      Sim sem σ (typeOf a) (__eo_typeof (σ.decode a)))
    (hN : ∀ {σ : Store} {a b : Id}, Inv sem σ → a < σ.size → b < σ.size →
      Sim sem σ (nilOf a b) (__eo_nil (σ.decode a) (σ.decode b)))
    {σ : Store} (hI : Inv sem σ) {f a : Id} {i : Nat} (hf : f < σ.size) (ha : a < σ.size) :
    Sim sem σ (rep typeOf nilOf f a i) (__eo_list_repeat_rec (σ.decode f) (σ.decode a) i) := by
  unfold rep
  by_cases hf0 : f = 0
  · simp only [hf0, true_or, ↓reduceIte]
    exact sim_zero hI (by rw [decode_zero hI, __eo_list_repeat_rec.eq_1])
  have hF := ns hI hf hf0
  by_cases ha0 : a = 0
  · simp only [ha0, or_true, ↓reduceIte]
    exact sim_zero hI (by rw [decode_zero hI, __eo_list_repeat_rec.eq_2 _ _ hF])
  have hA := ns hI ha ha0
  simp only [hf0, ha0, or_self, ↓reduceIte]
  apply Ok.bind
  apply Ok.mono (hT hI ha)
  intro t σ1 hp
  apply Ok.bind
  apply Ok.mono (hN hp.inv (Nat.lt_of_lt_of_le hf hp.ext.size_le) hp.valid)
  intro e σ2 hq
  have h12 := hp.ext.trans hq.ext
  apply Ok.bind
  apply Ok.mono (intern_app hq.inv h12 hf (Nat.lt_of_lt_of_le ha h12.size_le) rfl)
  intro fa σ3 hr
  have h13 := h12.trans hr.ext
  refine Ok.mono (P := Post sem σ3 _) ?_ (fun _ _ h => h.weaken h13)
  refine repeatR_spec hF hA rfl i hr.inv hr.valid
    (Nat.lt_of_lt_of_le hq.valid hr.ext.size_le) ?_ ?_
  · rw [hr.dec, decode_extends h12 a ha]
  · rw [decode_extends hr.ext e hq.valid, hq.dec, hp.dec, decode_extends hp.ext f hf]

/-! ## Small builtins -/
theorem mkApply_sim {σ : Store} (hI : Inv sem σ) {f x : Id} (hf : f < σ.size) (hx : x < σ.size) :
    Sim sem σ (mkApply f x) (__eo_mk_apply (σ.decode f) (σ.decode x)) := by
  unfold mkApply
  by_cases hf0 : f = 0
  · simp only [hf0, true_or, ↓reduceIte]
    exact sim_zero hI (by rw [decode_zero hI, __eo_mk_apply.eq_1])
  have hF := ns hI hf hf0
  by_cases hx0 : x = 0
  · simp only [hx0, or_true, ↓reduceIte]
    exact sim_zero hI (by rw [decode_zero hI, __eo_mk_apply.eq_2 _ hF])
  simp only [hf0, hx0, or_self, ↓reduceIte]
  rw [__eo_mk_apply.eq_3 _ _ hF (ns hI hx hx0)]
  exact intern_app hI (Extends.refl σ) hf hx rfl

theorem eq_sim {σ : Store} (hI : Inv sem σ) {a b : Id} (ha : a < σ.size) (hb : b < σ.size) :
    Sim sem σ (eq a b) (__eo_eq (σ.decode a) (σ.decode b)) := by
  unfold eq
  by_cases ha0 : a = 0
  · simp only [ha0, true_or, ↓reduceIte]
    exact sim_zero hI (by rw [decode_zero hI, __eo_eq.eq_1])
  by_cases hb0 : b = 0
  · simp only [hb0, or_true, ↓reduceIte]
    exact sim_zero hI (by rw [decode_zero hI, __eo_eq.eq_2 _ (ns hI ha ha0)])
  simp only [ha0, hb0, or_self, ↓reduceIte]
  rw [eo_eq_ids hI ha hb ha0 hb0]
  by_cases h : b = a
  · simp only [h, ↓reduceIte, decide_true]; exact bool_sim hI true rfl
  · simp only [h, Ne.symm h, ↓reduceIte, decide_false]; exact bool_sim hI false rfl

theorem requires_sim {σ : Store} (hI : Inv sem σ) {a b c : Id} (ha : a < σ.size)
    (hb : b < σ.size) (hc : c < σ.size) :
    Sim sem σ (requires a b c) (__eo_requires (σ.decode a) (σ.decode b) (σ.decode c)) := by
  unfold requires
  by_cases hab : a = b
  · subst hab
    by_cases ha0 : a = 0
    · simp only [ha0, ne_eq, not_true_eq_false, and_false, ↓reduceIte]
      refine sim_zero hI ?_
      simp [decode_zero hI, __eo_requires, native_ite, native_teq, native_not]
    · simp only [ha0, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      rw [requires_self (ns hI ha ha0)]
      exact Sim.pure hI hc rfl
  · simp only [hab, false_and, ↓reduceIte]
    exact sim_zero hI (requires_ne fun e => hab ((dec_eq_iff hI ha hb).mp e))

theorem isOk_sim {σ : Store} (hI : Inv sem σ) {a : Id} (ha : a < σ.size) :
    Sim sem σ (isOk a) (__eo_is_ok (σ.decode a)) := by
  unfold isOk
  by_cases ha0 : a = 0
  · simp only [ha0, ↓reduceIte]
    exact bool_sim hI false (by rw [decode_zero hI, is_ok_stuck])
  · simp only [ha0, ↓reduceIte]
    exact bool_sim hI true (is_ok_of (ns hI ha ha0))

end Kairos.Native
