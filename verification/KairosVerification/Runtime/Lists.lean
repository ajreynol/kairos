/-
Proofs of the native list operations (`Kairos/Runtime/Lists.lean`): each
computes Logos's function on the decoded arguments. They are stated against
Logos's definitions (`__eo_list_erase_rec` and the others), so a change to
those breaks this file, not the checker.
-/
import Kairos.Runtime.Lists
import KairosVerification.Gen.Prims

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

end Kairos.Native
