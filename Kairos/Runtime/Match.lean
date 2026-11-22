/-
Pattern-matching primitives and their lemmas.

A generated matcher is a chain of these primitives in continuation-passing
style (`app`, `leaf`, `var`, ...). Generated proofs take a chain apart one
step at a time with the `_some` lemmas, run it on a known shape with the
`_of_view` lemmas, and invert a decoded shape with the `_inv` lemmas. Under the invariant, none of these needs the id to be
valid: an id outside the store reads as `Stuck` and views as `stuck`.
-/
import Kairos.Runtime.Ctx

namespace Kairos
open Eo Store

variable {sem : Sem} {σ : Store}

namespace Store

/-! Matcher steps, in continuation-passing style: each takes an id apart and
hands its parts to the rest of the matcher. They inline to nested matches. -/

@[inline] def app {α : Type} (σ : Store) (x : Id) (k : Id → Id → Option α) : Option α :=
  match σ.view x with
  | .Apply f y => k f y
  | _ => none

@[inline] def leaf {α : Type} (σ : Store) (x : Id) (n : Node) (k : Option α) : Option α :=
  if σ.view x = n then k else none

@[inline] def var {α : Type} (σ : Store) (x : Id) (k : Id → Id → Option α) : Option α :=
  match σ.view x with
  | .Var s T => k s T
  | _ => none

@[inline] def boolean {α : Type} (σ : Store) (x : Id) (k : Bool → Option α) : Option α :=
  match σ.view x with
  | .Boolean b => k b
  | _ => none

@[inline] def binary {α : Type} (σ : Store) (x : Id) (k : Int → Int → Option α) : Option α :=
  match σ.view x with
  | .Binary w n => k w n
  | _ => none

/-- The `Stuck` pattern, which is id 0. -/
@[inline] def stuck {α : Type} (x : Id) (k : Option α) : Option α :=
  if x = 0 then k else none

end Store

theorem view_out {x : Id} (hx : ¬ x < σ.size) : σ.view x = .Stuck := by
  simp [view, Array.getElem?_eq_none (Nat.le_of_not_lt hx)]

theorem decode_out {x : Id} (hx : ¬ x < σ.size) : σ.decode x = .Stuck := by
  rw [decode_unfold, Array.getElem?_eq_none (Nat.le_of_not_lt hx)]

/-- An id reads as its view, valid or not. -/
theorem decode_view' (hI : Inv sem σ) (x : Id) : σ.decode x = (σ.view x).toTerm σ.decode := by
  by_cases hx : x < σ.size
  · exact decode_view hI hx
  · rw [decode_out hx, view_out hx]; rfl

theorem decode_of_view (hI : Inv sem σ) {x : Id} {n : Node} (hv : σ.view x = n) :
    σ.decode x = n.toTerm σ.decode := by
  rw [decode_view' hI x, hv]

/-- The children of a valid id are valid. -/
theorem valid_of_view (hI : Inv sem σ) {x : Id} (hx : x < σ.size) {n : Node}
    (hv : σ.view x = n) {j : Id} (hj : j ∈ n.children) : j < σ.size :=
  child_valid hI hx (hv ▸ hj)

theorem valid_of_app (hI : Inv sem σ) {x f y : Id} (hx : x < σ.size)
    (hv : σ.view x = .Apply f y) : f < σ.size ∧ y < σ.size :=
  ⟨valid_of_view hI hx hv (by simp [Node.children]),
   valid_of_view hI hx hv (by simp [Node.children])⟩

/-! ## Taking a matcher chain apart (the `_some` direction) -/

theorem app_some {α : Type} {x : Id} {k : Id → Id → Option α} {r : α}
    (h : σ.app x k = some r) : ∃ f y, σ.view x = .Apply f y ∧ k f y = some r := by
  unfold app at h; split at h
  · rename_i f y hv; exact ⟨f, y, hv, h⟩
  · simp at h

theorem leaf_some {α : Type} {x : Id} {n : Node} {k : Option α} {r : α}
    (h : σ.leaf x n k = some r) : σ.view x = n ∧ k = some r := by
  unfold leaf at h; split at h
  · rename_i hb; exact ⟨hb, h⟩
  · simp at h

theorem var_some {α : Type} {x : Id} {k : Id → Id → Option α} {r : α}
    (h : σ.var x k = some r) : ∃ s T, σ.view x = .Var s T ∧ k s T = some r := by
  unfold var at h; split at h
  · rename_i s T hv; exact ⟨s, T, hv, h⟩
  · simp at h

theorem boolean_some {α : Type} {x : Id} {k : Bool → Option α} {r : α}
    (h : σ.boolean x k = some r) : ∃ b, σ.view x = .Boolean b ∧ k b = some r := by
  unfold boolean at h; split at h
  · rename_i b hv; exact ⟨b, hv, h⟩
  · simp at h

theorem binary_some {α : Type} {x : Id} {k : Int → Int → Option α} {r : α}
    (h : σ.binary x k = some r) : ∃ w n, σ.view x = .Binary w n ∧ k w n = some r := by
  unfold binary at h; split at h
  · rename_i w n hv; exact ⟨w, n, hv, h⟩
  · simp at h

theorem stuck_some {α : Type} {x : Id} {k : Option α} {r : α}
    (h : Store.stuck x k = some r) : x = 0 ∧ k = some r := by
  unfold Store.stuck at h; split at h
  · rename_i hb; exact ⟨hb, h⟩
  · simp at h

/-! ## Running a matcher chain on a known shape (the `_none` direction) -/

theorem app_of_view {α : Type} {x f y : Id} {k : Id → Id → Option α}
    (hv : σ.view x = .Apply f y) : σ.app x k = k f y := by simp [app, hv]

theorem leaf_of_view {α : Type} {x : Id} {n : Node} {k : Option α}
    (hv : σ.view x = n) : σ.leaf x n k = k := by simp [leaf, hv]

theorem var_of_view {α : Type} {x s T : Id} {k : Id → Id → Option α}
    (hv : σ.view x = .Var s T) : σ.var x k = k s T := by simp [var, hv]

theorem boolean_of_view {α : Type} {x : Id} {b : Bool} {k : Bool → Option α}
    (hv : σ.view x = .Boolean b) : σ.boolean x k = k b := by simp [boolean, hv]

theorem binary_of_view {α : Type} {x : Id} {w n : Int} {k : Int → Int → Option α}
    (hv : σ.view x = .Binary w n) : σ.binary x k = k w n := by simp [binary, hv]

theorem stuck_of_zero {α : Type} {k : Option α} : Store.stuck 0 k = k := by simp [Store.stuck]

/-! ## Inverting a decoded shape -/

theorem decode_apply_inv (hI : Inv sem σ) {x : Id} {A B : Term}
    (h : σ.decode x = .Apply A B) :
    ∃ f y, σ.view x = .Apply f y ∧ σ.decode f = A ∧ σ.decode y = B := by
  rw [decode_view' hI x] at h
  cases hv : σ.view x <;> simp [hv, Node.toTerm] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem decode_leaf_inv (hI : Inv sem σ) {x : Id} {n : Node} (hn : n.children = [])
    {d : Id → Term} (h : σ.decode x = n.toTerm d) : σ.view x = n := by
  rw [decode_view' hI x] at h
  have : n.toTerm d = n.toTerm σ.decode := Node.toTerm_congr n (by simp [hn])
  rw [this] at h
  exact Node.toTerm_inj _ _ (by simp [hn]) h

theorem decode_var_inv (hI : Inv sem σ) {x : Id} {S T : Term}
    (h : σ.decode x = .Var S T) :
    ∃ s t, σ.view x = .Var s t ∧ σ.decode s = S ∧ σ.decode t = T := by
  rw [decode_view' hI x] at h
  cases hv : σ.view x <;> simp [hv, Node.toTerm] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem decode_boolean_inv (hI : Inv sem σ) {x : Id} {b : Bool}
    (h : σ.decode x = .Boolean b) : σ.view x = .Boolean b := by
  rw [decode_view' hI x] at h
  cases hv : σ.view x <;> simp [hv, Node.toTerm] at h
  simp [h]

theorem decode_binary_inv (hI : Inv sem σ) {x : Id} {w n : Int}
    (h : σ.decode x = .Binary w n) : σ.view x = .Binary w n := by
  rw [decode_view' hI x] at h
  cases hv : σ.view x <;> simp [hv, Node.toTerm] at h
  simp [h]

theorem decode_stuck_inv (hI : Inv sem σ) {x : Id} (hx : x < σ.size)
    (h : σ.decode x = .Stuck) : x = 0 :=
  (decode_eq_stuck_iff hI hx).mp h

theorem stuck_iff (hI : Inv sem σ) {x : Id} (hx : x < σ.size) : σ.decode x = .Stuck ↔ x = 0 :=
  decode_eq_stuck_iff hI hx

end Kairos
