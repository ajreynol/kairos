/-
Pattern-matching primitives and their lemmas.

A generated matcher is a chain of primitives in continuation-passing style:
`leaf` and `stuck` here, and one per constructor of `Term`, generated
(Kairos/Gen/Prims.lean). Generated proofs take a chain apart one
step at a time with the `_some` lemmas, run it on a known shape with the
`_of_view` lemmas, and invert a decoded shape with the `_inv` lemmas. Under the invariant, none of these needs the id to be
valid: an id outside the store reads as `Stuck` and views as `stuck`.
-/
import Kairos.Runtime.Match
import KairosVerification.Runtime.Ctx

namespace Kairos
open Eo Store

variable {sem : Sem} {σ : Store}

namespace Store
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
/-- `leaf` is a test of the view, however it is made. -/
theorem leaf_eq {α : Type} {x : Id} {n : Node} {k : Option α} :
    σ.leaf x n k = if σ.view x = n then k else none := by
  unfold leaf
  split
  · cases σ.view x <;> simp
  · cases σ.view x <;> simp
  · rfl

theorem leaf_some {α : Type} {x : Id} {n : Node} {k : Option α} {r : α}
    (h : σ.leaf x n k = some r) : σ.view x = n ∧ k = some r := by
  rw [leaf_eq] at h; split at h
  · rename_i hb; exact ⟨hb, h⟩
  · simp at h

theorem kguard_some {α : Type} {c : Prop} [Decidable c] {k : Option α} {r : α}
    (h : kguard c k = some r) : c ∧ k = some r := by
  unfold kguard at h; split at h
  · rename_i hc; exact ⟨hc, h⟩
  · simp at h

theorem stuck_some {α : Type} {x : Id} {k : Option α} {r : α}
    (h : Store.stuck x k = some r) : x = 0 ∧ k = some r := by
  unfold Store.stuck at h; split at h
  · rename_i hb; exact ⟨hb, h⟩
  · simp at h

/-! ## Running a matcher chain on a known shape (the `_none` direction) -/
theorem leaf_of_view {α : Type} {x : Id} {n : Node} {k : Option α}
    (hv : σ.view x = n) : σ.leaf x n k = k := by simp [leaf_eq, hv]

theorem stuck_of_zero {α : Type} {k : Option α} : Store.stuck 0 k = k := by simp [Store.stuck]

/-! ## Inverting a decoded shape -/
theorem decode_leaf_inv (hI : Inv sem σ) {x : Id} {n : Node} (hn : n.children = [])
    {d : Id → Term} (h : σ.decode x = n.toTerm d) : σ.view x = n := by
  rw [decode_view' hI x] at h
  have : n.toTerm d = n.toTerm σ.decode := Node.toTerm_congr n (by simp [hn])
  rw [this] at h
  exact Node.toTerm_inj _ _ (by simp [hn]) h

theorem decode_stuck_inv (hI : Inv sem σ) {x : Id} (hx : x < σ.size)
    (h : σ.decode x = .Stuck) : x = 0 :=
  (decode_eq_stuck_iff hI hx).mp h

theorem stuck_iff (hI : Inv sem σ) {x : Id} (hx : x < σ.size) : σ.decode x = .Stuck ↔ x = 0 :=
  decode_eq_stuck_iff hI hx

end Kairos
