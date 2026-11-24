/-
The Kairos core: the store, reading ids back as Logos terms, and the store
invariant.

* A term is an `Id` into a hash-consed `Store`: `nodes[i]` is one level of a
  Logos `Term` whose `Term` children are `Id`s smaller than `i`. `Node` is
  generated from Logos's `Term` (Kairos/Gen/Term.lean).
* `decode` reads an `Id` back as Logos's `Term`. It is a specification
  function only; the checker never runs it.
* `Inv` is the store invariant: id 0 is `Stuck`, children precede parents, and
  the interning table is exact (so equal ids ⇔ equal terms).
-/
import Kairos.Runtime.Monad
import KairosVerification.Gen.Term

namespace Kairos
open Eo
namespace Store
@[simp] theorem decode_with_cache (σ : Store) (c : Std.HashMap (Nat × List Id) Id) :
    ({ σ with cache := c } : Store).decode = σ.decode := rfl

@[simp] theorem size_with_cache (σ : Store) (c : Std.HashMap (Nat × List Id) Id) :
    ({ σ with cache := c } : Store).size = σ.size := rfl

end Store

open Store

/-- The program semantics the cache is sound for: program `p` on the decoded
arguments. Generated per signature from Logos's definitions. -/
abbrev Sem := Nat → List Term → Option Term

/-- `i` is on the chain from `s`, which goes to smaller ids and ends at 0. -/
inductive Reach (next : Array Id) : Id → Id → Prop
  | here {i : Id} : 0 < i → Reach next i i
  | older {s i : Id} : next[s]! < s → Reach next next[s]! i → Reach next s i

/-- The chains hold the ids from 1 up to `m`, each in the bucket of its node. -/
structure Linked (nodes : Array Node) (heads next : Array Id) (m : Nat) : Prop where
  pos : 0 < heads.size
  lt : ∀ k : Nat, heads[k]! < m
  reach : ∀ i, 0 < i → i < m → Reach next heads[bucket (nhash nodes[i]!) heads.size]! i

/-- The store invariant. -/
structure Inv (sem : Sem) (σ : Store) : Prop where
  stuck0 : σ.nodes[0]? = some .Stuck
  wf : ∀ (i : Id) (n : Node), σ.nodes[i]? = some n → ∀ j ∈ n.children, j < i
  next_size : σ.next.size = σ.nodes.size
  linked : Linked σ.nodes σ.heads σ.next σ.nodes.size
  uniq : ∀ (n : Node) (i j : Id), σ.nodes[i]? = some n → σ.nodes[j]? = some n → i = j
  cache : ∀ (p : Nat) (args : List Id) (r : Id), σ.cache[(p, args)]? = some r →
    r < σ.size ∧ (∀ a ∈ args, a < σ.size) ∧
      sem p (args.map σ.decode) = some (σ.decode r)

/-- `σ'` extends `σ`: every id of `σ` keeps its node. -/
structure Extends (σ σ' : Store) : Prop where
  size_le : σ.size ≤ σ'.size
  same : ∀ i, i < σ.size → σ'.nodes[i]? = σ.nodes[i]?

theorem Extends.refl (σ : Store) : Extends σ σ := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Extends.trans {σ₁ σ₂ σ₃ : Store} (h₁ : Extends σ₁ σ₂) (h₂ : Extends σ₂ σ₃) :
    Extends σ₁ σ₃ :=
  ⟨Nat.le_trans h₁.size_le h₂.size_le, fun i hi => by
    rw [h₂.same i (Nat.lt_of_lt_of_le hi h₁.size_le), h₁.same i hi]⟩

section decode
variable {sem : Sem} {σ : Store}

theorem decode_unfold (σ : Store) (i : Id) :
    σ.decode i = match σ.nodes[i]? with
      | none => .Stuck
      | some n => n.toTerm (fun j => if j < i then σ.decode j else .Stuck) := by
  unfold Store.decode; rw [Store.decodeA]; rfl

/-- Under the invariant, an id reads as its node with its children read. -/
theorem decode_view (hI : Inv sem σ) {i : Id} (hi : i < σ.size) :
    σ.decode i = (σ.view i).toTerm σ.decode := by
  have hget : σ.nodes[i]? = some σ.nodes[i] := Array.getElem?_eq_getElem hi
  rw [decode_unfold, hget]
  simp only [view, hget, Option.getD_some]
  apply Node.toTerm_congr
  intro j hj
  simp [hI.wf i _ hget j hj]

theorem lt_of_child (hI : Inv sem σ) {i : Id} (hi : i < σ.size) {j : Id}
    (hj : j ∈ (σ.view i).children) : j < i := by
  have hget : σ.nodes[i]? = some σ.nodes[i] := Array.getElem?_eq_getElem hi
  simp only [view, hget, Option.getD_some] at hj
  exact hI.wf i _ hget j hj

theorem child_valid (hI : Inv sem σ) {i : Id} (hi : i < σ.size) {j : Id}
    (hj : j ∈ (σ.view i).children) : j < σ.size :=
  Nat.lt_trans (lt_of_child hI hi hj) hi

/-- Reading is stable when the store grows. -/
theorem decode_extends {σ' : Store} (hE : Extends σ σ') :
    ∀ i, i < σ.size → σ'.decode i = σ.decode i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    rw [decode_unfold σ', decode_unfold σ, hE.same i hi]
    cases h : σ.nodes[i]? with
    | none => rfl
    | some n =>
      simp only
      apply Node.toTerm_congr
      intro j _
      by_cases hji : j < i
      · simp [hji, ih j hji (Nat.lt_trans hji hi)]
      · simp [hji]

/-- Equal ids ⇔ equal terms: the table makes the store injective. -/
theorem decode_inj (hI : Inv sem σ) :
    ∀ i j, i < σ.size → j < σ.size → σ.decode i = σ.decode j → i = j := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro j hi hj h
    rw [decode_view hI hi, decode_view hI hj] at h
    have hn : σ.view i = σ.view j := by
      apply Node.toTerm_inj _ _ _ h
      intro a ha b hb hab
      exact ih a (lt_of_child hI hi ha) b (child_valid hI hi ha) (child_valid hI hj hb) hab
    have hgi : σ.nodes[i]? = some (σ.view i) := by
      simp [view, Array.getElem?_eq_getElem hi]
    have hgj : σ.nodes[j]? = some (σ.view i) := by
      rw [hn]; simp [view, Array.getElem?_eq_getElem hj]
    exact hI.uniq _ i j hgi hgj

theorem decode_eq_iff (hI : Inv sem σ) {i j : Id} (hi : i < σ.size) (hj : j < σ.size) :
    σ.decode i = σ.decode j ↔ i = j :=
  ⟨decode_inj hI i j hi hj, fun h => h ▸ rfl⟩

theorem decode_zero (hI : Inv sem σ) : σ.decode 0 = .Stuck := by
  rw [decode_unfold, hI.stuck0]; rfl

theorem size_pos (hI : Inv sem σ) : 0 < σ.size := by
  have := hI.stuck0
  rw [Array.getElem?_eq_some_iff] at this
  exact this.1

theorem decode_eq_stuck_iff (hI : Inv sem σ) {i : Id} (hi : i < σ.size) :
    σ.decode i = .Stuck ↔ i = 0 := by
  rw [← decode_zero hI]; exact decode_eq_iff hI hi (size_pos hI)

end decode

theorem Inv.init (sem : Sem) : Inv sem Store.init where
  stuck0 := rfl
  wf := by
    intro i n h j hj
    simp only [Store.init] at h
    rw [Array.getElem?_eq_some_iff] at h
    obtain ⟨hi, rfl⟩ := h
    simp [Node.children] at hj
  next_size := rfl
  linked := by
    refine ⟨by simp [Store.init], ?_, ?_⟩
    · intro k
      simp only [Store.init, getElem!_def, Array.getElem?_replicate]
      split
      · rename_i h; split at h <;> simp at h; simp [← h]
      · exact Nat.one_pos
    · intro i h0 h1
      simp [Store.init] at h1; omega
  uniq := by
    intro n i j hi hj
    have h1 := (Array.getElem?_eq_some_iff.mp hi).1
    have h2 := (Array.getElem?_eq_some_iff.mp hj).1
    simp [Store.init] at h1 h2; exact h1.trans h2.symm
  cache := by simp [Store.init]

end Kairos
