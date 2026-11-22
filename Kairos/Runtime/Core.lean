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
import Kairos.Gen.Term

namespace Kairos
open Eo

/-- Errors are resource exhaustion only: a Kairos error is never a verdict. -/
inductive Err where
  | fuel
  deriving Repr, Inhabited

structure Store where
  nodes : Array Node
  table : Std.HashMap Node Id
  /-- Program results, keyed by (program id, argument ids). -/
  cache : Std.HashMap (Nat × List Id) Id

namespace Store

/-- The store with only `Stuck`, at id 0. -/
def init : Store :=
  { nodes := #[.Stuck], table := (∅ : Std.HashMap Node Id).insert .Stuck 0, cache := ∅ }

def size (σ : Store) : Nat := σ.nodes.size

/-- The node of `i`; `Stuck` for an id that is not in the store. -/
def view (σ : Store) (i : Id) : Node := σ.nodes[i]?.getD .Stuck

/-- Read an id of a node array back as Logos's term. Specification only. -/
def decodeA (nodes : Array Node) (i : Id) : Term :=
  match nodes[i]? with
  | none => .Stuck
  | some n => n.toTerm (fun j => if j < i then decodeA nodes j else .Stuck)
termination_by i
decreasing_by assumption

/-- Read an id back as Logos's term. Specification only. -/
def decode (σ : Store) (i : Id) : Term := decodeA σ.nodes i

@[simp] theorem decode_with_cache (σ : Store) (c : Std.HashMap (Nat × List Id) Id) :
    ({ σ with cache := c } : Store).decode = σ.decode := rfl

@[simp] theorem size_with_cache (σ : Store) (c : Std.HashMap (Nat × List Id) Id) :
    ({ σ with cache := c } : Store).size = σ.size := rfl

end Store

open Store

/-- The program semantics the cache is sound for: program `p` on the decoded
arguments. Generated per signature from Logos's definitions. -/
abbrev Sem := Nat → List Term → Option Term

/-- The store invariant. -/
structure Inv (sem : Sem) (σ : Store) : Prop where
  stuck0 : σ.nodes[0]? = some .Stuck
  wf : ∀ (i : Id) (n : Node), σ.nodes[i]? = some n → ∀ j ∈ n.children, j < i
  table : ∀ (n : Node) (i : Id), σ.table[n]? = some i ↔ σ.nodes[i]? = some n
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
  unfold Store.decode; rw [Store.decodeA]

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
    have := ((hI.table _ i).mpr hgi).symm.trans ((hI.table _ j).mpr hgj)
    exact Option.some.inj this

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
  table := by
    intro n i
    simp only [Store.init, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
    constructor
    · intro h
      split at h
      · rename_i hn
        simp at h hn; subst h; subst hn; rfl
      · simp at h
    · intro h
      rw [Array.getElem?_eq_some_iff] at h
      obtain ⟨hi, rfl⟩ := h
      simp at hi; subst hi; simp
  cache := by simp [Store.init]

end Kairos
