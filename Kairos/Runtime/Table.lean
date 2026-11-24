/-
The interning table is exact: interning a node finds it if it is in the store,
and adds it otherwise. These proofs are with the code, not in `verification/`,
because interning by address (`Kairos/Runtime/Share.lean`) is only well defined
by them.

* `TInv`: the invariant of the table.
* `Stable m`: `m` returns, and returns the same id, changing nothing, in any
  later store. `intern` is stable, so `internTerm` is.
-/
import Kairos.Gen.Intern

namespace Kairos
open Eo Store

/-- `i` is on the chain from `s`, which goes to smaller ids and ends at 0. -/
inductive Reach (next : Array Id) : Id → Id → Prop
  | here {i : Id} : 0 < i → Reach next i i
  | older {s i : Id} : next[s]! < s → Reach next next[s]! i → Reach next s i

/-- The chains hold the ids from 3 up to `m`, each in the bucket of its node. -/
structure Linked (nodes : Array Node) (heads next : Array Id) (m : Nat) : Prop where
  pos : 0 < heads.size
  lt : ∀ k : Nat, heads[k]! < m
  reach : ∀ i, 2 < i → i < m → Reach next heads[bucket (nhash nodes[i]!) heads.size]! i

/-- The table's invariant: it holds every id in its bucket, and no node twice. -/
structure TInv (σ : Store) : Prop where
  stuck0 : σ.nodes[0]? = some .Stuck
  true1 : σ.nodes[1]? = some (.Boolean true)
  false2 : σ.nodes[2]? = some (.Boolean false)
  next_size : σ.next.size = σ.nodes.size
  linked : Linked σ.nodes σ.heads σ.next σ.nodes.size
  uniq : ∀ (n : Node) (i j : Id), σ.nodes[i]? = some n → σ.nodes[j]? = some n → i = j

/-! ## The interning table -/
section table
variable {nodes : Array Node} {heads next : Array Id}

theorem bucket_lt (h : UInt64) {sz : Nat} (hs : 0 < sz) : bucket h sz < sz := by
  unfold bucket; simp only; split <;> assumption

theorem find_le (p : Node → Bool) (s : Id) : find p nodes next s ≤ s := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
    rw [find]
    split
    · exact Nat.zero_le _
    · split
      · exact Nat.le_refl _
      · simp only
        split
        · rename_i h; exact Nat.le_trans (ih _ h) (Nat.le_of_lt h)
        · exact Nat.zero_le _

theorem find_sat (p : Node → Bool) (s : Id) (h : find p nodes next s ≠ 0) :
    p nodes[find p nodes next s]! = true := by
  induction s using Nat.strongRecOn with
  | ind s ih =>
    rw [find] at h ⊢
    by_cases h0 : s = 0
    · simp [h0] at h
    · simp only [h0, ↓reduceIte] at h ⊢
      by_cases hp : p nodes[s]! = true
      · simp only [hp, ↓reduceIte]
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hl : next[s]! < s
        · simp only [hl, ↓reduceIte] at h ⊢
          exact ih _ hl h
        · simp [hl] at h

theorem find_ne {p : Node → Bool} {s i : Id} (hr : Reach next s i)
    (hp : p nodes[i]! = true) : find p nodes next s ≠ 0 := by
  induction hr with
  | here hi => rw [find]; simp [hp, Nat.ne_of_gt hi]
  | @older s i hl _ ih =>
    rw [find]
    have h0 : s ≠ 0 := by intro h; rw [h] at hl; exact Nat.not_lt_zero _ hl
    simp only [h0, ↓reduceIte, hl]
    split
    · exact h0
    · exact ih hp

theorem Reach.congr {next' : Array Id} {s i : Id} (hr : Reach next s i)
    (h : ∀ x, x ≤ s → next'[x]! = next[x]!) : Reach next' s i := by
  induction hr with
  | here hi => exact .here hi
  | @older s i hl _ ih =>
    have hs := h s (Nat.le_refl _)
    refine .older (by rw [hs]; exact hl) ?_
    rw [hs]
    exact ih (fun x hx => h x (Nat.le_trans hx (Nat.le_of_lt hl)))

theorem getElem!_set! {a : Array Id} {k j : Nat} {v : Id} (hk : k < a.size) :
    (a.set! k v)[j]! = if j = k then v else a[j]! := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  by_cases h : j = k
  · subst h; simp [hk]
  · simp [h, Ne.symm h]

/-- Linking the id `m` in front of its bucket. -/
theorem Linked.step {nodes' : Array Node} {next' : Array Id} {m : Nat}
    (hL : Linked nodes heads next m) (hm : 2 < m)
    (hn : ∀ j, j < m → nodes'[j]! = nodes[j]!)
    (hx : ∀ j, j < m → next'[j]! = next[j]!)
    (ho : next'[m]! = heads[bucket (nhash nodes'[m]!) heads.size]!) :
    Linked nodes' (heads.set! (bucket (nhash nodes'[m]!) heads.size) m) next' (m + 1) := by
  have hk := bucket_lt (nhash nodes'[m]!) hL.pos
  refine ⟨by simpa using hL.pos, ?_, ?_⟩
  · intro k
    rw [getElem!_set! hk]
    split
    · exact Nat.lt_succ_self m
    · exact Nat.lt_succ_of_lt (hL.lt k)
  · intro i hi0 him
    have hsz : ∀ k, (heads.set! k m).size = heads.size := fun k => by simp
    rw [hsz, getElem!_set! hk]
    have hold : ∀ k, i < m → Reach next heads[k]! i → Reach next' heads[k]! i :=
      fun k _ hr => hr.congr (fun x hx' => hx x (Nat.lt_of_le_of_lt hx' (hL.lt k)))
    by_cases h : i = m
    · subst h; simp only [↓reduceIte]; exact .here (Nat.lt_trans (by decide) hi0)
    · have hi : i < m := by omega
      have hr := hL.reach i hi0 hi
      rw [← hn i hi] at hr
      split
      · rename_i he
        rw [he] at hr
        refine .older (by rw [ho]; exact hL.lt _) ?_
        rw [ho]
        exact hold _ hi hr
      · exact hold _ hi hr

theorem rehash_linked (m : Nat) : ∀ {heads next : Array Id},
    Linked nodes heads next m → 2 < m → m ≤ nodes.size → next.size = nodes.size →
    Linked nodes (rehash nodes m heads next).1 (rehash nodes m heads next).2 nodes.size ∧
      (rehash nodes m heads next).2.size = nodes.size := by
  induction hd : nodes.size - m using Nat.strongRecOn generalizing m with
  | ind d ih =>
    intro heads next hL hm hle hs
    rw [rehash]
    by_cases h : m < nodes.size
    · simp only [h, ↓reduceIte]
      refine ih (nodes.size - (m + 1)) (by omega) (m + 1) rfl ?_ (by omega) (by omega) (by simpa using hs)
      refine hL.step hm (fun _ _ => rfl) ?_ ?_
      · intro j hj
        rw [getElem!_set! (by omega)]
        simp [Nat.ne_of_lt hj]
      · rw [getElem!_set! (by omega)]; simp
    · have he : m = nodes.size := by omega
      subst he
      simp only [Nat.lt_irrefl, ↓reduceIte]
      exact ⟨hL, hs⟩

theorem grow_nodes (σ : Store) : (grow σ).nodes = σ.nodes := rfl
theorem grow_cache (σ : Store) : (grow σ).cache = σ.cache := rfl

theorem grow_linked {σ : Store} (hp : 2 < σ.nodes.size) (hs : σ.next.size = σ.nodes.size)
    (hL : Linked σ.nodes σ.heads σ.next σ.nodes.size) :
    Linked (grow σ).nodes (grow σ).heads (grow σ).next (grow σ).nodes.size ∧
      (grow σ).next.size = (grow σ).nodes.size := by
  refine rehash_linked (nodes := σ.nodes) 3 (heads := Array.replicate (σ.heads.size * 4) 0)
    (next := σ.next) ⟨?_, ?_, ?_⟩ (by omega) hp hs
  · have := hL.pos; simp; omega
  · intro k
    simp only [getElem!_def, Array.getElem?_replicate]
    split
    · rename_i h; split at h <;> simp at h; simp [← h]
    · simp
  · intro i h1 h2; omega

/-- A lookup that finds `i`: its node is the one looked for. -/
theorem find_node {σ : Store} {p : Node → Bool} {n : Node} (hI : TInv σ)
    (hp : ∀ m, p m = true ↔ m = n) (k : Nat) (h : find p σ.nodes σ.next σ.heads[k]! ≠ 0) :
    σ.nodes[find p σ.nodes σ.next σ.heads[k]!]? = some n := by
  have hlt := Nat.lt_of_le_of_lt (find_le (nodes := σ.nodes) (next := σ.next) p σ.heads[k]!)
    (hI.linked.lt k)
  have := (hp _).mp (find_sat p _ h)
  rw [getElem!_pos σ.nodes _ hlt] at this
  rw [Array.getElem?_eq_getElem hlt, this]

/-- A lookup that finds nothing: the node is new. -/
theorem find_new {σ : Store} {p : Node → Bool} {n : Node} (hI : TInv σ)
    (hp : ∀ m, p m = true ↔ m = n) (hn : n ≠ .Stuck)
    (hb : ∀ b, n ≠ .Boolean b)
    (h : find p σ.nodes σ.next σ.heads[bucket (nhash n) σ.heads.size]! = 0) (i : Id) :
    σ.nodes[i]? ≠ some n := by
  intro hi
  have hlt : i < σ.nodes.size := (Array.getElem?_eq_some_iff.mp hi).1
  have he : σ.nodes[i]! = n := by simp [getElem!_def, hi]
  have h0 : 2 < i := by
    match i, hi with
    | 0, hi => rw [hI.stuck0] at hi; exact absurd (Option.some.inj hi).symm hn
    | 1, hi => rw [hI.true1] at hi; exact absurd (Option.some.inj hi).symm (hb _)
    | 2, hi => rw [hI.false2] at hi; exact absurd (Option.some.inj hi).symm (hb _)
    | i + 3, _ => exact Nat.le_add_left 3 i
  have hr := hI.linked.reach i h0 hlt
  rw [he] at hr
  exact find_ne hr ((hp _).mpr he) h

end table

/-- What interning `n` guarantees. -/
structure Interned (σ : Store) (n : Node) (r : Id) (σ' : Store) : Prop where
  inv : TInv σ'
  node : σ'.nodes[r]? = some n
  cache : σ'.cache = σ.cache
  nodes : σ' = σ ∨ σ'.nodes = σ.nodes.push n

theorem TInv.add {σ σ' : Store} {n : Node} (hI : TInv σ) (hnew : ∀ i : Id, σ.nodes[i]? ≠ some n)
    (hnodes : σ'.nodes = σ.nodes.push n) (hcache : σ'.cache = σ.cache)
    (hL : Linked σ'.nodes σ'.heads σ'.next σ'.nodes.size)
    (hs : σ'.next.size = σ'.nodes.size) : Interned σ n σ.nodes.size σ' := by
  have h0 : 0 < σ.nodes.size := (Array.getElem?_eq_some_iff.mp hI.stuck0).1
  have h1 : 1 < σ.nodes.size := (Array.getElem?_eq_some_iff.mp hI.true1).1
  have h2 : 2 < σ.nodes.size := (Array.getElem?_eq_some_iff.mp hI.false2).1
  refine ⟨⟨?_, ?_, ?_, hs, hL, ?_⟩, by simp [hnodes], hcache, .inr hnodes⟩
  · rw [hnodes, Array.getElem?_push_lt h0, ← Array.getElem?_eq_getElem h0]; exact hI.stuck0
  · rw [hnodes, Array.getElem?_push_lt h1, ← Array.getElem?_eq_getElem h1]; exact hI.true1
  · rw [hnodes, Array.getElem?_push_lt h2, ← Array.getElem?_eq_getElem h2]; exact hI.false2
  · intro m i j hi hj
    simp only [hnodes, Array.getElem?_push] at hi hj
    split at hi <;> split at hj
    · rename_i h1 h2; exact h1.trans h2.symm
    · simp at hi; subst hi; exact absurd hj (hnew j)
    · simp at hj; subst hj; exact absurd hi (hnew i)
    · exact hI.uniq m i j hi hj

theorem addNode_table {σ : Store} {n : Node} (hI : TInv σ) (hnew : ∀ i : Id, σ.nodes[i]? ≠ some n) :
    ∃ r σ', addNode n (bucket (nhash n) σ.heads.size) σ = .ok r σ' ∧ Interned σ n r σ' := by
  have hpos : 2 < σ.nodes.size := (Array.getElem?_eq_some_iff.mp hI.false2).1
  have hs := hI.next_size
  have hm : (σ.nodes.push n)[σ.nodes.size]! = n := by simp
  have hL : Linked (σ.nodes.push n)
      (σ.heads.set! (bucket (nhash n) σ.heads.size) σ.nodes.size)
      (σ.next.push σ.heads[bucket (nhash n) σ.heads.size]!) (σ.nodes.size + 1) := by
    have h := hI.linked.step (nodes' := σ.nodes.push n)
      (next' := σ.next.push σ.heads[bucket (nhash n) σ.heads.size]!) hpos
      (fun j hj => by simp [getElem!_def, Array.getElem?_push, Nat.ne_of_lt hj])
      (fun j hj => by
        simp only [getElem!_def, Array.getElem?_push, hs, Nat.ne_of_lt hj, ↓reduceIte])
      (by rw [hm, ← hs]; simp only [getElem!_def, Array.getElem?_push, ↓reduceIte])
    rw [hm] at h; exact h
  unfold addNode
  refine ⟨_, _, rfl, ?_⟩
  split
  · obtain ⟨hL', hs'⟩ := grow_linked (σ := ⟨σ.nodes.push n,
      σ.heads.set! (bucket (nhash n) σ.heads.size) σ.nodes.size,
      σ.next.push σ.heads[bucket (nhash n) σ.heads.size]!, σ.cache⟩)
      (by simp; omega) (by simp [hs]) (by simpa using hL)
    exact hI.add hnew rfl rfl hL' hs'
  · exact hI.add hnew rfl rfl (by simpa using hL) (by simp [hs])

/-- Look `n` up, with any test for being `n`, and add it if it is not there. -/
theorem lookup_table {σ : Store} {p : Node → Bool} {n : Node} (hI : TInv σ)
    (hp : ∀ m, p m = true ↔ m = n) (hn : n ≠ .Stuck) (hb : ∀ b, n ≠ .Boolean b) :
    ∃ r σ', (if find p σ.nodes σ.next σ.heads[bucket (nhash n) σ.heads.size]! = 0
      then addNode n (bucket (nhash n) σ.heads.size) σ
      else .ok (find p σ.nodes σ.next σ.heads[bucket (nhash n) σ.heads.size]!) σ) = .ok r σ' ∧
      Interned σ n r σ' := by
  by_cases h : find p σ.nodes σ.next σ.heads[bucket (nhash n) σ.heads.size]! = 0
  · simp only [h, ↓reduceIte]
    exact addNode_table hI (find_new hI hp hn hb h)
  · simp only [h, ↓reduceIte]
    exact ⟨_, _, rfl, hI, find_node hI hp _ h, rfl, .inl rfl⟩

/-- `true` and `false` are at their ids. -/
theorem bool_table {σ : Store} (hI : TInv σ) (b : Bool) :
    σ.nodes[if b then 1 else 2]? = some (.Boolean b) := by
  cases b
  · exact hI.false2
  · exact hI.true1

theorem internNode_table {σ : Store} {n : Node} (hI : TInv σ) :
    ∃ r σ', internNode n σ = .ok r σ' ∧ Interned σ n r σ' := by
  by_cases hn : n = .Stuck
  · subst hn
    exact ⟨0, σ, rfl, hI, hI.stuck0, rfl, .inl rfl⟩
  · by_cases hb : ∃ b, n = .Boolean b
    · obtain ⟨b, rfl⟩ := hb
      exact ⟨_, σ, rfl, hI, bool_table hI b, rfl, .inl rfl⟩
    · have hb : ∀ b, n ≠ .Boolean b := fun b e => hb ⟨b, e⟩
      have h := lookup_table (p := fun m => decide (m = n)) hI (fun m => by simp) hn hb
      cases n <;> first | exact absurd rfl hn | exact absurd rfl (hb _) | exact h

theorem intern_table {σ : Store} (n : Node) (hI : TInv σ) :
    ∃ r σ', intern n σ = .ok r σ' ∧ Interned σ n r σ' := by
  unfold intern
  split
  · rename_i a b
    exact lookup_table (p := isApply a b) (n := .Apply a b) hI
      (fun m => by cases m <;> simp [isApply]) (by simp) (by simp)
  · rename_i o
    exact lookup_table (p := isUOp o) (n := .UOp o) hI
      (fun m => by cases m <;> simp [isUOp]) (by simp) (by simp)
  · exact ⟨_, σ, rfl, hI, bool_table hI _, rfl, .inl rfl⟩
  · exact internNode_table hI

/-- A node that is in the store is found, and nothing changes. -/
theorem intern_found {σ : Store} {n : Node} {i : Id} (hI : TInv σ) (h : σ.nodes[i]? = some n) :
    intern n σ = .ok i σ := by
  obtain ⟨r, σ', he, hs⟩ := intern_table n hI
  rcases hs.nodes with rfl | hp
  · rw [he, hI.uniq n r i hs.node h]
  · have hi : i < σ.nodes.size := (Array.getElem?_eq_some_iff.mp h).1
    have h1 : σ'.nodes[i]? = some n := by
      rw [hp, Array.getElem?_push_lt hi, ← Array.getElem?_eq_getElem hi]; exact h
    have h2 : σ'.nodes[σ.nodes.size]? = some n := by simp [hp]
    exact absurd (hs.inv.uniq n _ _ h1 h2) (Nat.ne_of_lt hi)

/-! ## Stable computations -/
/-- Every node of `σ` is in `σ'`, at the same id. -/
def Le (σ σ' : Store) : Prop := ∀ (i : Id) (n : Node), σ.nodes[i]? = some n → σ'.nodes[i]? = some n

theorem Le.refl (σ : Store) : Le σ σ := fun _ _ h => h
theorem Le.trans {σ₁ σ₂ σ₃ : Store} (h : Le σ₁ σ₂) (h' : Le σ₂ σ₃) : Le σ₁ σ₃ :=
  fun i n hi => h' i n (h i n hi)

/-- In every store from `σ` on, `m` returns `a` and changes nothing. -/
def Settled {α : Type} (m : K α) (σ : Store) (a : α) : Prop :=
  ∀ σ', TInv σ' → Le σ σ' → m σ' = .ok a σ'

theorem Settled.mono {α : Type} {m : K α} {σ σ' : Store} {a : α} (h : Settled m σ a)
    (hL : Le σ σ') : Settled m σ' a := fun σ'' hI hL' => h σ'' hI (hL.trans hL')

/-- `m` returns, with an answer that is settled. -/
def Stable {α : Type} (m : K α) : Prop :=
  ∀ σ, TInv σ → ∃ a σ', m σ = .ok a σ' ∧ TInv σ' ∧ Le σ σ' ∧ Settled m σ' a

theorem Stable.pure {α : Type} (a : α) : Stable (pure a : K α) := fun σ hI =>
  ⟨a, σ, rfl, hI, Le.refl σ, fun _ _ _ => rfl⟩

theorem bind_ok {α β : Type} {m : K α} {f : α → K β} {σ σ' : Store} {a : α} (h : m σ = .ok a σ') :
    (m >>= f) σ = f a σ' := by
  show EStateM.bind m f σ = _
  unfold EStateM.bind; rw [h]

theorem Stable.bind {α β : Type} {m : K α} {f : α → K β} (hm : Stable m) (hf : ∀ a, Stable (f a)) :
    Stable (m >>= f) := fun σ hI => by
  obtain ⟨a, σ1, e1, hI1, hL1, hs1⟩ := hm σ hI
  obtain ⟨b, σ2, e2, hI2, hL2, hs2⟩ := hf a σ1 hI1
  refine ⟨b, σ2, (bind_ok e1).trans e2, hI2, hL1.trans hL2, fun σ' hI' hL' => ?_⟩
  rw [bind_ok (hs1 σ' hI' (hL2.trans hL'))]
  exact hs2 σ' hI' hL'

theorem Stable.intern (n : Node) : Stable (intern n) := fun σ hI => by
  obtain ⟨r, σ', e, hs⟩ := intern_table n hI
  refine ⟨r, σ', e, hs.inv, ?_, fun σ'' hI' hL => intern_found hI' (hL r n hs.node)⟩
  rcases hs.nodes with rfl | hp
  · exact Le.refl _
  · intro i n' hi
    have hlt : i < σ.nodes.size := (Array.getElem?_eq_some_iff.mp hi).1
    rw [hp, Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]; exact hi

theorem internTerm_stable : ∀ t : Term, Stable (internTerm t) := by
  intro t
  induction t using internTerm.induct <;> simp only [internTerm] <;>
    repeat first
      | exact Stable.intern _
      | exact Stable.pure _
      | assumption
      | (refine Stable.bind (by assumption) fun _ => ?_)

theorem TInv.init : TInv Store.init where
  stuck0 := rfl
  true1 := rfl
  false2 := rfl
  next_size := rfl
  linked := by
    refine ⟨by simp [Store.init], ?_, ?_⟩
    · intro k
      simp only [Store.init, getElem!_def, Array.getElem?_replicate]
      split
      · rename_i h; split at h <;> simp at h; simp [← h]
      · simp
    · intro i h0 h1
      simp [Store.init] at h1; omega
  uniq := by
    intro n i j hi hj
    match i, j, hi, hj with
    | 0, 0, _, _ => rfl
    | 1, 1, _, _ => rfl
    | 2, 2, _, _ => rfl
    | 0, 1, hi, hj => cases hi; simp [Store.init] at hj
    | 0, 2, hi, hj => cases hi; simp [Store.init] at hj
    | 1, 0, hi, hj => cases hi; simp [Store.init] at hj
    | 1, 2, hi, hj => cases hi; simp [Store.init] at hj
    | 2, 0, hi, hj => cases hi; simp [Store.init] at hj
    | 2, 1, hi, hj => cases hi; simp [Store.init] at hj
    | i + 3, _, hi, _ => simp [Store.init] at hi
    | _, j + 3, _, hj => simp [Store.init] at hj

end Kairos
