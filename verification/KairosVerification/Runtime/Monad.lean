/-
The Kairos monad and its program logic.

* `K` threads the store; it can fail only by running out of a resource.
* `Ok m σ Q`: if `m` returns from `σ`, then `Q` holds of its result. Errors
  satisfy everything: this is the refinement reading (Kairos may give up, it
  may not be wrong).
* `Post sem σ t r σ'`: the standard postcondition of a term-producing
  computation started in `σ`: the invariant holds in `σ'`, `σ'` extends `σ`,
  and `r` is a valid id that reads as the Logos term `t`.
-/
import Kairos.Runtime.Monad
import KairosVerification.Runtime.Core

namespace Kairos
open Eo Store
variable {α β : Type} {sem : Sem}

def Ok (m : K α) (σ : Store) (Q : α → Store → Prop) : Prop :=
  match m σ with
  | .ok a σ' => Q a σ'
  | .error _ _ => True

theorem Ok.pure {a : α} {σ : Store} {Q : α → Store → Prop} (h : Q a σ) :
    Ok (Pure.pure a : K α) σ Q := h

theorem Ok.bind {m : K α} {f : α → K β} {σ : Store} {Q : β → Store → Prop}
    (h : Ok m σ (fun a σ' => Ok (f a) σ' Q)) : Ok (m >>= f) σ Q := by
  unfold Ok at *
  show (match EStateM.bind m f σ with | .ok a σ' => Q a σ' | .error _ _ => True)
  unfold EStateM.bind
  cases hm : m σ with
  | ok a σ' => simp only [hm] at h; exact h
  | error e σ' => trivial

theorem Ok.throw {e : Err} {σ : Store} {Q : α → Store → Prop} :
    Ok (MonadExcept.throw e : K α) σ Q := trivial

theorem Ok.mono {m : K α} {σ : Store} {P Q : α → Store → Prop}
    (h : Ok m σ P) (hPQ : ∀ a σ', P a σ' → Q a σ') : Ok m σ Q := by
  unfold Ok at *
  cases hm : m σ with
  | ok a σ' => simp only [hm] at h; exact hPQ a σ' h
  | error e σ' => trivial

/-- The postcondition of a computation of the term `t`, started in `σ`. -/
structure Post (sem : Sem) (σ : Store) (t : Term) (r : Id) (σ' : Store) : Prop where
  inv : Inv sem σ'
  ext : Extends σ σ'
  valid : r < σ'.size
  dec : σ'.decode r = t

/-- `m`, run in a store with the invariant, computes the Logos term `t`. -/
def Sim (sem : Sem) (σ : Store) (m : K Id) (t : Term) : Prop :=
  Ok m σ (Post sem σ t)

theorem Post.weaken {σ₀ σ σ' : Store} {t : Term} {r : Id} (hE : Extends σ₀ σ)
    (h : Post sem σ t r σ') : Post sem σ₀ t r σ' :=
  ⟨h.inv, hE.trans h.ext, h.valid, h.dec⟩

/-- Sequencing: compute `t` into `r`, then continue in the bigger store, where
every earlier id still reads the same. -/
theorem Sim.bind {σ : Store} {m : K Id} {k : Id → K Id} {t u : Term}
    (hm : Sim sem σ m t)
    (hk : ∀ r σ', Post sem σ t r σ' → Sim sem σ' (k r) u) :
    Sim sem σ (m >>= k) u := by
  apply Ok.bind
  apply Ok.mono hm
  intro r σ' hp
  exact Ok.mono (hk r σ' hp) (fun _ _ h => h.weaken hp.ext)

theorem Sim.pure {σ : Store} {r : Id} {t : Term} (hI : Inv sem σ) (hr : r < σ.size)
    (h : σ.decode r = t) : Sim sem σ (Pure.pure r) t :=
  Ok.pure ⟨hI, Extends.refl σ, hr, h⟩

theorem Sim.congr {σ : Store} {m : K Id} {t t' : Term} (h : Sim sem σ m t) (e : t = t') :
    Sim sem σ m t' :=
  e ▸ h

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
    (hL : Linked nodes heads next m) (hm : 0 < m)
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
    · subst h; simp only [↓reduceIte]; exact .here hi0
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
    Linked nodes heads next m → 0 < m → m ≤ nodes.size → next.size = nodes.size →
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

theorem grow_linked {σ : Store} (hp : 0 < σ.nodes.size) (hs : σ.next.size = σ.nodes.size)
    (hL : Linked σ.nodes σ.heads σ.next σ.nodes.size) :
    Linked (grow σ).nodes (grow σ).heads (grow σ).next (grow σ).nodes.size ∧
      (grow σ).next.size = (grow σ).nodes.size := by
  refine rehash_linked (nodes := σ.nodes) 1 (heads := Array.replicate (σ.heads.size * 4) 0)
    (next := σ.next) ⟨?_, ?_, ?_⟩ (by omega) hp hs
  · have := hL.pos; simp; omega
  · intro k
    simp only [getElem!_def, Array.getElem?_replicate]
    split
    · rename_i h; split at h <;> simp at h; simp [← h]
    · exact Nat.one_pos
  · intro i h1 h2; omega

/-- A lookup that finds `i`: its node is the one looked for. -/
theorem find_view {σ : Store} {p : Node → Bool} {n : Node} (hI : Inv sem σ)
    (hp : ∀ m, p m = true ↔ m = n) (k : Nat) (h : find p σ.nodes σ.next σ.heads[k]! ≠ 0) :
    find p σ.nodes σ.next σ.heads[k]! < σ.size ∧
      σ.view (find p σ.nodes σ.next σ.heads[k]!) = n := by
  have hlt := Nat.lt_of_le_of_lt (find_le (nodes := σ.nodes) (next := σ.next) p σ.heads[k]!)
    (hI.linked.lt k)
  refine ⟨hlt, ?_⟩
  have := (hp _).mp (find_sat p _ h)
  rw [getElem!_pos σ.nodes _ hlt] at this
  simp only [view, Array.getElem?_eq_getElem hlt, Option.getD_some, this]

/-- A lookup that finds nothing: the node is new. -/
theorem find_new {σ : Store} {p : Node → Bool} {n : Node} (hI : Inv sem σ)
    (hp : ∀ m, p m = true ↔ m = n) (hn : n ≠ .Stuck)
    (h : find p σ.nodes σ.next σ.heads[bucket (nhash n) σ.heads.size]! = 0) (i : Id) :
    σ.nodes[i]? ≠ some n := by
  intro hi
  have hlt : i < σ.nodes.size := (Array.getElem?_eq_some_iff.mp hi).1
  have he : σ.nodes[i]! = n := by simp [getElem!_def, hi]
  have h0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; rw [hI.stuck0] at hi; exact absurd (Option.some.inj hi).symm hn
    · exact h0
  have hr := hI.linked.reach i h0 hlt
  rw [he] at hr
  exact find_ne hr ((hp _).mpr he) h

end table

/-- What interning `n` guarantees. -/
def Interned (sem : Sem) (σ : Store) (n : Node) (r : Id) (σ' : Store) : Prop :=
  Inv sem σ' ∧ Extends σ σ' ∧ r < σ'.size ∧ σ'.view r = n

/-- The invariant, for any store with the new node and a good table. -/
theorem Inv.add {σ σ' : Store} {n : Node} (hI : Inv sem σ)
    (hc : ∀ j ∈ n.children, j < σ.size) (hnew : ∀ i : Id, σ.nodes[i]? ≠ some n)
    (hnodes : σ'.nodes = σ.nodes.push n) (hcache : σ'.cache = σ.cache)
    (hL : Linked σ'.nodes σ'.heads σ'.next σ'.nodes.size)
    (hs : σ'.next.size = σ'.nodes.size) :
    Interned sem σ n σ.nodes.size σ' := by
  have hext : Extends σ σ' :=
    ⟨by simp [Store.size, hnodes], fun i hi => by
      rw [hnodes, Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]⟩
  refine ⟨⟨?_, ?_, hs, hL, ?_, ?_⟩, hext, by simp [Store.size, hnodes], by simp [view, hnodes]⟩
  · have h0 : 0 < σ.nodes.size := size_pos hI
    rw [hnodes, Array.getElem?_push_lt h0, ← Array.getElem?_eq_getElem h0]; exact hI.stuck0
  · intro i m hm j hj
    simp only [hnodes, Array.getElem?_push] at hm
    split at hm
    · rename_i hieq
      simp at hm; subst hm; subst hieq; exact hc j hj
    · exact hI.wf i m hm j hj
  · intro m i j hi hj
    simp only [hnodes, Array.getElem?_push] at hi hj
    split at hi <;> split at hj
    · rename_i h1 h2; exact h1.trans h2.symm
    · simp at hi; subst hi; exact absurd hj (hnew j)
    · simp at hj; subst hj; exact absurd hi (hnew i)
    · exact hI.uniq m i j hi hj
  · intro p args r hr
    rw [hcache] at hr
    obtain ⟨h1, h2, h3⟩ := hI.cache p args r hr
    refine ⟨Nat.lt_of_lt_of_le h1 hext.size_le,
      fun a ha => Nat.lt_of_lt_of_le (h2 a ha) hext.size_le, ?_⟩
    rw [decode_extends hext r h1,
      List.map_congr_left (fun a ha => decode_extends hext a (h2 a ha))]
    exact h3

theorem addNode_spec {σ : Store} {n : Node} (hI : Inv sem σ)
    (hc : ∀ j ∈ n.children, j < σ.size) (hnew : ∀ i : Id, σ.nodes[i]? ≠ some n) :
    Ok (addNode n (bucket (nhash n) σ.heads.size)) σ (Interned sem σ n) := by
  have hpos : 0 < σ.nodes.size := size_pos hI
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
  unfold Ok addNode
  simp only
  split
  · obtain ⟨hL', hs'⟩ := grow_linked (σ := ⟨σ.nodes.push n,
      σ.heads.set! (bucket (nhash n) σ.heads.size) σ.nodes.size,
      σ.next.push σ.heads[bucket (nhash n) σ.heads.size]!, σ.cache⟩)
      (by simp) (by simp [hs]) (by simpa using hL)
    exact hI.add hc hnew rfl rfl hL' hs'
  · exact hI.add hc hnew rfl rfl (by simpa using hL) (by simp [hs])

/-- Look `n` up, with any test for being `n`, and add it if it is not there. -/
theorem lookup_spec {σ : Store} {p : Node → Bool} {n : Node} (hI : Inv sem σ)
    (hc : ∀ j ∈ n.children, j < σ.size) (hp : ∀ m, p m = true ↔ m = n) (hn : n ≠ .Stuck) :
    Ok (fun σ =>
      let i := find p σ.nodes σ.next σ.heads[bucket (nhash n) σ.heads.size]!
      if i = 0 then addNode n (bucket (nhash n) σ.heads.size) σ else .ok i σ) σ
      (Interned sem σ n) := by
  by_cases h : find p σ.nodes σ.next σ.heads[bucket (nhash n) σ.heads.size]! = 0
  · have := addNode_spec hI hc (find_new hI hp hn h)
    unfold Ok at this ⊢
    simp only [h, ↓reduceIte]
    exact this
  · have := find_view hI hp _ h
    unfold Ok
    simp only [h, ↓reduceIte]
    exact ⟨hI, Extends.refl σ, this.1, this.2⟩

theorem internNode_spec {σ : Store} {n : Node} (hI : Inv sem σ)
    (hc : ∀ j ∈ n.children, j < σ.size) : Ok (internNode n) σ (Interned sem σ n) := by
  by_cases hn : n = .Stuck
  · subst hn
    exact ⟨hI, Extends.refl σ, size_pos hI, by simp [view, hI.stuck0]⟩
  · have h := lookup_spec (p := fun m => decide (m = n)) hI hc (fun m => by simp) hn
    cases n <;> first | exact absurd rfl hn | exact h

theorem intern_spec {σ : Store} {n : Node} (hI : Inv sem σ)
    (hc : ∀ j ∈ n.children, j < σ.size) :
    Ok (intern n) σ (fun r σ' => Inv sem σ' ∧ Extends σ σ' ∧ r < σ'.size ∧ σ'.view r = n) := by
  unfold intern
  split
  · rename_i a b
    exact lookup_spec (p := isApply a b) (n := .Apply a b) hI hc
      (fun m => by cases m <;> simp [isApply]) (by simp)
  · rename_i o
    exact lookup_spec (p := isUOp o) (n := .UOp o) hI hc
      (fun m => by cases m <;> simp [isUOp]) (by simp)
  · exact internNode_spec hI hc

/-- Interning computes the term the node stands for. -/
theorem intern_sim {σ : Store} {n : Node} (hI : Inv sem σ)
    (hc : ∀ j ∈ n.children, j < σ.size) :
    Sim sem σ (intern n) (n.toTerm σ.decode) := by
  apply Ok.mono (intern_spec hI hc)
  rintro r σ' ⟨hI', hE, hr, hv⟩
  refine ⟨hI', hE, hr, ?_⟩
  rw [decode_view hI' hr, hv]
  exact Node.toTerm_congr n (fun j hj => decode_extends hE j (hc j hj))

theorem cached_sim {σ : Store} {p : Nat} {args : List Id} {body : K Id} {t : Term}
    (hI : Inv sem σ) (hargs : ∀ a ∈ args, a < σ.size)
    (hsem : sem p (args.map σ.decode) = some t)
    (hbody : Sim sem σ body t) :
    Sim sem σ (cached p args body) t := by
  unfold Sim Ok cached
  cases hc : σ.cache[(p, args)]? with
  | some r =>
    simp only
    obtain ⟨h1, _, h3⟩ := hI.cache p args r hc
    rw [hsem] at h3
    exact ⟨hI, Extends.refl σ, h1, (Option.some.inj h3).symm⟩
  | none =>
    simp only
    unfold Sim Ok at hbody
    cases hb : body σ with
    | error e σ' => trivial
    | ok r σ' =>
      simp only [hb] at hbody
      obtain ⟨hI', hE, hr, hd⟩ := hbody
      have hE' : Extends σ { σ' with cache := σ'.cache.insert (p, args) r } :=
        ⟨hE.size_le, hE.same⟩
      refine ⟨?_, hE', by simpa using hr, by simpa using hd⟩
      refine ⟨hI'.stuck0, hI'.wf, hI'.next_size, hI'.linked, hI'.uniq, ?_⟩
      intro p' args' r' h
      simp only [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i heq
        simp only [beq_iff_eq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp only [Option.some.injEq] at h; subst h
        refine ⟨by simpa using hr, fun a ha => by simpa using Nat.lt_of_lt_of_le (hargs a ha) hE.size_le, ?_⟩
        simp only [decode_with_cache]
        have : args.map σ'.decode = args.map σ.decode :=
          List.map_congr_left (fun a ha => decode_extends hE a (hargs a ha))
        rw [this, hsem, hd]
      · simpa using hI'.cache p' args' r' h

end Kairos
