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

theorem intern_spec {σ : Store} {n : Node} (hI : Inv sem σ)
    (hc : ∀ j ∈ n.children, j < σ.size) :
    Ok (intern n) σ (fun r σ' => Inv sem σ' ∧ Extends σ σ' ∧ r < σ'.size ∧ σ'.view r = n) := by
  unfold Ok intern
  cases ht : σ.table[n]? with
  | some i =>
    simp only
    have hn := (hI.table n i).mp ht
    rw [Array.getElem?_eq_some_iff] at hn
    obtain ⟨hi, hni⟩ := hn
    refine ⟨hI, Extends.refl σ, hi, ?_⟩
    simp [view, Array.getElem?_eq_getElem hi, hni]
  | none =>
    simp only
    -- the new store
    have hsize : (σ.nodes.push n).size = σ.size + 1 := by simp [Store.size]
    have hext : Extends σ { σ with nodes := σ.nodes.push n, table := σ.table.insert n σ.nodes.size } :=
      ⟨by simp [Store.size], fun i hi => by
        simp only
        rw [Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]⟩
    refine ⟨?_, hext, by simp [Store.size], ?_⟩
    · constructor
      · simp only
        have h0 : 0 < σ.nodes.size := size_pos hI
        rw [Array.getElem?_push_lt h0, ← Array.getElem?_eq_getElem h0]; exact hI.stuck0
      · intro i m hm j hj
        simp only [Array.getElem?_push] at hm
        split at hm
        · rename_i hieq
          simp at hm; subst hm; subst hieq; exact hc j hj
        · exact hI.wf i m hm j hj
      · intro m i
        simp only [Std.HashMap.getElem?_insert, Array.getElem?_push]
        by_cases hnm : n = m
        · subst hnm
          simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq]
          constructor
          · intro h; subst h; simp
          · intro h
            split at h
            · rename_i h'; exact h'.symm
            · exact absurd ((hI.table n i).mpr h) (by simp [ht])
        · have hb : (n == m) = false := by simp [hnm]
          simp only [hb, Bool.false_eq_true, ↓reduceIte]
          rw [hI.table m i]
          constructor
          · intro h
            have hi : i < σ.nodes.size := (Array.getElem?_eq_some_iff.mp h).1
            simp [Nat.ne_of_lt hi, h]
          · intro h
            split at h
            · simp at h; exact absurd h hnm
            · exact h
      · intro p args r hr
        obtain ⟨h1, h2, h3⟩ := hI.cache p args r hr
        refine ⟨Nat.lt_of_lt_of_le h1 hext.size_le,
          fun a ha => Nat.lt_of_lt_of_le (h2 a ha) hext.size_le, ?_⟩
        rw [decode_extends hext r h1]
        have : args.map (Store.decode { σ with nodes := σ.nodes.push n, table := σ.table.insert n σ.nodes.size })
            = args.map σ.decode :=
          List.map_congr_left (fun a ha => decode_extends hext a (h2 a ha))
        rw [this]; exact h3
    · simp [view]

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
      refine ⟨hI'.stuck0, hI'.wf, hI'.table, ?_⟩
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
