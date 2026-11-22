/-
Contexts of facts, and the step lemmas that generated proofs are made of.

A generated proof of a program case walks the right-hand side in evaluation
order. At each step it knows a list `Γ` of facts "Kairos value `a` stands for
Logos value `A`". One lemma (`Ctx.mono`) carries all of them across a store
that grew, so a step costs one line however much is known. Each step lemma
below takes the facts it needs as memberships in `Γ`, which `by simp`
discharges.

Facts are about any type with a representation `RepD α β` (Kairos `α`,
Logos `β`). Term ids use `termRep`. The embedded checker types get theirs
from the generator. Native values (Bool, Int, ...) need none: they are the
same values on both sides.
-/
import KairosVerification.Runtime.Monad

namespace Kairos
open Eo Store

/-- How a Kairos value of type `α` stands for a Logos value of type `β`. -/
structure RepD (α β : Type) where
  dec : Store → α → β
  valid : Store → α → Prop
  mono : ∀ {σ σ' : Store} (a : α), Extends σ σ' → valid σ a → valid σ' a ∧ dec σ' a = dec σ a

def termRep : RepD Id Term where
  dec := Store.decode
  valid σ i := i < σ.size
  mono a hE ha := ⟨Nat.lt_of_lt_of_le ha hE.size_le, decode_extends hE a ha⟩

/-- A fact: `a` stands for `b`. -/
structure Fact where
  {α β : Type}
  rep : RepD α β
  a : α
  b : β

/-- The fact that the id `i` reads as `t`. -/
abbrev Fact.term (i : Id) (t : Term) : Fact := ⟨termRep, i, t⟩

def Fact.Holds (σ : Store) (f : Fact) : Prop := f.rep.valid σ f.a ∧ f.rep.dec σ f.a = f.b

/-- Every fact of `Γ` holds in `σ`. -/
def Ctx (σ : Store) (Γ : List Fact) : Prop := ∀ f ∈ Γ, f.Holds σ

variable {sem : Sem} {σ : Store} {Γ : List Fact}

theorem Ctx.nil (σ : Store) : Ctx σ [] := by simp [Ctx]

theorem Ctx.cons {f : Fact} (hf : f.Holds σ) (hΓ : Ctx σ Γ) : Ctx σ (f :: Γ) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hΓ g hg

theorem Ctx.mono {σ' : Store} (hE : Extends σ σ') (hΓ : Ctx σ Γ) : Ctx σ' Γ := by
  intro f hf
  obtain ⟨hv, hd⟩ := hΓ f hf
  obtain ⟨hv', hd'⟩ := f.rep.mono f.a hE hv
  exact ⟨hv', hd'.trans hd⟩

theorem Ctx.term {i : Id} {t : Term} (hΓ : Ctx σ Γ) (h : Fact.term i t ∈ Γ) :
    i < σ.size ∧ σ.decode i = t :=
  hΓ _ h

theorem Ctx.valid {i : Id} {t : Term} (hΓ : Ctx σ Γ) (h : Fact.term i t ∈ Γ) : i < σ.size :=
  (hΓ.term h).1

theorem Ctx.dec {i : Id} {t : Term} (hΓ : Ctx σ Γ) (h : Fact.term i t ∈ Γ) : σ.decode i = t :=
  (hΓ.term h).2

theorem Fact.holds_term {i : Id} (hi : i < σ.size) : (Fact.term i (σ.decode i)).Holds σ :=
  ⟨hi, rfl⟩

/-- The context every case starts from: `Stuck` is id 0. -/
theorem Ctx.stuck (hI : Inv sem σ) : Ctx σ [Fact.term 0 .Stuck] :=
  Ctx.cons ⟨size_pos hI, decode_zero hI⟩ (Ctx.nil σ)

/-- Add a valid id, reading as its decoding. -/
theorem Ctx.arg {i : Id} (hi : i < σ.size) (hΓ : Ctx σ Γ) :
    Ctx σ (Fact.term i (σ.decode i) :: Γ) :=
  Ctx.cons (Fact.holds_term hi) hΓ

/-! ## Step lemmas -/
/-- Compute `t` into a fresh id, then continue knowing that it reads as `t`. -/
theorem Sim.step {m : K Id} {k : Id → K Id} {t u : Term}
    (hΓ : Ctx σ Γ) (hm : Sim sem σ m t)
    (hk : ∀ r σ', Inv sem σ' → Ctx σ' (Fact.term r t :: Γ) → Sim sem σ' (k r) u) :
    Sim sem σ (m >>= k) u :=
  Sim.bind hm fun r σ' hp =>
    hk r σ' hp.inv (Ctx.cons ⟨hp.valid, hp.dec⟩ (hΓ.mono hp.ext))

/-- The last step: an id already known to read as the goal. -/
theorem Sim.ret {r : Id} {t : Term} (hI : Inv sem σ) (hΓ : Ctx σ Γ)
    (h : Fact.term r t ∈ Γ) : Sim sem σ (Pure.pure r) t :=
  Sim.pure hI (hΓ.valid h) (hΓ.dec h)

/-- `Stuck`, which is id 0. -/
theorem Sim.stuck (hI : Inv sem σ) : Sim sem σ (Pure.pure 0) .Stuck :=
  Sim.pure hI (size_pos hI) (decode_zero hI)

/-- Intern a node whose children are known: it reads as the node's term. -/
theorem intern_ctx {n : Node} {d : Id → Term} (hI : Inv sem σ) (hΓ : Ctx σ Γ)
    (hc : ∀ j ∈ n.children, Fact.term j (d j) ∈ Γ) :
    Sim sem σ (intern n) (n.toTerm d) := by
  apply (intern_sim hI (fun j hj => hΓ.valid (hc j hj))).congr
  exact Node.toTerm_congr n (fun j hj => hΓ.dec (hc j hj))

theorem intern_leaf {n : Node} (hI : Inv sem σ) (hn : n.children = []) :
    Sim sem σ (intern n) (n.toTerm (fun _ => .Stuck)) :=
  intern_ctx (Γ := []) hI (Ctx.nil σ) (by simp [hn])

/-- A cached program: the cache is sound for `sem`, so a hit is correct. -/
theorem cached_ctx {p : Nat} {args : List Id} {body : K Id} {t : Term}
    (hI : Inv sem σ) (hargs : ∀ a ∈ args, a < σ.size)
    (hsem : sem p (args.map σ.decode) = some t) (hbody : Sim sem σ body t) :
    Sim sem σ (cached p args body) t :=
  cached_sim hI hargs hsem hbody

end Kairos
