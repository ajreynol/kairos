/-
Computations of values of any representation, not only term ids.

`SimR rep sem σ m t`: run in a store with the invariant, `m` returns a value
that stands for the Logos value `t` under `rep`. `Sim` (term ids) is the
instance `SimR termRep`, see `SimR.of_sim`. Checker states, argument lists and
native results (`natRep`) use the same step lemmas.
-/
import KairosVerification.Gen.Intern

namespace Kairos
open Eo Store SmtEval

variable {sem : Sem} {σ : Store} {Γ : List Fact}

structure PostR {α β : Type} (rep : RepD α β) (sem : Sem) (σ : Store) (t : β) (r : α)
    (σ' : Store) : Prop where
  inv : Inv sem σ'
  ext : Extends σ σ'
  valid : rep.valid σ' r
  dec : rep.dec σ' r = t

def SimR {α β : Type} (rep : RepD α β) (sem : Sem) (σ : Store) (m : K α) (t : β) : Prop :=
  Ok m σ (PostR rep sem σ t)

/-- Native values stand for themselves. -/
def natRep (β : Type) : RepD β β where
  dec _ b := b
  valid _ _ := True
  mono _ _ _ := ⟨trivial, rfl⟩

theorem SimR.of_sim {m : K Id} {t : Term} (h : Sim sem σ m t) : SimR termRep sem σ m t :=
  Ok.mono h fun _ _ p => ⟨p.inv, p.ext, p.valid, p.dec⟩

theorem SimR.to_sim {m : K Id} {t : Term} (h : SimR termRep sem σ m t) : Sim sem σ m t :=
  Ok.mono h fun _ _ p => ⟨p.inv, p.ext, p.valid, p.dec⟩

theorem SimR.congr {α β : Type} {rep : RepD α β} {m : K α} {t t' : β}
    (h : SimR rep sem σ m t) (e : t = t') : SimR rep sem σ m t' := e ▸ h

theorem SimR.bind {α₁ β₁ α₂ β₂ : Type} {rep₁ : RepD α₁ β₁} {rep₂ : RepD α₂ β₂}
    {m : K α₁} {k : α₁ → K α₂} {t : β₁} {u : β₂}
    (hm : SimR rep₁ sem σ m t)
    (hk : ∀ r σ', PostR rep₁ sem σ t r σ' → SimR rep₂ sem σ' (k r) u) :
    SimR rep₂ sem σ (m >>= k) u := by
  apply Ok.bind
  apply Ok.mono hm
  intro r σ' hp
  exact Ok.mono (hk r σ' hp) fun _ _ h => ⟨h.inv, hp.ext.trans h.ext, h.valid, h.dec⟩

/-- Compute a value, then continue knowing what it stands for. -/
theorem SimR.step {α₁ β₁ α₂ β₂ : Type} {rep₁ : RepD α₁ β₁} {rep₂ : RepD α₂ β₂}
    {m : K α₁} {k : α₁ → K α₂} {t : β₁} {u : β₂}
    (hΓ : Ctx σ Γ) (hm : SimR rep₁ sem σ m t)
    (hk : ∀ r σ', Inv sem σ' → Ctx σ' (⟨rep₁, r, t⟩ :: Γ) → SimR rep₂ sem σ' (k r) u) :
    SimR rep₂ sem σ (m >>= k) u :=
  SimR.bind hm fun r σ' hp => hk r σ' hp.inv (Ctx.cons ⟨hp.valid, hp.dec⟩ (hΓ.mono hp.ext))

theorem SimR.pure {α β : Type} {rep : RepD α β} {r : α} {t : β} (hI : Inv sem σ)
    (hv : rep.valid σ r) (hd : rep.dec σ r = t) : SimR rep sem σ (Pure.pure r) t :=
  ⟨hI, Extends.refl σ, hv, hd⟩

theorem SimR.ret {α β : Type} {rep : RepD α β} {r : α} {t : β} (hI : Inv sem σ)
    (hΓ : Ctx σ Γ) (h : (⟨rep, r, t⟩ : Fact) ∈ Γ) : SimR rep sem σ (Pure.pure r) t :=
  SimR.pure hI (hΓ _ h).1 (hΓ _ h).2

theorem SimR.native {β : Type} {b : β} (hI : Inv sem σ) :
    SimR (natRep β) sem σ (Pure.pure b) b :=
  SimR.pure hI trivial rfl

theorem SimR.withStore {α β : Type} {rep : RepD α β} {f : Store → K α} {t : β}
    (h : SimR rep sem σ (f σ) t) : SimR rep sem σ (Kairos.withStore f) t := h

theorem SimR.ite {α β : Type} {rep : RepD α β} {c : Prop} [Decidable c] {mt me : K α} {t : β}
    (ht : c → SimR rep sem σ mt t) (he : ¬ c → SimR rep sem σ me t) :
    SimR rep sem σ (if c then mt else me) t := by
  by_cases h : c
  · simpa [h] using ht h
  · simpa [h] using he h

/-- What a fact about a native value says: it is that value. -/
theorem Ctx.native {β : Type} {b b' : β} (hΓ : Ctx σ Γ)
    (h : (⟨natRep β, b, b'⟩ : Fact) ∈ Γ) : b = b' :=
  (hΓ _ h).2

end Kairos
