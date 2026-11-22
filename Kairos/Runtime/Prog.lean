/-
What generated programs are built from, beyond interning and matching: reading
the store, Logos's builtin `__eo_ite` and `native_ite` (lazy in Kairos),
natives over terms, and the call-site lemmas.
-/
import Kairos.Gen.Prims

namespace Kairos
open Eo Store SmtEval

variable {sem : Sem} {σ : Store} {Γ : List Fact}

/-- Run `f` on the current store, without changing it. -/
@[inline] def withStore {α : Type} (f : Store → K α) : K α := fun σ => f σ σ

theorem Sim.withStore {f : Store → K Id} {t : Term} (h : Sim sem σ (f σ) t) :
    Sim sem σ (Kairos.withStore f) t := h

/-! ## Trying a case

A program tries its cases in order: `kcase (m σ args) rhs rest` runs `rhs`
on what the matcher bound, or `rest`. Proofs split it with `kcase_sim`, which
only sees the case at hand, however many cases follow. -/

@[inline] def kcase {α β : Type} (o : Option α) (f : α → K β) (g : K β) : K β :=
  match o with
  | some v => f v
  | none => g

theorem kcase_sim {α : Type} {o : Option α} {f : α → K Id} {g : K Id} {t : Term}
    (h1 : ∀ v, o = some v → Sim sem σ (f v) t) (h2 : o = none → Sim sem σ g t) :
    Sim sem σ (kcase o f g) t := by
  cases ho : o with
  | some v => exact h1 v ho
  | none => exact h2 ho

/-! ## Natives over terms -/

/-- `native_teq` on ids: equal ids are equal terms. -/
@[inline] def knative_teq (a b : Id) : Bool := decide (a = b)

theorem knative_teq_eq (hI : Inv sem σ) {a b : Id} (ha : a < σ.size) (hb : b < σ.size) :
    knative_teq a b = native_teq (σ.decode a) (σ.decode b) := by
  simp [knative_teq, native_teq, decode_eq_iff hI ha hb]

theorem knative_teq_ctx (hI : Inv sem σ) (hΓ : Ctx σ Γ) {a b : Id} {A B : Term}
    (ha : Fact.term a A ∈ Γ) (hb : Fact.term b B ∈ Γ) :
    knative_teq a b = native_teq A B := by
  rw [knative_teq_eq hI (hΓ.valid ha) (hΓ.valid hb), hΓ.dec ha, hΓ.dec hb]

/-! ## Conditionals: Logos is strict, Kairos evaluates one branch -/

theorem Sim.nite {c : Bool} {mt me : K Id} {T E : Term}
    (ht : c = true → Sim sem σ mt T) (he : c = false → Sim sem σ me E) :
    Sim sem σ (if c then mt else me) (native_ite c T E) := by
  cases c
  · simpa [native_ite] using he rfl
  · simpa [native_ite] using ht rfl

/-- Logos's `__eo_ite` on the id `c`, evaluating only the branch taken. -/
@[inline] def k_ite (c : Id) (mt me : K Id) : K Id := withStore fun σ =>
  match σ.view c with
  | .Boolean true => mt
  | .Boolean false => me
  | _ => pure 0

theorem k_ite_sim (hI : Inv sem σ) (hΓ : Ctx σ Γ) {c : Id} {C T E : Term} {mt me : K Id}
    (hc : Fact.term c C ∈ Γ) (ht : Sim sem σ mt T) (he : Sim sem σ me E) :
    Sim sem σ (k_ite c mt me) (__eo_ite C T E) := by
  apply Sim.withStore
  have hd := hΓ.dec hc
  rw [decode_view' hI c] at hd
  subst hd
  cases hv : σ.view c with
  | Boolean b =>
    cases b
    · simpa [hv, Node.toTerm, __eo_ite, native_ite, native_teq] using he
    · simpa [hv, Node.toTerm, __eo_ite, native_ite, native_teq] using ht
  | _ =>
    apply (Sim.stuck hI).congr
    simp [Node.toTerm, __eo_ite, native_ite, native_teq]

/-! ## Calls

A program's spec says that, on valid ids, it computes the Logos function of
their decodings. At a call site the arguments are known through facts. -/

theorem Sim.call1 {k : Id → K Id} {f : Term → Term}
    (spec : ∀ {σ : Store} {a : Id}, Inv sem σ → a < σ.size → Sim sem σ (k a) (f (σ.decode a)))
    (hI : Inv sem σ) (hΓ : Ctx σ Γ) {a : Id} {A : Term}
    (ha : Fact.term a A ∈ Γ) : Sim sem σ (k a) (f A) :=
  (spec hI (hΓ.valid ha)).congr (by rw [hΓ.dec ha])

theorem Sim.call2 {k : Id → Id → K Id} {f : Term → Term → Term}
    (spec : ∀ {σ : Store} {a b : Id}, Inv sem σ → a < σ.size → b < σ.size →
      Sim sem σ (k a b) (f (σ.decode a) (σ.decode b)))
    (hI : Inv sem σ) (hΓ : Ctx σ Γ) {a b : Id} {A B : Term}
    (ha : Fact.term a A ∈ Γ) (hb : Fact.term b B ∈ Γ) : Sim sem σ (k a b) (f A B) :=
  (spec hI (hΓ.valid ha) (hΓ.valid hb)).congr (by rw [hΓ.dec ha, hΓ.dec hb])

theorem Sim.call3 {k : Id → Id → Id → K Id} {f : Term → Term → Term → Term}
    (spec : ∀ {σ : Store} {a b c : Id}, Inv sem σ → a < σ.size → b < σ.size → c < σ.size →
      Sim sem σ (k a b c) (f (σ.decode a) (σ.decode b) (σ.decode c)))
    (hI : Inv sem σ) (hΓ : Ctx σ Γ) {a b c : Id} {A B C : Term}
    (ha : Fact.term a A ∈ Γ) (hb : Fact.term b B ∈ Γ) (hc : Fact.term c C ∈ Γ) :
    Sim sem σ (k a b c) (f A B C) :=
  (spec hI (hΓ.valid ha) (hΓ.valid hb) (hΓ.valid hc)).congr
    (by rw [hΓ.dec ha, hΓ.dec hb, hΓ.dec hc])

/-- Discharge a hypothesis of a Logos equation lemma `f.eq_k`: that an earlier
case does not match. The facts in context (decoded shapes and earlier
matchers' failures) close it. It leaves the main goal (a `Sim` or `SimR`)
alone at once: `simp_all` there could unfold the program's recursive calls. -/
macro "kdis" : tactic => `(tactic|
  (fail_if_success (show Sim _ _ _ _)
   fail_if_success (show SimR _ _ _ _ _)
   first | assumption | (intros; simp_all)))

end Kairos
