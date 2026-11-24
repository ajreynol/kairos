/-
Kairos's checker, on Logos's values: the counterpart of Logos's
`__eo_checker_is_refutation`, which the central theorem is stated against.

It interns Logos's argument and command lists into an empty store and runs
the checker. `internArgs` and the others say what interning computes; what runs
is `sharedArgs` and the others, which visit a shared term once
(`Kairos/Runtime/Share.lean`) and compute the same. Running out of fuel makes it answer `false`: Kairos may give up,
it may not be wrong.
-/
import Kairos.Checker.Main
import Kairos.Runtime.Share

namespace Kairos.Checker
open Eo Kairos

def internArgs : CArgList → K KArgList
  | .nil => pure .nil
  | .cons t r => do
    let x ← internTerm t
    let r' ← internArgs r
    pure (.cons x r')

def internCmd : CCmd → K KCmd
  | .assume_push F => do let x ← internTerm F; pure (.assume_push x)
  | .check_proven F => do let x ← internTerm F; pure (.check_proven x)
  | .step r a p => do let a' ← internArgs a; pure (.step r a' p)
  | .step_pop r a p => do let a' ← internArgs a; pure (.step_pop r a' p)

def internCmds : CCmdList → K KCmdList
  | .nil => pure .nil
  | .cons c cs => do
    let c' ← internCmd c
    let cs' ← internCmds cs
    pure (.cons c' cs')

/-- Fuel for the checker: enough for any proof that fits in memory. -/
def defaultFuel : Nat := 2 ^ 62

/-- Intern the assumptions and the commands, then check. -/
def kairos_check (fuel : Nat) (F : CArgList) (C : CCmdList) : K Bool := do
  let as ← internArgs F
  let cs ← internCmds C
  k_checker_is_refutation fuel as cs

/-! ## Interning with sharing -/
theorem internArgs_stable : ∀ F, Stable (internArgs F)
  | .nil => Stable.pure _
  | .cons t r => Stable.bind (internTerm_stable t) fun _ =>
      Stable.bind (internArgs_stable r) fun _ => Stable.pure _

theorem internCmd_stable : ∀ c, Stable (internCmd c)
  | .assume_push F => Stable.bind (internTerm_stable F) fun _ => Stable.pure _
  | .check_proven F => Stable.bind (internTerm_stable F) fun _ => Stable.pure _
  | .step _ a _ => Stable.bind (internArgs_stable a) fun _ => Stable.pure _
  | .step_pop _ a _ => Stable.bind (internArgs_stable a) fun _ => Stable.pure _

theorem internCmds_stable : ∀ cs, Stable (internCmds cs)
  | .nil => Stable.pure _
  | .cons c cs => Stable.bind (internCmd_stable c) fun _ =>
      Stable.bind (internCmds_stable cs) fun _ => Stable.pure _

def sharedArgs : (F : CArgList) → (σ : Store) → TInv σ → Squash (Memo σ) → Shared (internArgs F) σ
  | .nil, σ, _, mm => ⟨.nil, σ, rfl, mm⟩
  | .cons t r, σ, hI, mm =>
    Shared.bind (internTerm_stable t) hI (internShared t σ hI mm) fun x σ1 hI1 mm1 =>
      Shared.bind (internArgs_stable r) hI1 (sharedArgs r σ1 hI1 mm1) fun r' σ2 _ mm2 =>
        ⟨.cons x r', σ2, rfl, mm2⟩

def sharedCmd : (c : CCmd) → (σ : Store) → TInv σ → Squash (Memo σ) → Shared (internCmd c) σ
  | .assume_push F, σ, hI, mm =>
    Shared.bind (internTerm_stable F) hI (internShared F σ hI mm) fun x σ1 _ mm1 =>
      ⟨.assume_push x, σ1, rfl, mm1⟩
  | .check_proven F, σ, hI, mm =>
    Shared.bind (internTerm_stable F) hI (internShared F σ hI mm) fun x σ1 _ mm1 =>
      ⟨.check_proven x, σ1, rfl, mm1⟩
  | .step r a p, σ, hI, mm =>
    Shared.bind (internArgs_stable a) hI (sharedArgs a σ hI mm) fun a' σ1 _ mm1 =>
      ⟨.step r a' p, σ1, rfl, mm1⟩
  | .step_pop r a p, σ, hI, mm =>
    Shared.bind (internArgs_stable a) hI (sharedArgs a σ hI mm) fun a' σ1 _ mm1 =>
      ⟨.step_pop r a' p, σ1, rfl, mm1⟩

def sharedCmds : (cs : CCmdList) → (σ : Store) → TInv σ → Squash (Memo σ) →
    Shared (internCmds cs) σ
  | .nil, σ, _, mm => ⟨.nil, σ, rfl, mm⟩
  | .cons c cs, σ, hI, mm =>
    Shared.bind (internCmd_stable c) hI (sharedCmd c σ hI mm) fun c' σ1 hI1 mm1 =>
      Shared.bind (internCmds_stable cs) hI1 (sharedCmds cs σ1 hI1 mm1) fun cs' σ2 _ mm2 =>
        ⟨.cons c' cs', σ2, rfl, mm2⟩

def internInput (F : CArgList) (C : CCmdList) : K (KArgList × KCmdList) := do
  let as ← internArgs F
  let cs ← internCmds C
  pure (as, cs)

/-- `internInput`, from an empty store. -/
def sharedInput (F : CArgList) (C : CCmdList) : Shared (internInput F C) Store.init :=
  Shared.bind (internArgs_stable F) TInv.init
    (sharedArgs F Store.init TInv.init (Squash.mk ⟨∅, by simp⟩)) fun as σ1 hI1 mm1 =>
      Shared.bind (internCmds_stable C) hI1 (sharedCmds C σ1 hI1 mm1) fun cs σ2 _ mm2 =>
        ⟨(as, cs), σ2, rfl, mm2⟩

/-- Kairos's checker on Logos's values, from an empty store. -/
def kairos_checker_is_refutation (F : CArgList) (C : CCmdList) : Bool :=
  match sharedInput F C with
  | ⟨(as, cs), σ, _, _⟩ =>
    match k_checker_is_refutation defaultFuel as cs σ with
    | .ok b _ => b
    | .error _ _ => false

/-- It runs `kairos_check`. -/
theorem kairos_checker_is_refutation_eq (F : CArgList) (C : CCmdList) :
    kairos_checker_is_refutation F C =
      match kairos_check defaultFuel F C Store.init with
      | .ok b _ => b
      | .error _ _ => false := by
  have h : kairos_check defaultFuel F C =
      internInput F C >>= fun p => k_checker_is_refutation defaultFuel p.1 p.2 := by
    simp only [kairos_check, internInput, bind_assoc, pure_bind]
  unfold kairos_checker_is_refutation
  rw [h]
  split
  rename_i as cs σ e _ _
  rw [bind_ok e]

end Kairos.Checker
