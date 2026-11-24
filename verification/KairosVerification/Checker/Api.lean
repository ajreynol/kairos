/-
The central theorem: Kairos's checker accepts only what Logos's checker
accepts. It is stated on Logos's values and Kairos's code alone, so reading it
needs nothing of this project: no store invariant, no decoding, no program
logic (KairosVerification/Statement.lean checks that).
-/
import Kairos.Checker.Api
import KairosVerification.Checker.Main

set_option linter.unusedVariables false

namespace Kairos.Checker
open Eo Kairos Store Kairos.Gen

variable {σ : Store} {Γ : List Fact}

theorem internArgs_sim : ∀ (F : CArgList) {σ : Store}, Inv sem σ →
    SimR argsRep sem σ (internArgs F) F
  | .nil, σ, hI => SimR.pure hI trivial rfl
  | .cons t r, σ, hI => by
    simp only [internArgs]
    refine SimR.step (Ctx.nil σ) (SimR.of_sim (internTerm_sim t hI)) fun x σ1 hI1 hΓ1 => ?_
    refine SimR.step hΓ1 (internArgs_sim r hI1) fun r' σ2 hI2 hΓ2 => ?_
    have hx : x < σ2.size ∧ σ2.decode x = t := hΓ2 _ (.tail _ (.head _))
    have hr : r'.valid σ2 ∧ r'.dec σ2 = r := hΓ2 _ (.head _)
    exact SimR.pure hI2 ⟨hx.1, hr.1⟩ (by
      show KArgList.dec σ2 (.cons x r') = _
      simp [KArgList.dec, hx.2, hr.2])

theorem internCmd_sim (c : CCmd) {σ : Store} (hI : Inv sem σ) :
    SimR cmdRep sem σ (internCmd c) c := by
  cases c with
  | assume_push F =>
    simp only [internCmd]
    refine SimR.step (Ctx.nil σ) (SimR.of_sim (internTerm_sim F hI)) fun x σ1 hI1 hΓ1 => ?_
    have hx : x < σ1.size ∧ σ1.decode x = F := hΓ1 _ (.head _)
    exact SimR.pure hI1 hx.1 (by show KCmd.dec σ1 (.assume_push x) = _; simp [KCmd.dec, hx.2])
  | check_proven F =>
    simp only [internCmd]
    refine SimR.step (Ctx.nil σ) (SimR.of_sim (internTerm_sim F hI)) fun x σ1 hI1 hΓ1 => ?_
    have hx : x < σ1.size ∧ σ1.decode x = F := hΓ1 _ (.head _)
    exact SimR.pure hI1 hx.1 (by show KCmd.dec σ1 (.check_proven x) = _; simp [KCmd.dec, hx.2])
  | step r a p =>
    simp only [internCmd]
    refine SimR.step (Ctx.nil σ) (internArgs_sim a hI) fun a' σ1 hI1 hΓ1 => ?_
    have ha : a'.valid σ1 ∧ a'.dec σ1 = a := hΓ1 _ (.head _)
    exact SimR.pure hI1 ha.1 (by show KCmd.dec σ1 (.step r a' p) = _; simp [KCmd.dec, ha.2])
  | step_pop r a p =>
    simp only [internCmd]
    refine SimR.step (Ctx.nil σ) (internArgs_sim a hI) fun a' σ1 hI1 hΓ1 => ?_
    have ha : a'.valid σ1 ∧ a'.dec σ1 = a := hΓ1 _ (.head _)
    exact SimR.pure hI1 ha.1 (by show KCmd.dec σ1 (.step_pop r a' p) = _; simp [KCmd.dec, ha.2])

theorem internCmds_sim : ∀ (C : CCmdList) {σ : Store}, Inv sem σ →
    SimR cmdsRep sem σ (internCmds C) C
  | .nil, σ, hI => SimR.pure hI trivial rfl
  | .cons c cs, σ, hI => by
    simp only [internCmds]
    refine SimR.step (Ctx.nil σ) (internCmd_sim c hI) fun c' σ1 hI1 hΓ1 => ?_
    refine SimR.step hΓ1 (internCmds_sim cs hI1) fun cs' σ2 hI2 hΓ2 => ?_
    have hc : c'.valid σ2 ∧ c'.dec σ2 = c := hΓ2 _ (.tail _ (.head _))
    have hcs : cs'.valid σ2 ∧ cs'.dec σ2 = cs := hΓ2 _ (.head _)
    exact SimR.pure hI2 ⟨hc.1, hcs.1⟩ (by
      show KCmdList.dec σ2 (.cons c' cs') = _
      simp [KCmdList.dec, hc.2, hcs.2])

theorem kairos_check_sim (fuel : Nat) (F : CArgList) (C : CCmdList) :
    SimR (natRep Bool) sem Store.init (kairos_check fuel F C) (__eo_checker_is_refutation F C) := by
  unfold kairos_check
  refine SimR.step (Ctx.nil _) (internArgs_sim F (Inv.init sem)) fun as σ1 hI1 hΓ1 => ?_
  refine SimR.step hΓ1 (internCmds_sim C hI1) fun cs σ2 hI2 hΓ2 => ?_
  have has : as.valid σ2 ∧ as.dec σ2 = F := hΓ2 _ (.tail _ (.head _))
  have hcs : cs.valid σ2 ∧ cs.dec σ2 = C := hΓ2 _ (.head _)
  exact (k_checker_is_refutation_sim fuel hI2 has.1 hcs.1).congr (by rw [has.2, hcs.2])

/-- **Kairos refines Logos.** If Kairos's checker accepts the assumptions `F`
and the commands `C`, so does Logos's checker. -/
theorem kairos_refines_logos (F : CArgList) (C : CCmdList) :
    kairos_checker_is_refutation F C = true → __eo_checker_is_refutation F C = true := by
  intro hb
  have h := kairos_check_sim defaultFuel F C
  rw [kairos_checker_is_refutation_eq] at hb
  unfold SimR Ok at h
  cases hr : kairos_check defaultFuel F C Store.init with
  | ok b σ' =>
    simp only [hr] at hb h
    have e : b = __eo_checker_is_refutation F C := h.dec
    rw [← e]
    exact hb
  | error e σ' =>
    simp [hr] at hb

end Kairos.Checker
