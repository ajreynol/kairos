/-
Kairos is sound: if its checker accepts a refutation, the assumptions are
unsatisfiable. This composes Kairos's refinement theorem
(`Kairos.Checker.kairos_refines_logos`, in ../verification) with Logos's
soundness theorem (`correct___eo_is_refutation`, in Logos's verification
project). Nothing else is proved here.

Not built by CI: it needs Logos's verification project and Mathlib.
-/
import KairosVerification
import Cpc.Proofs.Checker

namespace Kairos.Soundness
open Eo Kairos Kairos.Checker

/-- If Kairos's checker returns `true` on assumptions `as` and commands `cs`,
then the assumptions are unsatisfiable, provided they are in the fragment
Logos's theorem covers (its two translation hypotheses). -/
theorem kairos_sound (fuel : Nat) (σ : Store) (hI : Inv Kairos.Gen.sem σ) {as : KArgList}
    {cs : KCmdList} (has : as.valid σ) (hcs : cs.valid σ)
    (htr : TranslatableAssumptionList (as.dec σ)) (hok : CmdListTranslationOk (cs.dec σ)) :
    Ok (k_checker_is_refutation fuel as cs) σ (fun b _ =>
      b = true → eo_satisfiability (argListAssumes (as.dec σ)) false) :=
  Ok.mono (kairos_refines_logos fuel σ hI has hcs) fun _ _ h hb =>
    correct___eo_is_refutation _ _ htr hok (eo_is_refutation.intro _ _ (h hb))

end Kairos.Soundness
