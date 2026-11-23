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

/-- **Kairos is sound.** If Kairos's checker accepts the assumptions `F` and
the commands `C`, the assumptions are unsatisfiable, provided they are in the
fragment Logos's theorem covers (its two translation hypotheses). This is
Logos's `correct___eo_is_refutation`, with Kairos's checker in place of
Logos's. -/
theorem correct___kairos_is_refutation (F : CArgList) (C : CCmdList) :
    TranslatableAssumptionList F ->
    CmdListTranslationOk C ->
    kairos_checker_is_refutation F C = true ->
    eo_satisfiability (argListAssumes F) false :=
  fun htr hok h =>
    correct___eo_is_refutation F C htr hok (eo_is_refutation.intro F C (kairos_refines_logos F C h))

end Kairos.Soundness
