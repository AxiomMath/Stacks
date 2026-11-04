module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Localizing a module in two steps

Localizing `T⁻¹N` at a prime `P` of `T⁻¹B` localizes `N` at the contraction of `P` to `B`.
-/

@[expose] public section

namespace Stacks

variable {B : Type*} [CommRing B] (T : Submonoid B) (N : Type*) [AddCommGroup N] [Module B N]

/-- Localizing `T⁻¹N` at a prime `P` of `T⁻¹B` localizes `N` at the contraction of `P` to `B`:
both steps are base changes, and so is their composite. -/
theorem isLocalizedModule_comp_mkLinearMap (P : Ideal (Localization T)) [P.IsPrime] :
    IsLocalizedModule (P.comap (algebraMap B (Localization T))).primeCompl
      (((LocalizedModule.mkLinearMap P.primeCompl (LocalizedModule T N)).restrictScalars B).comp
        (LocalizedModule.mkLinearMap T N)) :=
  (isLocalizedModule_iff_isBaseChange _ (Localization.AtPrime P) _).mpr
    ((LocalizedModule.isBaseChange T N).comp (LocalizedModule.isBaseChange P.primeCompl _))

end Stacks

end
