module

public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localizing a linear equivalence

A linear equivalence of modules localizes, at any submonoid of the scalars, to a linear
equivalence of the localized modules over the localized ring.

## Main definitions

* `Module.localizedEquiv`: the localization of a linear equivalence at a submonoid.

## Implementation notes

At `S := p.primeCompl` this is the localization at the prime `p`, since
`Localization p.primeCompl` is `Localization.AtPrime p` by definition. It is unrelated to
`Submodule.localizedEquiv`, which compares the localization of a submodule with a submodule of
the localized module.
-/

@[expose] public noncomputable section

namespace Module

/-- At any submonoid `S` of the scalars, a linear equivalence `M ≃ₗ[R] N` induces a linear
equivalence `LocalizedModule S M ≃ₗ[Localization S] LocalizedModule S N`, the base change of `e`
along `R → Localization S`. -/
def localizedEquiv {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (S : Submonoid R) (e : M ≃ₗ[R] N) :
    LocalizedModule S M ≃ₗ[Localization S] LocalizedModule S N :=
  ((IsLocalizedModule.isBaseChange S (Localization S)
        (LocalizedModule.mkLinearMap S M)).equiv.symm.trans
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (Localization S) (Localization S)) e)).trans
    (IsLocalizedModule.isBaseChange S (Localization S)
      (LocalizedModule.mkLinearMap S N)).equiv

end Module

end
