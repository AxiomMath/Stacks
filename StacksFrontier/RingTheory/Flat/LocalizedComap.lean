module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Flatness over the base of a localization at a contracted prime

Let `R → A` be a ring map, `B` a localization of `A` at a submonoid `U`, and `N` an `A`-module
regarded as an `R`-module by restriction. For a prime `q` of `B`, this file identifies the
flatness over `R` of the localization of `N` at the contraction `q ∩ A` with the flatness over
`R` of the localization at `q` of the base change `B ⊗[A] N`.

## Main results

* `Module.flat_localizedModule_atPrime_comap_iff`: flatness over the base of the localization of
  `N` at a contracted prime is the flatness of the localization of the base change.
-/

@[expose] public section

open scoped TensorProduct

namespace Module

/-- Along a localization `A → B`, flatness over `R` of `N` at the prime of `A` under a prime `q`
of `B` is flatness over `R` of the extension of scalars `B ⊗[A] N` at `q`. -/
public theorem flat_localizedModule_atPrime_comap_iff {R A B N : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] (U : Submonoid A)
    [IsLocalization U B] (q : Ideal B) [q.IsPrime] :
    Module.Flat R (LocalizedModule.AtPrime (q.comap (algebraMap A B)) N) ↔
      Module.Flat R (LocalizedModule.AtPrime q (B ⊗[A] N)) := by
  have : IsLocalization (q.comap (algebraMap A B)).primeCompl (Localization.AtPrime q) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization U
      (Localization.AtPrime q) q
  let e₁ := IsLocalizedModule.linearEquiv (q.comap (algebraMap A B)).primeCompl
    (LocalizedModule.mkLinearMap (q.comap (algebraMap A B)).primeCompl N)
    (TensorProduct.mk A (Localization.AtPrime q) N 1)
  let e₂ := (LocalizedModule.equivTensorProduct q.primeCompl (B ⊗[A] N)).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (Localization.AtPrime q)
      (Localization.AtPrime q) N)
  exact (Module.Flat.equiv_iff (e₁.restrictScalars R)).trans
    (Module.Flat.equiv_iff (e₂.restrictScalars R)).symm

end Module

end
