module

public import StacksFrontier.RingTheory.Length.LocalizationModelIndependence
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# The length of a localized quotient

For a commutative ring `A`, a prime `p` and an `A`-module `M` isomorphic to `A ⧸ J`, the length of
the localization `M_p` over `A_p` is the colength of the extended ideal `J A_p`.

## Main results

* `Module.length_localizedModule_eq_length_quotient_map`.
-/

@[expose] public section

namespace Module

variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] {M : Type*} [AddCommGroup M]
  [Module A M]

/-- The length over `A_p` of the localization at `p` of a module isomorphic to `A ⧸ J` is the
length of `T ⧸ J T`, for any localization `T` of `A` at `p`. -/
theorem length_localizedModule_eq_length_quotient_map (T : Type*) [CommRing T] [Algebra A T]
    [IsLocalization p.primeCompl T] (J : Ideal A) (e : M ≃ₗ[A] A ⧸ J) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M) =
      Module.length T (T ⧸ J.map (algebraMap A T)) := by
  let f : A ⧸ J →ₗ[A] T ⧸ Submodule.localized' T p.primeCompl (Algebra.linearMap A T) J :=
    Submodule.toLocalizedQuotient' T p.primeCompl (Algebra.linearMap A T) J
  have : IsLocalizedModule p.primeCompl (f ∘ₗ e.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right p.primeCompl f e
  rw [Module.length_eq_of_isLocalization_of_isLocalizedModule p.primeCompl T (f ∘ₗ e.toLinearMap)]
  rw [Ideal.localized'_eq_map]

end Module

end
