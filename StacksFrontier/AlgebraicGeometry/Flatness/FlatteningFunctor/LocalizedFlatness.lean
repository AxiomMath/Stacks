module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksFrontier.RingTheory.Flat.LocalizedComap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness over a base ring of localized modules

Let `R → A` be a ring map and `M` an `A`-module, regarded as an `R`-module by restriction. The
flatness over `R` of a localization `M_T` is inherited from flatness of `M`, flatness of `M` over
`R` is detected by the localizations at the maximal ideals of `A`, and the flatness of a
localization at a prime is unchanged by an `A`-linear isomorphism of `M`.

## Main results

* `Module.Flat.localizedModule_of_isScalarTower`: a localization of a flat module is flat over
  the base.
* `Module.flat_iff_forall_flat_localizedModule_isMaximal`: flatness over the base is detected by
  the localizations at the maximal ideals.
* `Module.compHom_localizedModule_eq`: restricting the scalars of a localized module along the
  structure map is the same as localizing the restricted module.
* `Module.flat_localizedModule_atPrime_congr`: flatness over the base of a localization at a
  prime is invariant under a linear isomorphism.

## Implementation notes

The two `R`-module structures on `LocalizedModule T M` — the restriction along `R → A` of the
`A`-module structure, and the localization of the restricted `R`-module structure — are equal,
not merely isomorphic (`Module.compHom_localizedModule_eq`).
-/

@[expose] public section

open scoped TensorProduct

namespace Module

/-- A localization of a module which is flat over a base ring is again flat over that base
ring. -/
@[sga "1 IV 1.2"]
public theorem Flat.localizedModule_of_isScalarTower {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (T : Submonoid A) [Module.Flat R M] :
    Module.Flat R (LocalizedModule T M) := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ Q
  have hi : Function.Injective (Q.subtype.lTensor M) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  show Function.Injective
    (TensorProduct.AlgebraTensorModule.lTensor A (LocalizedModule T M) Q.subtype)
  rw [← (inferInstance : IsLocalizedModule T (LocalizedModule.mkLinearMap T M)).map_lTensor A T
    Q.subtype (LocalizedModule.mkLinearMap T M)]
  exact IsLocalizedModule.map_injective T
    (TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T M))
    (TensorProduct.AlgebraTensorModule.rTensor R P (LocalizedModule.mkLinearMap T M)) _ hi

/-- Flatness over a base ring of a module over an algebra is detected by the localizations at
the maximal ideals of the algebra. -/
public theorem flat_iff_forall_flat_localizedModule_isMaximal {R A M : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    [Module A M] [IsScalarTower R A M] :
    Module.Flat R M ↔
      ∀ (P : Ideal A) [P.IsMaximal], Module.Flat R (LocalizedModule P.primeCompl M) :=
  ⟨fun _ P _ ↦ Flat.localizedModule_of_isScalarTower P.primeCompl,
    Module.flat_of_isLocalized_maximal A M (fun P _ ↦ LocalizedModule P.primeCompl M)
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M)⟩

/-- Restricting the scalars of a localized module along the structure map of the algebra is the
same module structure as localizing the restricted module. -/
public theorem compHom_localizedModule_eq {R A N : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] (T : Submonoid A) :
    Module.compHom (LocalizedModule T N) (algebraMap R A) =
      (OreLocalization.instModuleOfIsScalarTower (R₀ := R) (R := A) (X := N) (S := T)) :=
  Module.ext' _ _ fun r n ↦ IsScalarTower.algebraMap_smul (R := R) (A := A) r n

/-- Flatness over the base of a localization at a prime is invariant under an isomorphism of
modules over the algebra. -/
public theorem flat_localizedModule_atPrime_congr {R : Type*} {D : Type*} {M N : Type*}
    [CommRing R] [CommRing D] [Algebra R D] [AddCommGroup M] [Module D M] [Module R M]
    [IsScalarTower R D M] [AddCommGroup N] [Module D N] [Module R N] [IsScalarTower R D N]
    (e : M ≃ₗ[D] N) (p : Ideal D) [p.IsPrime] :
    Module.Flat R (LocalizedModule.AtPrime p M) ↔
      Module.Flat R (LocalizedModule.AtPrime p N) :=
  Module.Flat.equiv_iff ((IsLocalizedModule.mapEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)
    (LocalizedModule.mkLinearMap p.primeCompl N) (Localization.AtPrime p) e).restrictScalars R)

end Module
