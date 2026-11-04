module

public import StacksFrontier.RingTheory.Dualizing.LocalizationAwayDualizing
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# Transporting a dualizing complex along an exact extension of scalars

When extension of scalars along a ring map `φ` is exact, the derived extension of scalars
`StacksDraft.PseudoCoherence.derivedExtensionScalars φ` is the functor
`(ModuleCat.extendScalars φ).mapDerivedCategory` induced degreewise. Read through this
identification, a dualizing complex extends to a dualizing complex over a localization and along a
ring isomorphism.

## Main definitions

* `Dualizing.derivedExtensionScalarsIsoExtendScalars`: for exact extension of scalars,
  `derivedExtensionScalars φ ≅ (ModuleCat.extendScalars φ).mapDerivedCategory`.
* `Dualizing.extendScalarsCompMapDerivedCategoryIso`: extension of scalars along a composite.
* `Dualizing.extendScalarsIsoLocalizationAwayFunctorAux`: the same comparison at
  `StacksDraft.PseudoCoherence.localizationAwayFunctorAux`.

## Main results

* `Dualizing.isDualizingComplex_extendScalars_of_isLocalization`: the extension of a dualizing
  complex to a localization along `(ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory`
  is dualizing.
* `Dualizing.isDualizingComplex_of_ringEquiv`: a dualizing complex stays dualizing after
  extension of scalars along a ring isomorphism.
* `Dualizing.isDualizingComplex_localizationAway_of_extendScalars`: if the extension of `K` to
  some localization of `A` away from `g` is dualizing, then so is the derived localization of `K`
  away from `g`.

## References

* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A7H](https://stacks.math.columbia.edu/tag/0A7H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.PseudoCoherence (derivedExtensionScalars localizationAwayFunctorAux)
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

section Exact

variable {B C : Type u} [CommRing B] [CommRing C] (φ : B →+* C)
  [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ)]

/-- For exact extension of scalars, the total derived functor of degreewise extension of scalars is
the functor induced degreewise, through the comparison of
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`. -/
@[no_expose] noncomputable def totalDerivedExtensionScalarsIsoExtendScalars :
    (totalDerivedExtensionScalars.{u, u, u} φ).functor ≅
      (ModuleCat.extendScalars φ).mapDerivedCategory := by
  let F := ModuleCat.extendScalars.{u, u, u} φ
  let D := totalDerivedExtensionScalars.{u, u, u} φ
  have : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison
    (W := HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)) (by
      intro X Y g hg
      have : QuasiIso g := hg
      change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map g))
      infer_instance)
  exact Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
    (DerivedCategory.Q ⋙ D.functor) (DerivedCategory.Q ⋙ F.mapDerivedCategory) _ _
    (asIso D.comparison ≪≫ F.mapDerivedCategoryFactors.symm)

/-- Derived extension of scalars along an exact `φ` is the functor induced degreewise on the
derived categories. -/
@[no_expose] noncomputable def derivedExtensionScalarsIsoExtendScalars :
    derivedExtensionScalars.{u, u, u} φ ≅ (ModuleCat.extendScalars φ).mapDerivedCategory :=
  Functor.isoWhiskerRight (uliftDerivedSelfIso B) _ ≪≫ Functor.leftUnitor _ ≪≫
    totalDerivedExtensionScalarsIsoExtendScalars φ

end Exact

/-- The extension of a dualizing complex to a localization, along the functor induced degreewise by
extension of scalars, is a dualizing complex over the localized ring. -/
theorem isDualizingComplex_extendScalars_of_isLocalization {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [IsNoetherianRing A] (S : Submonoid A) [IsLocalization S B]
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K) :
    letI : IsNoetherianRing B := IsLocalization.isNoetherianRing S B inferInstance
    IsDualizingComplex
      ((ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory.obj K) :=
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing S B inferInstance
  isDualizingComplex_of_iso
    ((derivedExtensionScalarsIsoExtendScalars (algebraMap A B)).app K)
    (isDualizingComplex_localization S K hK)

/-- A dualizing complex stays dualizing after extension of scalars along an isomorphism of
rings. -/
theorem isDualizingComplex_of_ringEquiv {B C : Type u} [CommRing B] [CommRing C]
    [IsNoetherianRing B] (e : B ≃+* C)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (e : B →+* C))]
    (ω : DerivedCategory (ModuleCat.{u} B)) (hω : IsDualizingComplex ω) :
    letI : IsNoetherianRing C := isNoetherianRing_of_ringEquiv B e
    IsDualizingComplex ((ModuleCat.extendScalars (e : B →+* C)).mapDerivedCategory.obj ω) := by
  let : Algebra B C := (e : B →+* C).toAlgebra
  have : IsLocalization (Submonoid.powers (1 : B)) C :=
    IsLocalization.away_of_isUnit_of_bijective C isUnit_one e.bijective
  exact isDualizingComplex_extendScalars_of_isLocalization (Submonoid.powers (1 : B)) ω hω

/-- The derived localization away from `g` is the functor induced degreewise by extension of
scalars to `Localization.Away g`. -/
@[no_expose] noncomputable def extendScalarsIsoLocalizationAwayFunctorAux {A : Type u}
    [CommRing A] (g : A)
    [PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away g)))] :
    (ModuleCat.extendScalars
        (algebraMap A (Localization.Away g))).mapDerivedCategory ≅
      localizationAwayFunctorAux.{u, u} g :=
  (derivedExtensionScalarsIsoExtendScalars (algebraMap A (Localization.Away g))).symm ≪≫
    derivedExtensionScalarsIsoLocalizationAway A g

/-- Extension of scalars along a composite of ring maps, on the derived categories: the degreewise
identification `ModuleCat.extendScalarsComp` carried through
`CategoryTheory.Functor.mapDerivedCategory`. -/
@[no_expose] noncomputable def extendScalarsCompMapDerivedCategoryIso {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C)
    (h : ψ.comp φ = χ)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ)]
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} ψ)]
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} χ)] :
    (ModuleCat.extendScalars φ).mapDerivedCategory ⋙
        (ModuleCat.extendScalars ψ).mapDerivedCategory ≅
      (ModuleCat.extendScalars χ).mapDerivedCategory := by
  subst h
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ (ModuleCat.extendScalars ψ).mapDerivedCategory)
    ((ModuleCat.extendScalars (ψ.comp φ)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q) _ _
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ModuleCat.extendScalars ψ).mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp φ ψ).symm _)
        DerivedCategory.Q)

/-- If the extension of `K` to a localization `B` of `A` away from `g` is dualizing, then so is its
extension to `Localization.Away g`. -/
theorem isDualizingComplex_extendScalars_localizationAway {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] (g : A) [IsLocalization.Away g B] [IsNoetherianRing B]
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))]
    [PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away g)))]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDualizingComplex
      ((ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory.obj K)) :
    letI : IsNoetherianRing (Localization.Away g) := isNoetherianRing_of_ringEquiv B
      (IsLocalization.algEquiv (Submonoid.powers g) B (Localization.Away g)).toRingEquiv
    IsDualizingComplex
      ((ModuleCat.extendScalars
        (algebraMap A (Localization.Away g))).mapDerivedCategory.obj K) := by
  let a := IsLocalization.algEquiv (Submonoid.powers g) B (Localization.Away g)
  let : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (a.toRingEquiv : B →+* Localization.Away g)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.Flat.of_bijective a.toRingEquiv.bijective)
  let : IsNoetherianRing (Localization.Away g) := isNoetherianRing_of_ringEquiv B a.toRingEquiv
  exact isDualizingComplex_of_iso
    ((extendScalarsCompMapDerivedCategoryIso (algebraMap A B) _ _
      (RingHom.ext a.commutes)).app K)
    (isDualizingComplex_of_ringEquiv a.toRingEquiv _ hK)

/-- If the extension of `K` to some localization `B` of `A` away from `g` is dualizing over `B`,
then the derived localization of `K` away from `g` is dualizing over `Localization.Away g`. -/
theorem isDualizingComplex_localizationAway_of_extendScalars {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] (g : A) [IsLocalization.Away g B] [IsNoetherianRing B]
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))]
    [PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away g)))]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDualizingComplex
      ((ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory.obj K)) :
    letI : IsNoetherianRing (Localization.Away g) := isNoetherianRing_of_ringEquiv B
      (IsLocalization.algEquiv (Submonoid.powers g) B (Localization.Away g)).toRingEquiv
    IsDualizingComplex ((localizationAwayFunctorAux.{u, u} g).obj K) :=
  let : IsNoetherianRing (Localization.Away g) := isNoetherianRing_of_ringEquiv B
    (IsLocalization.algEquiv (Submonoid.powers g) B (Localization.Away g)).toRingEquiv
  isDualizingComplex_of_iso ((extendScalarsIsoLocalizationAwayFunctorAux g).app K)
    (isDualizingComplex_extendScalars_localizationAway g K hK)

end Dualizing

end
