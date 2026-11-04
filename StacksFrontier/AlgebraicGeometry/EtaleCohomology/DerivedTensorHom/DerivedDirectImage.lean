module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.DirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedPushforwardToposComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact

/-!
# The unbounded derived direct image along the morphism of constant ringed sites

For a morphism of schemes `f : X ⟶ Y` and a commutative ring `Λ`, the unbounded derived direct
image `Rf_* : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of sheaves of `Λ`-modules
(`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded`) is, through the equivalences
`Stacks.EtaleCohomology.etaleDerivedEquivalence`, the unbounded derived direct image along the
morphism of ringed topoi `(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)` underlying
`Stacks.EtaleCohomology.etaleRingedSiteHom`.

## Main definitions

* `Stacks.EtaleCohomology.etaleRingedDerivedPushforward`: the derived direct image along the
  morphism of constant ringed topoi.
* `Stacks.EtaleCohomology.etaleDerivedPushforwardIso`: the comparison
  `Rf_* ⋙ Φ_Y ≅ Φ_X ⋙ Rf_*`.

## Implementation notes

Both sides are right derived functors of `f_*` along the localization of cochain complexes of
sheaves of `Λ`-modules on `X_étale`: the étale one by construction, the other because its unit,
assembled from the comparison of underived direct images
`Stacks.EtaleCohomology.etaleRingedPushforwardIso` and the unit of the ringed-topos derived
direct image, is invertible at every K-injective complex
(`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Injectives.KInjectiveResolution (invertsQuasiIso_mapHomologicalComplex_comp_Q)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The direct image of sheaves of modules along the morphism of constant ringed sites is
additive (`AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive`). -/
local instance etaleRingedPushforwardTopos_additive :
    (etaleRingedSiteHom.{u, r} Λ f).toRingedToposSiteHom.pushforwardTopos.Additive :=
  AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive _

/-- **The unbounded derived direct image along the morphism of constant ringed topoi**
`(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)`. -/
abbrev etaleRingedDerivedPushforward :
    DerivedCategory (EtaleRingedModules.{u, r} Λ X) ⥤
      DerivedCategory (EtaleRingedModules.{u, r} Λ Y) :=
  Stacks.Cohomology.DerivedPushforward.derivedPushforward.{max (u + 1) r, max (u + 1) r,
    max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r}
    (etaleRingedSiteHom.{u, r} Λ f).ringedToposHom

/-- The degreewise direct image along the morphism of constant ringed topoi, on the homotopy
category, followed by the localization. -/
abbrev etaleRingedPushforwardOnHomotopy :=
  Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy.{max (u + 1) r, max (u + 1) r,
    max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r}
    (etaleRingedSiteHom.{u, r} Λ f).ringedToposHom

/-- The unit of `etaleRingedDerivedPushforward`. -/
abbrev etaleRingedDerivedPushforwardUnit :
    etaleRingedPushforwardOnHomotopy.{u, r} Λ f ⟶
      DerivedCategory.Qh ⋙ etaleRingedDerivedPushforward.{u, r} Λ f :=
  (etaleRingedPushforwardOnHomotopy.{u, r} Λ f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (EtaleRingedModules.{u, r} Λ X) (ComplexShape.up ℤ))

/-- The first half of the unit of the comparison: the étale direct image of complexes, localized,
is the ringed-topos direct image on the homotopy category applied to the transported complex,
read back on `D(Y_étale, Λ)`. -/
def etaleDerivedPushforwardComparisonIso :
    (etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ≅
      ((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient _ (ComplexShape.up ℤ)) ⋙
        etaleRingedPushforwardOnHomotopy.{u, r} Λ f ⋙
          (etaleDerivedEquivalence.{u, r} Λ Y).inverse :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      ((etaleModulesEquivalence.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).unitIso _ ≪≫
    Functor.isoWhiskerLeft ((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
      (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex
          (etaleRingedPushforwardIso.{u, r} Λ f).symm (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
        Functor.isoWhiskerLeft
          ((etaleRingedSiteHom.{u, r} Λ f).toRingedToposSiteHom.pushforwardTopos
            |>.mapHomologicalComplex (ComplexShape.up ℤ))
          (etaleModulesEquivalence.{u, r} Λ Y).inverse.mapDerivedCategoryFactors.symm ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft
          ((etaleRingedSiteHom.{u, r} Λ f).toRingedToposSiteHom.pushforwardTopos
            |>.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso _).symm ≪≫
          Functor.isoWhiskerRight
            ((etaleRingedSiteHom.{u, r} Λ f).toRingedToposSiteHom.pushforwardTopos
              |>.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
          Functor.isoWhiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
            (Functor.isoWhiskerRight
              (etaleRingedSiteHom.{u, r} Λ f).pushforwardHomotopyToposIso.symm DerivedCategory.Qh))
          (etaleDerivedEquivalence.{u, r} Λ Y).inverse)

/-- The second half of the unit of the comparison: localizing the transported complex. -/
def etaleDerivedEquivalenceFactorsIso :
    ((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient _ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Qh ≅
      DerivedCategory.Q ⋙ (etaleDerivedEquivalence.{u, r} Λ X).functor :=
  Functor.isoWhiskerLeft ((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)) (DerivedCategory.quotientCompQhIso _) ≪≫
    (etaleModulesEquivalence.{u, r} Λ X).functor.mapDerivedCategoryFactors.symm

/-- The unit exhibiting `Φ_X ⋙ Rf_* ⋙ Φ_Y⁻¹` as a right derived functor of the étale `f_*`. -/
def etaleDerivedPushforwardComparisonUnit :
    (etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (etaleDerivedEquivalence.{u, r} Λ X).functor ⋙
        etaleRingedDerivedPushforward.{u, r} Λ f ⋙ (etaleDerivedEquivalence.{u, r} Λ Y).inverse :=
  (etaleDerivedPushforwardComparisonIso.{u, r} Λ f).hom ≫
    Functor.whiskerLeft ((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (Functor.whiskerRight (etaleRingedDerivedPushforwardUnit.{u, r} Λ f)
        (etaleDerivedEquivalence.{u, r} Λ Y).inverse) ≫
    Functor.whiskerRight (etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := X)).hom
      (etaleRingedDerivedPushforward.{u, r} Λ f ⋙ (etaleDerivedEquivalence.{u, r} Λ Y).inverse)

/-- The unit `etaleDerivedPushforwardComparisonUnit` is an isomorphism at every K-injective
complex of étale modules. -/
theorem isIso_etaleDerivedPushforwardComparisonUnit_app
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (hK : K.IsKInjective) :
    IsIso ((etaleDerivedPushforwardComparisonUnit.{u, r} Λ f).app K) := by
  have : CochainComplex.IsKInjective
      (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
    have := hK
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence _ K
  have : IsIso ((etaleRingedDerivedPushforwardUnit.{u, r} Λ f).app
      (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ _ _ _ _ this
  simp only [etaleDerivedPushforwardComparisonUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- `Φ_X ⋙ Rf_* ⋙ Φ_Y⁻¹` is a right derived functor of the étale direct image `f_*`. -/
instance etaleDerivedPushforwardComparison_isRightDerivedFunctor :
    ((etaleDerivedEquivalence.{u, r} Λ X).functor ⋙ etaleRingedDerivedPushforward.{u, r} Λ f ⋙
        (etaleDerivedEquivalence.{u, r} Λ Y).inverse).IsRightDerivedFunctor
      (etaleDerivedPushforwardComparisonUnit.{u, r} Λ f)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) :=
  (Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective
    DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (etaleModuleDirectImage.{u, r} Λ f))).2
    (isIso_etaleDerivedPushforwardComparisonUnit_app.{u, r} Λ f)

/-- **The étale unbounded derived direct image is the ringed-topos one**:
`Rf_* ≅ Φ_X ⋙ Rf_* ⋙ Φ_Y⁻¹`, both being right derived functors of `f_*`. -/
def etaleDerivedPushforwardIsoConj :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ≅
      (etaleDerivedEquivalence.{u, r} Λ X).functor ⋙ etaleRingedDerivedPushforward.{u, r} Λ f ⋙
        (etaleDerivedEquivalence.{u, r} Λ Y).inverse :=
  Functor.rightDerivedUnique _ _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)
    (etaleDerivedPushforwardComparisonUnit.{u, r} Λ f)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

/-- **The étale unbounded derived direct image is the ringed-topos one**:
`Rf_* ⋙ Φ_Y ≅ Φ_X ⋙ Rf_*`. -/
def etaleDerivedPushforwardIso :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        (etaleDerivedEquivalence.{u, r} Λ Y).functor ≅
      (etaleDerivedEquivalence.{u, r} Λ X).functor ⋙ etaleRingedDerivedPushforward.{u, r} Λ f :=
  Functor.isoWhiskerRight (etaleDerivedPushforwardIsoConj.{u, r} Λ f) _ ≪≫
    Functor.isoWhiskerLeft ((etaleDerivedEquivalence.{u, r} Λ X).functor ⋙
      etaleRingedDerivedPushforward.{u, r} Λ f) (etaleDerivedEquivalence.{u, r} Λ Y).counitIso ≪≫
    Functor.rightUnitor _

end Stacks.EtaleCohomology

end
