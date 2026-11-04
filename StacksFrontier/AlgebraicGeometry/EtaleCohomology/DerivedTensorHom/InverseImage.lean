module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.RelativeCupProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparisonOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage

/-!
# The derived inverse image on `D(X_étale, Λ)` and the derived tensor product

For a morphism of schemes `g : X ⟶ Y` and a commutative ring `Λ`, the inverse image `g^{-1}` of
sheaves of `Λ`-modules on small étale sites is exact, so it induces
`g^{-1} : D(Y_étale, Λ) ⥤ D(X_étale, Λ)` degreewise. Read through
`Stacks.EtaleCohomology.etaleDerivedEquivalence`, it is the derived pullback `Lg^*` along the
morphism of constant ringed topoi `(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)`; so it is left adjoint to the
unbounded derived direct image `Rg_*`, and it commutes with the derived tensor product,
`g^{-1}(A ⊗^L_Λ B) ≅ g^{-1}A ⊗^L_Λ g^{-1}B` ([Stacks, Tag 07A4]).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedInverseImage`: `g^{-1}` on `D(Y_étale, Λ)`.
* `Stacks.EtaleCohomology.etaleRingedPullbackIso`: the pullback of sheaves of `Λ̲`-modules along
  the morphism of constant ringed topoi is the étale inverse image.
* `Stacks.EtaleCohomology.etaleRingedDerivedPullbackIso`: the derived pullback `Lg^*` is the
  étale derived inverse image.
* `Stacks.EtaleCohomology.etaleModuleDerivedInverseImageAdj`: `g^{-1} ⊣ Rg_*` on unbounded
  derived categories.
* `Stacks.EtaleCohomology.etaleDerivedInverseImageTensorIso`: `g^{-1}` commutes with `⊗^L_Λ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **The derived inverse image `g^{-1} : D(Y_étale, Λ) ⥤ D(X_étale, Λ)`**, induced degreewise by
the exact inverse image of sheaves of `Λ`-modules. -/
abbrev etaleModuleDerivedInverseImage :
    DerivedCategory (EtaleModules.{u, r} Λ Y) ⥤ DerivedCategory (EtaleModules.{u, r} Λ X) :=
  (etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategory

/-- The morphism of constant ringed topoi underlying `etaleRingedSiteHom`. -/
abbrev etaleRingedToposHom :=
  (etaleRingedSiteHom.{u, r} Λ g).ringedToposHom

/-- The pullback of sheaves of `Λ̲`-modules along the morphism of constant ringed topoi. -/
abbrev etaleRingedPullback :
    EtaleRingedModules.{u, r} Λ Y ⥤ EtaleRingedModules.{u, r} Λ X :=
  (etaleRingedToposHom.{u, r} Λ g).toModulesHom.pullbackModules

/-- The pushforward of sheaves of `Λ̲`-modules along the morphism of constant ringed topoi is the
étale direct image, read through the identifications of `Λ̲`-modules with `Λ`-modules. -/
def etaleRingedPushforwardModulesIso :
    (etaleRingedToposHom.{u, r} Λ g).pushforwardModules ≅
      (etaleModulesEquivalence.{u, r} Λ X).inverse ⋙ etaleModuleDirectImage.{u, r} Λ g ⋙
        (etaleModulesEquivalence.{u, r} Λ Y).functor :=
  (etaleRingedSiteHom.{u, r} Λ g).pushforwardToposIso ≪≫ (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (etaleModulesEquivalence.{u, r} Λ Y).counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleRingedPushforwardIso.{u, r} Λ g)
      (etaleModulesEquivalence.{u, r} Λ Y).functor ≪≫
    Functor.associator _ _ _

/-- **The pullback of sheaves of `Λ̲`-modules is the étale inverse image**, both being left
adjoint to the direct image. -/
def etaleRingedPullbackIso :
    etaleRingedPullback.{u, r} Λ g ≅
      (etaleModulesEquivalence.{u, r} Λ Y).inverse ⋙ etaleModuleInverseImage.{u, r} Λ g ⋙
        (etaleModulesEquivalence.{u, r} Λ X).functor :=
  Adjunction.leftAdjointUniq
    (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
      (etaleRingedToposHom.{u, r} Λ g))
    (((etaleModulesEquivalence.{u, r} Λ Y).symm.toAdjunction.comp
      ((etaleModuleInverseImageAdj.{u, r} Λ g).comp
        (etaleModulesEquivalence.{u, r} Λ X).toAdjunction)).ofNatIsoRight
      (etaleRingedPushforwardModulesIso.{u, r} Λ g).symm)

/-- The pullback of sheaves of `Λ̲`-modules along the morphism of constant ringed topoi preserves
finite limits. -/
instance etaleRingedPullback_preservesFiniteLimits :
    PreservesFiniteLimits (etaleRingedPullback.{u, r} Λ g) :=
  preservesFiniteLimits_of_natIso (etaleRingedPullbackIso.{u, r} Λ g).symm

/-- The pullback of sheaves of `Λ̲`-modules along the morphism of constant ringed topoi preserves
finite colimits. -/
instance etaleRingedPullback_preservesFiniteColimits :
    PreservesFiniteColimits (etaleRingedPullback.{u, r} Λ g) :=
  preservesFiniteColimits_of_natIso (etaleRingedPullbackIso.{u, r} Λ g).symm

/-- The pullback of sheaves of `Λ̲`-modules along the morphism of constant ringed topoi is
additive. -/
instance etaleRingedPullback_additive : (etaleRingedPullback.{u, r} Λ g).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The derived pullback along the morphism of constant ringed topoi exists. -/
local instance etaleRingedPullbackOnHomotopy_hasLeftDerivedFunctor :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy.{max (u + 1) r,
      max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r,
      max (u + 1) r} (etaleRingedToposHom.{u, r} Λ g)).HasLeftDerivedFunctor
      (Stacks.Cohomology.DerivedPullbackOfToposHom.quasiIsoTarget
        (Y := (etaleRingedSite.{u, r} Λ Y).ringedTopos)) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy.{
    max (u + 1) r, max (u + 1) r,
    max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r} (etaleRingedToposHom.{u, r} Λ g)

/-- The derived pullback along the morphism of constant ringed topoi. -/
abbrev etaleRingedDerivedPullback :
    DerivedCategory (EtaleRingedModules.{u, r} Λ Y) ⥤
      DerivedCategory (EtaleRingedModules.{u, r} Λ X) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback.{max (u + 1) r, max (u + 1) r,
    max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r}
    (etaleRingedToposHom.{u, r} Λ g)

/-- **The derived pullback is degreewise pullback**: degreewise pullback is exact, so the functor
it induces on derived categories is a left derived functor of it. -/
def etaleRingedDerivedPullbackMapIso :
    etaleRingedDerivedPullback.{u, r} Λ g ≅ (etaleRingedPullback.{u, r} Λ g).mapDerivedCategory :=
  haveI : (etaleRingedPullback.{u, r} Λ g).mapDerivedCategory.IsLeftDerivedFunctor
      (etaleRingedPullback.{u, r} Λ g).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (EtaleRingedModules.{u, r} Λ Y) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (EtaleRingedModules.{u, r} Λ Y) (ComplexShape.up ℤ)) _
      (etaleRingedPullback.{u, r} Λ g).mapDerivedCategoryFactorsh
  Functor.leftDerivedNatIso (etaleRingedDerivedPullback.{u, r} Λ g)
    (etaleRingedPullback.{u, r} Λ g).mapDerivedCategory
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison.{max (u + 1) r,
      max (u + 1) r, max (u + 1) r, max (u + 1) r,
      max (u + 1) r, max (u + 1) r} (etaleRingedToposHom.{u, r} Λ g))
    (etaleRingedPullback.{u, r} Λ g).mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (EtaleRingedModules.{u, r} Λ Y) (ComplexShape.up ℤ))
    (Iso.refl _)

/-- The underived comparison, in the form the derived one is read off. -/
def etaleRingedPullbackCompIso :
    (etaleModulesEquivalence.{u, r} Λ Y).functor ⋙ etaleRingedPullback.{u, r} Λ g ≅
      etaleModuleInverseImage.{u, r} Λ g ⋙ (etaleModulesEquivalence.{u, r} Λ X).functor :=
  Functor.isoWhiskerLeft _ (etaleRingedPullbackIso.{u, r} Λ g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleModulesEquivalence.{u, r} Λ Y).unitIso.symm _ ≪≫
    Functor.leftUnitor _

/-- **The derived pullback along the morphism of constant ringed topoi is the étale derived
inverse image**: `Φ_Y ⋙ Lg^* ≅ g^{-1} ⋙ Φ_X`. -/
def etaleRingedDerivedPullbackIso :
    (etaleDerivedEquivalence.{u, r} Λ Y).functor ⋙ etaleRingedDerivedPullback.{u, r} Λ g ≅
      etaleModuleDerivedInverseImage.{u, r} Λ g ⋙ (etaleDerivedEquivalence.{u, r} Λ X).functor :=
  Functor.isoWhiskerLeft _ (etaleRingedDerivedPullbackMapIso.{u, r} Λ g) ≪≫
    Dualizing.mapDerivedCategoryCompNatIso _ _ _ (etaleRingedPullbackCompIso.{u, r} Λ g) ≪≫
    (Dualizing.mapDerivedCategoryCompNatIso _ _ _ (Iso.refl _)).symm

/-- **`g^{-1} ⊣ Rg_*` on unbounded derived categories**: the derived adjunction of
[Stacks, Tag 07A6] for the morphism of constant ringed topoi, read on `D(X_étale, Λ)` and
`D(Y_étale, Λ)`. -/
def etaleModuleDerivedInverseImageAdj :
    etaleModuleDerivedInverseImage.{u, r} Λ g ⊣ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g :=
  (((etaleDerivedEquivalence.{u, r} Λ Y).toAdjunction.comp
      ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
          (etaleRingedToposHom.{u, r} Λ g)).comp
        (etaleDerivedEquivalence.{u, r} Λ X).symm.toAdjunction)).ofNatIsoLeft
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (etaleRingedDerivedPullbackIso.{u, r} Λ g) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (etaleDerivedEquivalence.{u, r} Λ X).unitIso.symm ≪≫
        Functor.rightUnitor _)).ofNatIsoRight
    ((Functor.associator _ _ _) ≪≫ (etaleDerivedPushforwardIsoConj.{u, r} Λ g).symm)

/-- **`g^{-1}` commutes with the derived tensor product**, `g^{-1}(A ⊗^L_Λ B) ≅ g^{-1}A ⊗^L_Λ
g^{-1}B`, naturally in `A` and `B`: the comparison of [Stacks, Tag 07A4] for the morphism of
constant ringed topoi, read on `D(X_étale, Λ)` and `D(Y_étale, Λ)`. -/
def etaleDerivedInverseImageTensorIso :
    Functor.uncurry.obj (etaleDerivedTensor.{u, r} Λ Y) ⋙
        etaleModuleDerivedInverseImage.{u, r} Λ g ≅
      (etaleModuleDerivedInverseImage.{u, r} Λ g).prod (etaleModuleDerivedInverseImage.{u, r} Λ g) ⋙
        Functor.uncurry.obj (etaleDerivedTensor.{u, r} Λ X) :=
  TensorHomAdjunction.transportTensorIso (etaleDerivedEquivalence.{u, r} Λ X)
    (etaleDerivedEquivalence.{u, r} Λ Y) (etaleRingedDerivedPullbackIso.{u, r} Λ g)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
      (etaleRingedToposHom.{u, r} Λ g))

end Stacks.EtaleCohomology

end
