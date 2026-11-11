module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerivedQ
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceCoheratorAssociatedModule
import StacksCore.Tactic.StacksAttribute

/-!
# The derived coherator of an affine algebraic space is the associated complex of `RΓ`

Let `X` be an affine algebraic space over a scheme `S` contained in a big fppf site `B` and set
`A = Γ(X, 𝒪_X)`. The derived coherator `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` of Stacks 08GZ sends an
object `E` of `D(𝒪_X)` to the complex of quasi-coherent `𝒪_X`-modules associated to the object
`RΓ(X, E)` of `D(A)` (Stacks 08H0 (2)). Here `RQ_X` is `AlgebraicGeometry.Space.derivedCoherator`.

## Main definitions

* `AlgebraicGeometry.Space.affineSpaceDerivedGlobalSections`: `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`, the
  total right derived functor of `Γ(X, -)` on the whole unbounded derived category.
* `AlgebraicGeometry.Space.coheratorMapHomologicalComplexIso`: the isomorphism of Stacks 08H0 (1)
  between the coherator and `Γ(X, -) ⋙ (-)^~`, applied degreewise to cochain complexes.
* `AlgebraicGeometry.Space.derivedCoheratorIsoDerivedGlobalSectionsAssociated_of_isAffineSpace`:
  the natural isomorphism `RQ_X ≅ RΓ(X, -) ⋙ (-)^~` of Stacks 08H0 (2).

## Implementation notes

The derived categories are the standard models `CategoryTheory.HasDerivedCategory.standard` and
the localization is `CategoryTheory.DerivedCategory.Q`, as for
`AlgebraicGeometry.Space.derivedCoherator`. The total right derived functors exist because the
`𝒪_X`-modules form a Grothendieck abelian category
(`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`), so every cochain complex of them has a
K-injective resolution.

## References

* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 08GZ](https://stacks.math.columbia.edu/tag/08GZ)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
  isClosedUnderKernels_quasicoherentSheaves_schemeUniverse
  isClosedUnderCokernels_quasicoherentSheaves quasicoherentSheaves_abelian_of_closure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hAffine : IsAffineSpace B S hS F)

/-- **`RΓ(X, -) : D(𝒪_X) ⥤ D(A)`**, the total right derived functor of the global sections of
`𝒪_X`-modules on the whole unbounded derived category. -/
def affineSpaceDerivedGlobalSections :
    DerivedCategory (Modules.{u, u} B S hS F hF) ⥤
      DerivedCategory (ModuleCat.{u} (affineSpaceCoordinateRing B S hS F hAffine)) :=
  letI := isGrothendieckAbelian_modules B S hS F hF
  letI := Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (affineSpaceGlobalSections B S hS F hF hAffine)
  ((affineSpaceGlobalSections B S hS F hF hAffine).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ))

/-- The identification of the coherator with `Γ(X, -) ⋙ (-)^~` of Stacks 08H0 (1), applied
degreewise to cochain complexes. -/
def coheratorMapHomologicalComplexIso :
    (coherator B S hS F hF).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (affineSpaceGlobalSections B S hS F hF hAffine ⋙
        (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).functor).mapHomologicalComplex
          (ComplexShape.up ℤ) where
  hom := NatTrans.mapHomologicalComplex
    (coheratorIsoGlobalSectionsAssociated_of_isAffineSpace B S hS F hF hAffine).hom
    (ComplexShape.up ℤ)
  inv := NatTrans.mapHomologicalComplex
    (coheratorIsoGlobalSectionsAssociated_of_isAffineSpace B S hS F hF hAffine).inv
    (ComplexShape.up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomologicalComplex_comp,
      (coheratorIsoGlobalSectionsAssociated_of_isAffineSpace B S hS F hF hAffine).hom_inv_id,
      NatTrans.mapHomologicalComplex_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomologicalComplex_comp,
      (coheratorIsoGlobalSectionsAssociated_of_isAffineSpace B S hS F hF hAffine).inv_hom_id,
      NatTrans.mapHomologicalComplex_id]

/-- **Stacks 08H0 (2).**  Let `X` be an affine algebraic space over a scheme `S` and set
`A = Γ(X, 𝒪_X)`.  The derived coherator `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` sends an object `E` of
`D(𝒪_X)` to the complex of quasi-coherent `𝒪_X`-modules associated to the object `RΓ(X, E)` of
`D(A)`. -/
@[stacks 08H0 "part (2): for affine X, RQ_X is naturally isomorphic to E ↦ RΓ(X, E)^~ on the \
unbounded derived category"]
def derivedCoheratorIsoDerivedGlobalSectionsAssociated_of_isAffineSpace :
    derivedCoherator B S hS F hF ≅
      affineSpaceDerivedGlobalSections B S hS F hF hAffine ⋙
        (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).functor.mapDerivedCategory :=
  letI := isGrothendieckAbelian_modules B S hS F hF
  letI := Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (affineSpaceGlobalSections B S hS F hF hAffine)
  letI := Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (affineSpaceGlobalSections B S hS F hF hAffine ⋙
      (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).functor)
  Functor.rightDerivedNatIso (derivedCoherator B S hS F hF)
      (((affineSpaceGlobalSections B S hS F hF hAffine ⋙
        (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).functor).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived DerivedCategory.Q
          (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)))
      (derivedCoheratorUnit B S hS F hF)
      (((affineSpaceGlobalSections B S hS F hF hAffine ⋙
        (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).functor).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
          (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)))
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight
        (coheratorMapHomologicalComplexIso B S hS F hF hAffine) DerivedCategory.Q) ≪≫
    (Stacks.Injectives.KInjectiveResolution.totalRightDerivedMapDerivedCategoryIsoQ
      (affineSpaceGlobalSections B S hS F hF hAffine)
      (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).functor).symm

end AlgebraicGeometry.Space

end
