module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsAlongAFunctor
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ForgetEtaleModuleStructure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Homology.DerivedLinear

/-!
# Higher direct images of étale sheaves of `Λ`-modules and of their underlying abelian sheaves

Let `f : X ⟶ Y` be a morphism of schemes and `Λ` a ring. The higher direct images `R^n f_*` of
sheaves of `Λ`-modules on the small étale sites are Mathlib's classical right derived functors of
`Stacks.EtaleCohomology.etaleModuleDirectImage`, while the unbounded derived direct image
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded` is a total right derived functor
on unbounded derived categories. This file records the bridges between these models.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageSingleHomologyIso`:
  `H^n(Rf_*(F[0])) ≅ R^n f_* F` for sheaves of `Λ`-modules, naturally in `F`.
* `Stacks.EtaleCohomology.etaleAbelianDerivedDirectImageSingleHomologyIso`: the same for abelian
  sheaves.
* `Stacks.EtaleCohomology.etaleModuleRightDerivedDirectImageForgetIso`: **the underlying abelian
  sheaf of `R^n f_* F` is `R^n f_*` of the underlying abelian sheaf of `F`**, naturally in `F`
  (the classical-functor form of [Stacks, Tag 0D6J] (3)).

## Main results

* `Stacks.EtaleCohomology.etaleModuleDirectImage_linear`: the direct image of sheaves of
  `Λ`-modules is `Λ`-linear, so its higher direct images are `Λ`-linear too.

## Implementation notes

The comparison is assembled from the derived-category statement
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageForgetIsoUnconditional` and the
identification of `Hⁿ(Rw(X[0]))` with `Rⁿw(X)` of
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, applied on both sides.

## References

* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Injectives.KInjectiveResolution (homotopyCategoryUnit)

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

section

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`H^n(Rf_*(F[0])) ≅ R^n f_* F`** for sheaves of `Λ`-modules on small étale sites, naturally in
`F`: the degree-`n` cohomology sheaf of the unbounded derived direct image of a sheaf placed in
degree `0` is Mathlib's classical higher direct image. -/
def etaleModuleDerivedDirectImageSingleHomologyIso (n : ℕ) :
    DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0 ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
          DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ Y) (n : ℤ) ≅
      (etaleModuleDirectImage.{u, r} Λ f).rightDerived n :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (etaleModuleDirectImage.{u, r} Λ f) (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f)
    (homotopyCategoryUnit _ _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f))
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _) n

/-- **`H^n(Rf_*(A[0])) ≅ R^n f_* A`** for abelian sheaves on small étale sites, naturally in
`A`. -/
def etaleAbelianDerivedDirectImageSingleHomologyIso (n : ℕ) :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) 0 ⋙
        etaleAbelianDerivedDirectImage.{u, r} f ⋙
          DerivedCategory.homologyFunctor
            (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) (n : ℤ) ≅
      (etaleAbelianDirectImage.{u, r} f).rightDerived n :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (etaleAbelianDirectImage.{u, r} f) (etaleAbelianDerivedDirectImage.{u, r} f)
    (etaleAbelianDerivedDirectImageUnit.{u, r} f)
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _) n

/-- **The underlying abelian sheaf of `R^n f_* F` is `R^n f_*` of the underlying abelian sheaf
of `F`**, naturally in the sheaf of `Λ`-modules `F` ([Stacks, Tag 0D6J] (3), for the classical
higher direct images). -/
def etaleModuleRightDerivedDirectImageForgetIso (n : ℕ) :
    (etaleModuleDirectImage.{u, r} Λ f).rightDerived n ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y ≅
      _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X ⋙
        (etaleAbelianDirectImage.{u, r} f).rightDerived n :=
  Functor.isoWhiskerRight (etaleModuleDerivedDirectImageSingleHomologyIso.{u, r} Λ f n).symm
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0 ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f)
      ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ Y).mapDerivedCategoryHomologyIso
        (n : ℤ)).symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0)
      (Functor.isoWhiskerRight (etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ f)
        (DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) (n : ℤ))) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategorySingleFunctor
        (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X) 0)
      (etaleAbelianDerivedDirectImage.{u, r} f ⋙
        DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X)
      (etaleAbelianDerivedDirectImageSingleHomologyIso.{u, r} f n)

end

section Linear

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The direct image of sheaves of `Λ`-modules on small étale sites is `Λ`-linear: it is
restriction of sections along base change. -/
instance etaleModuleDirectImage_linear : Functor.Linear Λ (etaleModuleDirectImage.{u, r} Λ f) where
  map_smul _ _ := rfl

/-- The higher direct images of sheaves of `Λ`-modules on small étale sites are `Λ`-linear. -/
instance etaleModuleDirectImage_rightDerived_linear (n : ℕ) :
    Functor.Linear Λ ((etaleModuleDirectImage.{u, r} Λ f).rightDerived n) :=
  Stacks.DerivedLinear.rightDerived_linear (R := Λ) (etaleModuleDirectImage.{u, r} Λ f) n

end Linear

end Stacks.EtaleCohomology

end
