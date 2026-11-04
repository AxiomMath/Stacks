module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleRightDerivedViaPlus
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapSections

/-!
# Two crossings of the models of `Rf_*` at a morphism of schemes

For a morphism of schemes `f : X ⟶ Y`, a sheaf of modules `F` on `X` and a degree `n`, there are
two isomorphisms `H^n(Rf_*(F[0])) ≅ R^n f_* F`: `homologyFunctorDerivedPushforwardIso`, read
through `CategoryTheory.Functor.boundedDerivedIso` at the direct image, and
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, read off the chosen
injective resolution and landing in Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`.
This file identifies them, up to the comparison `Stacks.DerivedIndexing.rightDerivedIso` of the
two indexings of the right derived functors.

## Main results

* `singleCompDerivedCompHomologyIsoRightDerived_hom_app_eq`: the second isomorphism is the first
  followed by the inverse of `Stacks.DerivedIndexing.rightDerivedIso`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open DerivedCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- Sheaves of modules on a ringed space have enough injectives. -/
local instance moduleSheaves_enoughInjectives (Z : RingedSpace.{u, u}) :
    EnoughInjectives (SheafOfModules.{u} (structureSheafRing Z)) :=
  SheafOfModules.enoughInjectivesU.{u, u, u} (structureSheafRing Z)

variable {X Y : Scheme.{u}}

/-- For a morphism of schemes `f : X ⟶ Y`, a sheaf of modules `F` on `X` and a degree `n`, the
isomorphism `H^n(Rf_*(F[0])) ≅ R^n f_* F` read off the chosen injective resolution is
`homologyFunctorDerivedPushforwardIso f F n` followed by the inverse of
`Stacks.DerivedIndexing.rightDerivedIso`. -/
theorem singleCompDerivedCompHomologyIsoRightDerived_hom_app_eq (f : X ⟶ Y) (F : X.Modules)
    (n : ℕ) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
          (modulePushforward f.toLRSHom.toShHom) (derivedPushforward f.toLRSHom.toShHom)
          (derivedPushforwardUnit f.toLRSHom.toShHom)
          (exists_quasiIso_isKInjective X.toRingedSpace) n).hom.app F =
      (homologyFunctorDerivedPushforwardIso f F (n : ℤ)).hom ≫
        (Stacks.DerivedIndexing.rightDerivedIso
          (modulePushforward f.toLRSHom.toShHom) n).inv.app F :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_boundedDerivedIso
    (modulePushforward f.toLRSHom.toShHom) (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (exists_quasiIso_isKInjective X.toRingedSpace) n F

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
