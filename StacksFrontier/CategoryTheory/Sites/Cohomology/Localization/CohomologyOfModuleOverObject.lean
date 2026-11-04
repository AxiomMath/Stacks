module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a module over an object is cohomology on the localized site

Let `(C, O)` be a ringed site, `U` an object of `C` and `F` a sheaf of `O`-modules. Part (2) of
Stacks 03F3 says that the cohomology of `F` over `U` agrees with the cohomology of the
restriction `F|_U` on the localized site `C/U`:

`H^p(U, F) = H^p(C/U, F|_U)`.

Both sides are read off the unbounded derived category, `F` being placed in degree zero:
`H^p(U, -)` is `derivedSectionsOverObject` followed by the `p`-th homology functor, and
`H^p(C/U, -)` is `derivedSectionsOnSlice` followed by the same.

The derived form of the comparison is already available: `derivedSectionsOverObjectIsoSlice`
identifies derived sections over `U` with derived sections on `C/U` of the derived restriction.
What remains is to compute the derived restriction of a module placed in degree zero, and this
is where exactness of restriction enters. Restriction is exact on a ringed site
(`restriction_exact`), so it induces a functor on unbounded derived categories whose comparison
with the degreewise functor is an isomorphism *everywhere*, in particular on K-injective
complexes; uniqueness of right derived functors then identifies that induced functor with the
total right derived restriction. Mathlib's `Functor.mapDerivedCategorySingleFunctor` says the
induced functor commutes with placing an object in degree zero, which turns the derived
restriction of `F` into `F|_U`.

Part (1) of the tag — restriction preserves injectives, which is what makes the cohomology on
`C/U` computable by a resolution restricted from `C` — is
`Stacks.Cohomology.Localization.preservesInjectiveObjects_overFunctor`.

## Main results

* `Stacks.Cohomology.Localization.derivedRestrictionIsoMapDerivedCategory`: the total right
  derived restriction is the functor that exact restriction induces on derived categories.
* `Stacks.Cohomology.Localization.cohomologyOverObjectIsoSlice`: **Stacks 03F3 (2)**, naturally
  in the module.
* `Stacks.Cohomology.Localization.cohomologyOverObjectIsoSliceOfModule`: the same statement for
  one sheaf of modules.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Cohomology.LerayUnbounded

namespace Stacks.Cohomology.Localization

universe u

section RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- The total right derived restriction to the slice site is the functor that restriction, being
exact, induces on unbounded derived categories. Both are right derived functors of degreewise
restriction followed by localization: for the induced functor the comparison is Mathlib's
`Functor.mapDerivedCategoryFactorsh`, which is an isomorphism, hence an isomorphism on
K-injective complexes. -/
noncomputable def derivedRestrictionIsoMapDerivedCategory (X : RingedSite.{u, u, u}) (U : X.C) :
    derivedRestriction X U ≅
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory := by
  let C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let c := ComplexShape.up ℤ
  let G := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let α : homotopyRestriction X U ⟶ DerivedCategory.Qh ⋙ G.mapDerivedCategory :=
    G.mapDerivedCategoryFactorsh.inv
  let := rightDerived_of_kInjectives (homotopyRestriction X U) G.mapDerivedCategory α
    (fun I _ => inferInstance)
  exact Functor.rightDerivedNatIso (derivedRestriction X U) G.mapDerivedCategory
    ((homotopyRestriction X U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso C c))
    α (HomotopyCategory.quasiIso C c) (Iso.refl _)

/-- **Stacks 03F3 (2).** For a ringed site `(C, O)` and an object `U` of `C`, the cohomology
`H^p(U, F)` of a sheaf of `O`-modules over `U` is the cohomology `H^p(C/U, F|_U)` of its
restriction on the site localized at `U`. Both sides place the module in degree zero and take
the `p`-th homology of the corresponding derived sections; the isomorphism is natural in the
module. -/
@[stacks 03F3 "part (2)"]
noncomputable def cohomologyOverObjectIsoSlice (X : RingedSite.{u, u, u}) (U : X.C) (p : ℤ) :
    DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0 ⋙
        derivedSectionsOverObject X U ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} p ≅
      SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
        DerivedCategory.singleFunctor (SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) 0 ⋙
          derivedSectionsOnSlice X U ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} p := by
  let G := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let Hp := DerivedCategory.homologyFunctor AddCommGrpCat.{u} p
  let S := derivedSectionsOnSlice X U ⋙ Hp
  let e₁ : derivedSectionsOverObject X U ⋙ Hp ≅ derivedRestriction X U ⋙ S :=
    Functor.isoWhiskerRight (derivedSectionsOverObjectIsoSlice X U) Hp ≪≫
      Functor.associator _ _ _
  let e₂ : derivedRestriction X U ⋙ S ≅ G.mapDerivedCategory ⋙ S :=
    Functor.isoWhiskerRight (derivedRestrictionIsoMapDerivedCategory X U) S
  exact Functor.isoWhiskerLeft
      (DerivedCategory.singleFunctor (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0) (e₁ ≪≫ e₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapDerivedCategorySingleFunctor 0) S ≪≫
    Functor.associator _ _ _

/-- **Stacks 03F3 (2)**, for one module: the cohomology of `F` over `U` is the cohomology of
`F|_U` on the site localized at `U`. -/
@[stacks 03F3 "part (2), for one module"]
noncomputable def cohomologyOverObjectIsoSliceOfModule (X : RingedSite.{u, u, u}) (U : X.C)
    (p : ℤ) (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).obj
        ((derivedSectionsOverObject X U).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F)) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).obj
        ((derivedSectionsOnSlice X U).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) 0).obj
            (F.over U))) :=
  (cohomologyOverObjectIsoSlice X U p).app F

end RingedSite

end Stacks.Cohomology.Localization

end
