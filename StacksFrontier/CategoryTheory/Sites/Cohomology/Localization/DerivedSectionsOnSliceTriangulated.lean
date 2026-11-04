module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfModuleOverObjectEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit

/-!
# Derived sections on a localized site are triangulated

The unbounded derived global sections `RΓ(C/U, -) : D(Mod(R_U)) ⥤ D(Ab)` on the site localized
at an object `U` commute with the shift and send distinguished triangles to distinguished
triangles, both in the single-universe form of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Localization/RestrictionOfModules.lean` and in the
form over a site with large objects.

## Main results

* `Stacks.Cohomology.Localization.derivedSectionsOnSlice_isTriangulated`,
* `Stacks.Cohomology.Localization.OfEssentiallySmall.derivedSectionsOnSlice_isTriangulated`.

## Implementation notes

Both are total right derived functors along `DerivedCategory.Qh`, so both are
`Stacks.Injectives.rightDerivedFunctor_isTriangulated` at the Grothendieck abelianness of the
sheaves of `R_U`-modules on the localized site, which is
`Stacks.Cohomology.Localization.OfEssentiallySmall.isGrothendieckAbelian_slice_modules` in the
essentially small case and `SheafOfModules.isGrothendieckAbelian` in the small one.

On a small site the derived categories are instance arguments, of the functor and of its two
instances here. Over a site with large objects the functor is defined against the standard model
of the derived categories, so that model has to be available in order to apply a general
statement to it; it is introduced in each proof body, never as an instance of this file.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u c

namespace Stacks.Cohomology.Localization

namespace OfEssentiallySmall

variable {C : Type c} [Category.{u} C] [EssentiallySmall.{u} C]
  (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u}) (U : C)

/-- **Derived global sections on the localized site commute with the shift**, over a site whose
objects need not lie in the universe of its morphisms. -/
instance derivedSectionsOnSlice_commShift :
    (derivedSectionsOnSlice J R U).CommShift ℤ := by
  letI := essentiallySmall_over U
  letI := hasSheafify_slice J U
  letI := wEqualsLocallyBijective_slice J U
  letI := isGrothendieckAbelian_slice_modules J R U
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (R.over U))
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  exact Functor.IsRightDerivedFunctor.commShift (derivedSectionsOnSlice J R U)
    ((homotopySectionsOnSlice J R U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (R.over U)) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (R.over U)) (ComplexShape.up ℤ)) ℤ

/-- **Derived global sections on the localized site are triangulated**, over a site whose
objects need not lie in the universe of its morphisms. -/
instance derivedSectionsOnSlice_isTriangulated :
    (derivedSectionsOnSlice J R U).IsTriangulated := by
  let := essentiallySmall_over U
  let := hasSheafify_slice J U
  let := wEqualsLocallyBijective_slice J U
  let := isGrothendieckAbelian_slice_modules J R U
  let := HasDerivedCategory.standard (SheafOfModules.{u} (R.over U))
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  exact Stacks.Injectives.rightDerivedFunctor_isTriangulated (sectionsOnSlice J R U)
    (derivedSectionsOnSlice J R U)
    ((homotopySectionsOnSlice J R U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (R.over U)) (ComplexShape.up ℤ)))

end OfEssentiallySmall

variable (X : AlgebraicGeometry.RingedSite.{u, u, u}) (U : X.C)
  [HasDerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]
  [HasDerivedCategory AddCommGrpCat.{u}]

/-- **Derived global sections on the localized site commute with the shift.** -/
instance derivedSectionsOnSlice_commShift : (derivedSectionsOnSlice X U).CommShift ℤ := by
  letI : HasSheafify (X.J.over U) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} (X.J.over U)
  letI : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} (X.J.over U)
  exact Functor.IsRightDerivedFunctor.commShift (derivedSectionsOnSlice X U)
    ((homotopySectionsOnSlice X U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
        (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
      (ComplexShape.up ℤ)) ℤ

/-- **Derived global sections on the localized site are triangulated.** -/
instance derivedSectionsOnSlice_isTriangulated :
    (derivedSectionsOnSlice X U).IsTriangulated := by
  let : HasSheafify (X.J.over U) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} (X.J.over U)
  let : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} (X.J.over U)
  exact Stacks.Injectives.rightDerivedFunctor_isTriangulated (sectionsOnSlice X U)
    (derivedSectionsOnSlice X U)
    ((homotopySectionsOnSlice X U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
        (ComplexShape.up ℤ)))

end Stacks.Cohomology.Localization

end
