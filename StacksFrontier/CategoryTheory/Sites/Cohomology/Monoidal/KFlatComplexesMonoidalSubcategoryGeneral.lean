module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.MonoidalLocalizationFunctorsGeneral

/-!
# The monoidal subcategory of K-flat complexes, at general universes

Let `(C, O)` be a ringed site whose objects live in a universe `c` and whose morphisms and sections
live in the universe `u` of the sheaf of rings. The K-flat complexes of `O`-modules form a monoidal
subcategory, and its quotient to `D(Mod(O))`.

## Implementation notes

This is the part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.KFlatComplexesMonoidalSubcategory` that does
not need `C` to be a `SmallCategory.{u}`, for a site `C : Type c` with `[Category.{u} C]`; the
statements and proofs are the same, in the namespace
`Stacks.SheafOfModules.DerivedMonoidalGeneral`. This applies to the small étale ringed site of
an algebraic space.

## References

* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor

universe d c u

namespace Stacks.SheafOfModules.DerivedMonoidalGeneral

variable {C : Type c} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  CochainComplex.symmetricCategory

/- The pinned-universe monoidal structures of `CanonicalDerivedTensorComparison`, back in
scope.  `SheafOfModules.monoidalCategorySheafTensor` has sections in `max u v w` for a `w`
that the `u` of `Mod R` does not determine, and the total tensor product below cannot be
reduced through a structure whose universe is still a metavariable. -/
attribute [local instance] monoidalCategoryMod symmetricCategoryMod monoidalPreadditiveMod
  monoidalClosedMod hasTensorMod monoidalComplexes

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal
  CochainComplex.KFlatMonoidal.homotopyBraided
  kFlatQ_isLocalization derivedMonoidal derivedSymmetric

/-! ### The K-flat complexes are a full monoidal subcategory -/

/-- The unit of `Comp(Mod(O))`, the structure sheaf in degree zero, is K-flat. -/
instance : (KFlatComplexes R).ContainsUnit where
  prop_unit := CochainComplex.KFlatMonoidal.kFlat_tensorUnit (Mod R)

/-- The total tensor product of two K-flat complexes of `O`-modules is K-flat. -/
instance : ObjectProperty.TensorLE (KFlatComplexes R) (KFlatComplexes R) (KFlatComplexes R) where
  prop_tensor _ _ h₁ h₂ := CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) h₁ h₂

/-- The K-flat complexes of `O`-modules span a full monoidal subcategory of `Comp(Mod(O))`. -/
instance : (KFlatComplexes R).IsMonoidal where

/-- The homotopy quotient from the K-flat complexes of `O`-modules to the K-flat objects of
`K(Mod(O))`. -/
abbrev kFlatQuotient :
    (KFlatComplexes R).FullSubcategory ⥤
      (kFlatObjects (curriedTensor (Mod R))).FullSubcategory :=
  ObjectProperty.complexSubcategoryQuotient (kFlatObjects (curriedTensor (Mod R)))

end Stacks.SheafOfModules.DerivedMonoidalGeneral

end
