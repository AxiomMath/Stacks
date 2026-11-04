module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.MonoidalLocalizationFunctors

/-!
# The K-flat complexes of modules on a ringed site as a monoidal subcategory

The K-flat complexes of `O`-modules contain the unit of `Comp(Mod(O))` and are stable under the
total tensor product, so they span a full monoidal subcategory, and the homotopy quotient
carries them into the K-flat objects of `K(Mod(O))`.  This file records that subcategory.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.kFlatQuotient`: the homotopy quotient from the K-flat
  complexes of `O`-modules to the K-flat objects of `K(Mod(O))`.

## Implementation notes

The monoidal datum of `Stacks.SheafOfModules.DerivedMonoidal.kFlatQuotient` is
`Stacks.SheafOfModules.DerivedMonoidal.kFlatQuotientCore`, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/KFlatQuotientTensorator.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
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

end Stacks.SheafOfModules.DerivedMonoidal

end
