module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategoryGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftKFlatResolutions
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctor

/-!
# The derived tensor product and the monoidal structure of `D(O)`, at general universes

Let `(C, O)` be a ringed site whose objects live in a universe `c` and whose morphisms and sections
live in the universe `u` of the sheaf of rings. The tensor product of the monoidal structure on
`D(Mod(O))` agrees with the derived tensor bifunctor of K-flat complexes.

## Implementation notes

This is the part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComparisonWithTheDerivedTensorProduct` that
does not need `C` to be a `SmallCategory.{u}`, for a site `C : Type c` with `[Category.{u} C]`; the
statements and proofs are the same, in the namespace
`Stacks.SheafOfModules.DerivedMonoidalGeneral`.
This applies to the small étale ringed site of an algebraic space.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

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

omit [HasDerivedCategory.{d} (Mod R)] in
/-- K-flatness read at `curriedTensor (Mod R)` is K-flatness read at
`Stacks.SheafOfModules.Tensor.sheafTensor R`: the monoidal structure on sheaves of modules is built
from the sheaf tensor product, so the two bifunctors are the same term. -/
theorem curriedTensor_mod_eq_sheafTensor
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    curriedTensor (Mod R) = Stacks.SheafOfModules.Tensor.sheafTensor R := rfl

/-- The tensor product of `Stacks.SheafOfModules.DerivedMonoidalGeneral.derivedMonoidal` is the
localized tensor bifunctor for the K-flat localization. -/
theorem curriedTensor_eq_derivedLocalizedTensor
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    letI := CochainComplex.KFlatBifunctor.kFlatQ_isLocalization (curriedTensor (Mod R))
      (exists_kFlat_resolution R)
    @curriedTensor (DerivedModules R) _ (derivedMonoidal R) =
      CochainComplex.KFlatMonoidal.derivedLocalizedTensor (Mod R) :=
  CochainComplex.KFlatMonoidal.curriedTensor_derivedMonoidal (Mod R)
    (exists_kFlat_resolution R)

/-- **The tensor product of the monoidal derived category of Tag 0FPT is the derived tensor
bifunctor of Tag 06YU.**  No naturality square is checked: both bifunctors descend one
bifunctor on the K-flat objects of `K(Mod(O))` along one pair of localization functors, so
the comparison is `CategoryTheory.Localization.lift₂NatIso` of the identity. -/
def derivedTensorBifunctorIso :
    letI := CochainComplex.KFlatBifunctor.kFlatQ_isLocalization (curriedTensor (Mod R))
      (exists_kFlat_resolution R)
    letI := CochainComplex.KFlatBifunctor.kFlatQLeft_isLocalization (curriedTensor (Mod R))
      (CochainComplex.KFlatMonoidal.exists_kFlatLeft_quasiIso (Mod R)
        (exists_kFlat_resolution R))
    @curriedTensor (DerivedModules R) _ (derivedMonoidal R) ≅
      derivedBifunctor (curriedTensor (Mod R)) :=
  CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso (Mod R) (exists_kFlat_resolution R)

end Stacks.SheafOfModules.DerivedMonoidalGeneral

end
