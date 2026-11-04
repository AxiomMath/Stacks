module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftKFlatResolutions
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctor

/-!
# The tensor product of `D(Mod(O))` is the derived tensor product of Tag 06YU

For a ringed site `(C, O)`, Stacks Tag 0FPT gives `D(Mod(O))` a symmetric monoidal structure
by localizing twice (`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`), while Stacks Tag
06YU gives the derived tensor bifunctor by descending the total tensor product along the two K-flat
localizations (`CochainComplex.KFlatBifunctor.derivedBifunctor`).  This file identifies the two, as
the instance at a ringed site of the generic comparison
`CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso`.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_eq_derivedLocalizedTensor`: the tensor
  product of `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` is Mathlib's localized tensor
  bifunctor, by `rfl`.
* `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso`: the tensor product of
  `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` is isomorphic to
  `CochainComplex.KFlatBifunctor.derivedBifunctor (Stacks.SheafOfModules.Tensor.sheafTensor R)`.

## Implementation notes

The two sides are stated at different spellings of one bifunctor:
`Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` reads K-flatness at
`curriedTensor (Stacks.SheafOfModules.DerivedMonoidal.Mod R)` and Tag 06YU reads it at
`Stacks.SheafOfModules.Tensor.sheafTensor R`.  Those are the same term — the monoidal structure on
sheaves of modules is *built* from `Stacks.SheafOfModules.Tensor.sheafTensor`, which is what
`Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution` already relies on — so no bridge
is needed and the comparison transports verbatim.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

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

omit [HasDerivedCategory.{d} (Mod R)] in
/-- K-flatness read at `curriedTensor (Mod R)` is K-flatness read at
`Stacks.SheafOfModules.Tensor.sheafTensor R`: the monoidal structure on sheaves of modules is built
from the sheaf tensor product, so the two bifunctors are the same term. -/
theorem curriedTensor_mod_eq_sheafTensor :
    curriedTensor (Mod R) = Stacks.SheafOfModules.Tensor.sheafTensor R := rfl

/-- The tensor product of `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` is Mathlib's
localized tensor bifunctor for the K-flat localization. -/
theorem curriedTensor_eq_derivedLocalizedTensor :
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

end Stacks.SheafOfModules.DerivedMonoidal

end
