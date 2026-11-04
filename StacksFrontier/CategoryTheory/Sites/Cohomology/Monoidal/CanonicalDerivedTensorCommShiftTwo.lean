module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison
public import StacksFrontier.Homology.KFlat.BifunctorCommShiftTwoInstances
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoOfIso
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product of a ringed site commutes with the shifts in both variables

Let `(C, O)` be a ringed site.  `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R` is
the bifunctor `⊗^L_O : D(Mod(O)) ⥤ D(Mod(O)) ⥤ D(Mod(O))` of [Stacks, Tag 06YU] as every consumer
of the derived tensor product names it.  Its `CategoryTheory.Functor.CommShift₂Int` instance is
the structure field `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift₂` of the
canonical derived tensor product.  This file builds a second description of the datum,
transported from `CochainComplex.KFlatBifunctor.derivedBifunctor`, which is what moving a
statement between the two bifunctors needs.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`: **the canonical derived
  tensor product of [Stacks, Tag 06YU] commutes with the shifts in both variables**, with the
  datum transported along `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`.

## Implementation notes

`canonicalTensor_commShift₂Int` is a `def`, not an instance.  As an instance it formed a diamond
with the structure field, which instance search also finds on `derivedTensorProductFunctor R` (an
`abbrev` of the canonical structure's `tensor`): the two data are not definitionally equal, and
which one a declaration saw depended on its imports.
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq` proves them
equal, and `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso_commShift₂`, the
shift-compatibility of the comparison for the field's datum, follows from it; both are in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwoField`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
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

attribute [local instance] kFlatQ_isLocalization kFlatQLeft_isLocalization

/-- The K-flat derived bifunctor of the tensor product of `O`-modules commutes with the shifts in
both variables.  This is `CochainComplex.KFlatBifunctor.derivedBifunctor_commShift₂Int` at
`curriedTensor (Mod R)`, named here so that the transport below has a term to start from and so
that the two localization instances it needs are recorded in one place. -/
instance derivedBifunctor_commShift₂Int :
    (derivedBifunctor (curriedTensor (Mod R))).CommShift₂Int := inferInstance

/-- **The canonical derived tensor product of [Stacks, Tag 06YU] commutes with the shifts in both
variables**, with Mathlib's sign `(-1) ^ (p * q)`: the datum of
`CochainComplex.KFlatBifunctor.derivedBifunctor`, transported along
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`.

It is a `def`, not an instance: the instance on
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R` is the structure field
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift₂`, which
`canonicalDerivedTensorProduct_commShift₂_eq` identifies with this datum. -/
@[instance_reducible, stacks 06YU "compatibility with the shifts in both variables"]
def canonicalTensor_commShift₂Int :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R).CommShift₂Int :=
  Functor.CommShift₂.ofIsoInt (canonicalTensorIso R)

end Stacks.SheafOfModules.DerivedMonoidal

end
