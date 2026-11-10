module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparisonGeneral

/-!
# The canonical unit isomorphism of the derived tensor product, at general universes

Let `(C, O)` be a ringed site whose objects live in a universe `c` and whose morphisms and sections
live in the universe `u` of the sheaf of rings. The unit of the monoidal structure of `D(Mod(O))`
is the structure sheaf in degree zero.

## Implementation notes

This is the part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat` that
does not need `C` to be a `SmallCategory.{u}`, for a site `C : Type c` with `[Category.{u} C]`; the
statements and proofs are the same, in the namespace
`Stacks.SheafOfModules.DerivedMonoidalGeneral`. This applies to the small étale ringed site of an
algebraic space.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

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

/-- **The unit of the monoidal derived category of Tag 0FPT is the structure sheaf in degree
zero.**  This is `CochainComplex.KFlatMonoidal.derivedUnitIso`, read with the single-object
functor of `DerivedCategory` in place of `DerivedCategory.Q` of the single-object functor of
`CochainComplex`: `DerivedCategory.singleFunctorIsoCompQ` is `Iso.refl`, and Tag 0FPQ's
`unit_eq_structureSheaf` is `rfl`. -/
def canonicalUnitIso :
    letI := derivedMonoidal R
    𝟙_ (DerivedModules R) ≅
      (DerivedCategory.singleFunctor (Mod R) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} R)) :=
  CochainComplex.KFlatMonoidal.derivedUnitIso (Mod R) (exists_kFlat_resolution R)

end Stacks.SheafOfModules.DerivedMonoidalGeneral

end
