module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.KFlatComplexesMonoidalSubcategoryGeneral

/-!
# The tensorator of the K-flat quotient, at general universes

Let `(C, O)` be a ringed site whose objects live in a universe `c` and whose morphisms and
sections live in the universe `u` of the sheaf of rings. The comparison of tensor products along
the quotient of the K-flat complexes of `O`-modules.

## Implementation notes

This is the part of `StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.KFlatQuotientTensorator`
that does not need `C` to be a `SmallCategory.{u}`, for a site `C : Type c` with
`[Category.{u} C]`; the statements and proofs are the same, in the namespace
`Stacks.SheafOfModules.DerivedMonoidalGeneral`. This applies to the small étale ringed site of an
algebraic space.

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
that the `u` of `Mod R` does not determine, and the tensorator below cannot be synthesized
through a structure whose universe is still a metavariable. -/
attribute [local instance] monoidalCategoryMod symmetricCategoryMod monoidalPreadditiveMod
  monoidalClosedMod hasTensorMod monoidalComplexes

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal
  CochainComplex.KFlatMonoidal.homotopyBraided
  kFlatQ_isLocalization derivedMonoidal derivedSymmetric

attribute [local instance] homQMonoidal homQBraided kFlatQMonoidal kFlatQBraided

/-- The monoidal data of `kFlatQuotient`: its tensorator is that of the homotopy quotient, and
each coherence is the corresponding coherence of the homotopy quotient, read through the
faithful inclusion of the K-flat objects. -/
def kFlatQuotientCore : (kFlatQuotient R).CoreMonoidal where
  εIso := Iso.refl _
  μIso X Y :=
    (kFlatObjects (curriedTensor (Mod R))).isoMk
      (CochainComplex.KFlatMonoidal.homotopyMu (Mod R) X.1 Y.1)
  μIso_hom_natural_left f X' :=
    (kFlatObjects (curriedTensor (Mod R))).ι.map_injective
      (Functor.LaxMonoidal.μ_natural_left (F := homQ R) f.hom X'.1)
  μIso_hom_natural_right X' f :=
    (kFlatObjects (curriedTensor (Mod R))).ι.map_injective
      (Functor.LaxMonoidal.μ_natural_right (F := homQ R) X'.1 f.hom)
  associativity X Y Z :=
    (kFlatObjects (curriedTensor (Mod R))).ι.map_injective
      (Functor.LaxMonoidal.associativity (homQ R) X.1 Y.1 Z.1)
  left_unitality X :=
    (kFlatObjects (curriedTensor (Mod R))).ι.map_injective
      (Functor.LaxMonoidal.left_unitality (homQ R) X.1)
  right_unitality X :=
    (kFlatObjects (curriedTensor (Mod R))).ι.map_injective
      (Functor.LaxMonoidal.right_unitality (homQ R) X.1)

end Stacks.SheafOfModules.DerivedMonoidalGeneral

end
