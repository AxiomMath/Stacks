module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SubcategoryLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparisonGeneral

/-!
# Monoidal localization functors to `D(Mod(O))`, at general universes

Let `(C, O)` be a ringed site whose objects live in a universe `c` and whose morphisms and sections
live in the universe `u` of the sheaf of rings. The localization functors from complexes and from
K-flat complexes of `O`-modules to `D(Mod(O))` are monoidal and braided.

## Implementation notes

This is the part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.MonoidalLocalizationFunctors` that does not
need `C` to be a `SmallCategory.{u}`, for a site `C : Type c` with `[Category.{u} C]`; the
statements and proofs are the same, in the namespace
`Stacks.SheafOfModules.DerivedMonoidalGeneral`. This applies to the small étale ringed site of an
algebraic space.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
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
that the `u` of `Mod R` does not determine, and the localized structures below cannot be
synthesized through a structure whose universe is still a metavariable. -/
attribute [local instance] monoidalCategoryMod symmetricCategoryMod monoidalPreadditiveMod
  monoidalClosedMod hasTensorMod monoidalComplexes

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal
  CochainComplex.KFlatMonoidal.homotopyBraided
  kFlatQ_isLocalization derivedMonoidal derivedSymmetric

/-! ### The homotopy quotient -/

/-- The quotient functor `Comp(Mod(O)) ⥤ K(Mod(O))`. -/
abbrev homQ := HomotopyCategory.quotient (Mod R) (ComplexShape.up ℤ)

/-- The homotopy quotient, seen as the localization functor onto the monoidal localization of
`Comp(Mod(O))` at the homotopy equivalences. -/
abbrev homQLocalized := Localization.Monoidal.toMonoidalCategory
  (HomotopyCategory.quotient (Mod R) (ComplexShape.up ℤ))
  (HomologicalComplex.homotopyEquivalences (Mod R) (ComplexShape.up ℤ))
  (Iso.refl (CochainComplex.KFlatMonoidal.homotopyUnit (Mod R)))

/-- `homQLocalized` is a monoidal functor, by the universal property of the monoidal
localization. -/
@[instance_reducible]
def homQLocalizedMonoidal : (homQLocalized R).Monoidal := inferInstance

/-- `Comp(Mod(O)) ⥤ K(Mod(O))` is a monoidal functor: `K(Mod(O))` is the monoidal localization
of `Comp(Mod(O))` at the homotopy equivalences. -/
@[instance_reducible]
def homQMonoidal : (homQ R).Monoidal := homQLocalizedMonoidal R

/-- `Comp(Mod(O)) ⥤ K(Mod(O))` is a braided functor, so the braiding of `K(Mod(O))` is induced
by the Koszul symmetry of complexes. -/
@[instance_reducible]
def homQBraided : (homQ R).Braided where
  toMonoidal := homQMonoidal R
  braided X Y := Functor.LaxBraided.braided (F := homQLocalized R) X Y

/-! ### The K-flat localization -/

/-- The K-flat objects of `K(Mod(O))`, localized at the quasi-isomorphisms, seen as the
localization functor onto the monoidal localization. -/
abbrev kFlatQLocalized := Localization.Monoidal.toMonoidalCategory
  (kFlatQ (curriedTensor (Mod R))) (kFlatQuasiIso (curriedTensor (Mod R)))
  (Iso.refl ((kFlatQ (curriedTensor (Mod R))).obj (𝟙_ _)))

/-- `kFlatQLocalized` is a monoidal functor, by the universal property of the monoidal
localization. -/
@[instance_reducible]
def kFlatQLocalizedMonoidal
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    (kFlatQLocalized R).Monoidal := inferInstance

/-- The functor from the K-flat objects of `K(Mod(O))` to `D(Mod(O))` is monoidal:
`D(Mod(O))` is the monoidal localization of those objects at the quasi-isomorphisms. -/
@[instance_reducible]
def kFlatQMonoidal
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    (kFlatQ (curriedTensor (Mod R))).Monoidal := kFlatQLocalizedMonoidal R

/-- The functor from the K-flat objects of `K(Mod(O))` to `D(Mod(O))` is braided, so the
braiding of `D(Mod(O))` is induced by that of `K(Mod(O))`. -/
@[instance_reducible]
def kFlatQBraided : (kFlatQ (curriedTensor (Mod R))).Braided where
  toMonoidal := kFlatQMonoidal R
  braided X Y := Functor.LaxBraided.braided (F := kFlatQLocalized R) X Y

end Stacks.SheafOfModules.DerivedMonoidalGeneral

end
