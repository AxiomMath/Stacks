module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.KFlatComplexesMonoidalSubcategory

/-!
# The tensorator of the homotopy quotient of the K-flat complexes

The homotopy quotient from the K-flat complexes of `O`-modules to the K-flat objects of
`K(Mod(O))` is a monoidal functor, with the tensorator of the homotopy quotient of
`Comp(Mod(O))`.  This file supplies that monoidal datum.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.kFlatQuotientCore`: the tensorator of
  `Stacks.SheafOfModules.DerivedMonoidal.kFlatQuotient`, together with its four coherences.

## Implementation notes

This is the only new monoidal datum in the construction of the symmetric monoidal derived
category: each field is the corresponding field of the homotopy quotient of `Comp(Mod(O))`,
read through the faithful inclusion of the subcategory of K-flat objects.  Each coherence
field is an equation between morphisms of `K(Mod(O))` whose type mentions the localized
monoidal structure, which is what makes the declaration expensive to check; it is kept in a
module of its own for that reason.
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

end Stacks.SheafOfModules.DerivedMonoidal

end
