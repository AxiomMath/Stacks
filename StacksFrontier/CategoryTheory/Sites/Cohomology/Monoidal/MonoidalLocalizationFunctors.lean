module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SubcategoryLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison

/-!
# The two localization functors of the derived category of a ringed site are braided monoidal

The symmetric monoidal structure of `D(Mod(O))` is obtained by localizing twice: the complexes
of `O`-modules at the homotopy equivalences, giving `K(Mod(O))`, and then the K-flat objects of
`K(Mod(O))` at the quasi-isomorphisms, giving `D(Mod(O))`.  Each step is a monoidal
localization, so each localization functor is a braided monoidal functor; this file names those
structures.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.homQMonoidal`,
  `Stacks.SheafOfModules.DerivedMonoidal.homQBraided`: the homotopy quotient
  `Comp(Mod(O)) ⥤ K(Mod(O))` is a braided monoidal functor.
* `Stacks.SheafOfModules.DerivedMonoidal.kFlatQMonoidal`,
  `Stacks.SheafOfModules.DerivedMonoidal.kFlatQBraided`: the localization of the K-flat objects
  of `K(Mod(O))` at the quasi-isomorphisms is a braided monoidal functor.

## Implementation notes

Each structure is `CategoryTheory.Localization.Monoidal.toMonoidalCategory`, read at the
underlying category rather than at the type synonym
`CategoryTheory.Localization.Monoidal.LocalizedMonoidal` that carries the localized monoidal
structure.  That reading is split into two declarations: the structure is first named at the
type synonym, where instance synthesis finds it with no coercion
(`Stacks.SheafOfModules.DerivedMonoidal.homQLocalizedMonoidal`,
`Stacks.SheafOfModules.DerivedMonoidal.kFlatQLocalizedMonoidal`), and only then transported to
the underlying category.  The braided structures are likewise given field by field, with the
monoidal field taken from the already-named monoidal structure.
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
def kFlatQLocalizedMonoidal : (kFlatQLocalized R).Monoidal := inferInstance

/-- The functor from the K-flat objects of `K(Mod(O))` to `D(Mod(O))` is monoidal:
`D(Mod(O))` is the monoidal localization of those objects at the quasi-isomorphisms. -/
@[instance_reducible]
def kFlatQMonoidal : (kFlatQ (curriedTensor (Mod R))).Monoidal := kFlatQLocalizedMonoidal R

/-- The functor from the K-flat objects of `K(Mod(O))` to `D(Mod(O))` is braided, so the
braiding of `D(Mod(O))` is induced by that of `K(Mod(O))`. -/
@[instance_reducible]
def kFlatQBraided : (kFlatQ (curriedTensor (Mod R))).Braided where
  toMonoidal := kFlatQMonoidal R
  braided X Y := Functor.LaxBraided.braided (F := kFlatQLocalized R) X Y

end Stacks.SheafOfModules.DerivedMonoidal

end
