module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.KFlatQuotientTensoratorGeneral

/-!
# K-flat complexes in the derived category, at general universes

Let `(C, O)` be a ringed site whose objects live in a universe `c` and whose morphisms and sections
live in the universe `u` of the sheaf of rings. The monoidal and lax braided structures of the
functors from K-flat complexes of `O`-modules to `D(Mod(O))`.

## Implementation notes

This is the part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.KFlatComplexesInTheDerivedCategory` that does
not need `C` to be a `SmallCategory.{u}`, for a site `C : Type c` with `[Category.{u} C]`; the
statements and proofs are the same, in the namespace
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
that the `u` of `Mod R` does not determine, and the monoidal data below cannot be synthesized
through a structure whose universe is still a metavariable. -/
attribute [local instance] monoidalCategoryMod symmetricCategoryMod monoidalPreadditiveMod
  monoidalClosedMod hasTensorMod monoidalComplexes

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal
  CochainComplex.KFlatMonoidal.homotopyBraided
  kFlatQ_isLocalization derivedMonoidal derivedSymmetric

attribute [local instance] homQMonoidal homQBraided kFlatQMonoidal kFlatQBraided

/-! ### The homotopy quotient of the K-flat complexes -/

/-- `kFlatQuotient` is a monoidal functor. -/
@[instance_reducible]
def kFlatQuotientMonoidal : (kFlatQuotient R).Monoidal := (kFlatQuotientCore R).toMonoidal

attribute [local instance] kFlatQuotientMonoidal

/-- `kFlatQuotient` is a lax braided functor: the braiding of a full braided subcategory is the
ambient one, so this is the braided-functor identity of the homotopy quotient. -/
@[instance_reducible]
def kFlatQuotientLaxBraided
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    (kFlatQuotient R).LaxBraided where
  braided X Y :=
    (kFlatObjects (curriedTensor (Mod R))).ι.map_injective
      (Functor.LaxBraided.braided (F := homQ R) X.1 Y.1)

attribute [local instance] kFlatQuotientLaxBraided

/-! ### The K-flat complexes in the derived category -/

/-- `kFlatComplexQ` factors through the K-flat objects of `K(Mod(O))`: this is
`DerivedCategory.quotientCompQhIso` restricted to the K-flat complexes. -/
def kFlatComplexQIso
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    kFlatQuotient R ⋙ kFlatQ (curriedTensor (Mod R)) ≅ kFlatComplexQ R :=
  Functor.isoWhiskerLeft (KFlatComplexes R).ι (DerivedCategory.quotientCompQhIso (Mod R))

/-- **The K-flat complexes of `O`-modules form a monoidal functor into `D(Mod(O))`**, being the
composite of two monoidal localization functors, transported along `kFlatComplexQIso`. -/
@[instance_reducible]
def kFlatComplexQMonoidal : (kFlatComplexQ R).Monoidal :=
  Functor.Monoidal.transport (kFlatComplexQIso R)

attribute [local instance] kFlatComplexQMonoidal

/-- **That functor is lax braided**, so it carries the Koszul symmetry of complexes to the
braiding of `D(Mod(O))`. -/
@[instance_reducible]
def kFlatComplexQLaxBraided : (kFlatComplexQ R).LaxBraided :=
  letI : NatTrans.IsMonoidal (kFlatComplexQIso R).hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport (kFlatComplexQIso R)
  Functor.LaxBraided.ofNatIso (kFlatComplexQIso R)

end Stacks.SheafOfModules.DerivedMonoidalGeneral

end
