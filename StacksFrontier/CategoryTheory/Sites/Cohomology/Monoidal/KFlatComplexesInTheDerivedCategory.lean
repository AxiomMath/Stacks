module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.KFlatQuotientTensorator

/-!
# The K-flat complexes of modules on a ringed site as a monoidal functor to `D(Mod(O))`

The homotopy quotient of the K-flat complexes of `O`-modules is a lax braided monoidal functor
onto the K-flat objects of `K(Mod(O))`, and composing it with the K-flat localization gives a
braided monoidal functor into `D(Mod(O))`.  This file assembles that composite and transports
it to `DerivedCategory.Q` restricted to the K-flat complexes.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.kFlatQuotientMonoidal`,
  `Stacks.SheafOfModules.DerivedMonoidal.kFlatQuotientLaxBraided`: the homotopy quotient of the
  K-flat complexes is a lax braided monoidal functor.
* `Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQMonoidal`,
  `Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQLaxBraided`: the K-flat complexes of
  `O`-modules form a braided monoidal functor into `D(Mod(O))`.

## Implementation notes

The composite is formed through the full subcategory of K-flat objects of `K(Mod(O))` and then
transported along `DerivedCategory.quotientCompQhIso` by
`CategoryTheory.Functor.Monoidal.transport`, which is what places the structure at
`DerivedCategory.Q` rather than at `HomotopyCategory.quotient ⋙ DerivedCategory.Qh`.
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
def kFlatQuotientLaxBraided : (kFlatQuotient R).LaxBraided where
  braided X Y :=
    (kFlatObjects (curriedTensor (Mod R))).ι.map_injective
      (Functor.LaxBraided.braided (F := homQ R) X.1 Y.1)

attribute [local instance] kFlatQuotientLaxBraided

/-! ### The K-flat complexes in the derived category -/

/-- `kFlatComplexQ` factors through the K-flat objects of `K(Mod(O))`: this is
`DerivedCategory.quotientCompQhIso` restricted to the K-flat complexes. -/
def kFlatComplexQIso :
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

end Stacks.SheafOfModules.DerivedMonoidal

end
