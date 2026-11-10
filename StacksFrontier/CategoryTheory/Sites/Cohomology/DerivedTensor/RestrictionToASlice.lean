module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.Restriction
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product commutes with restriction to a slice

Let `(C, O)` be a ringed site and let `U` be an object of `C`. For objects `K` and `L` of `D(O)`
this file identifies

`(K ⊗^L_O L)|_U ≅ K|_U ⊗^L_{O|_U} L|_U`

in `D(O|_U)`, where `-|_U` is the derived functor of restriction to the slice site. This is the
derived tensor product analogue of Stacks 08JB, which is the same statement for the derived
internal Hom (`AlgebraicGeometry.RingedSite.derivedHomRestriction`).

The route is the one the library already uses for the extension by zero (Stacks 0GL1, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensor`): replace both
factors by K-flat complexes, where both derived tensor products are ordinary total tensor
complexes, and use that restriction commutes with the total tensor complex on the nose. The two
inputs that make this work are already in the library and are the reason no resolution has to be
chosen twice:

* restriction to a slice carries a K-flat complex to a K-flat complex, which is Stacks 0E8K,
  `Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex`, so the K-flat models of the
  two factors on `C` serve as K-flat models of the two factors on `C/U` as well;
* restriction commutes with the total tensor complex,
  `AlgebraicGeometry.RingedSite.tensorComplexOverIso`.

## Main definitions

* `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIsoOfKFlat`: the comparison at two
  K-flat complexes.
* `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIsoOfKFlatModels`: the comparison
  at two objects of `D(O)` presented by K-flat complexes.
* `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIso`: the comparison at two
  arbitrary objects of `D(O)`, taken at the K-flat models of
  `Stacks.DerivedTensor.RingedSite.kFlatModel`.

## What this file does not contain

**No naturality.** Nothing *below* states that the comparison is natural in either variable, and
the statements here are therefore not enough on their own to transport a *morphism* of `D(O)`
built from the derived tensor product to a slice. This is the same shape as Stacks 0GL1 in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensor`, which also
supplies only the isomorphism.

The naturality is pursued in the companion module
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceNaturality`.
Naturality of `AlgebraicGeometry.RingedSite.tensorComplexOverIso` in a chain map of either
variable, beyond the degreewise statements
`AlgebraicGeometry.RingedSite.sheafTensorOverIso_naturality_left` and
`AlgebraicGeometry.RingedSite.sheafTensorOverIso_naturality_right`, is available, in
both vocabularies, as
`AlgebraicGeometry.RingedSite.tensorComplexOverIso_hom_naturality` and
`AlgebraicGeometry.RingedSite.tensorComplexOverIso_hom_naturality_mapBifunctorMap`. All five of
the squares the naturality of the comparison splits into are now available, and so is the
naturality itself: `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceJunction` is the
comparison below as an isomorphism of functors `D(O) × D(O) ⥤ D(O|_U)`.

In consequence this file does **not** by itself discharge the input that
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionRestriction`,
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals` record as missing for the third
assertion of Stacks 08JJ. That input is the restriction compatibility of the canonical map
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` of Stacks 08JD, which needs the
comparison below *and* its compatibility with the composition morphism of Stacks 0A98 — the
chain-level half of which is
`AlgebraicGeometry.RingedSite.compositionMap_restrict_square`. What is new here is the object
part of that input: the isomorphism `(K ⊗^L_O L)|_U ≅ K|_U ⊗^L_{O|_U} L|_U`, which those three
files record as absent from the library in any public form (it occurred only as a `private def`
inside the proof of Stacks 09JB in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedTensorProduct`, pinned to the
universes `RingedSite.{0, 0, 0}` and specialised to a chosen pair of slice models).

No `@[stacks]` attribute is attached. Stacks 08JB is the statement for the derived internal Hom,
not for the derived tensor product, and no assertion of Stacks 08JJ follows from what is below.

## Implementation notes

The two derived tensor products are carried as arbitrary data of Stacks 06YU, one on `C` and one
on `C/U`, since only their comparison fields are used; `derivedTensorRestrictIso` is therefore
available at the canonical datum of each site in particular.

The universes are the diagonal `RingedSite.{u, u, u}`, which is what the derived tensor product
on a ringed site is stated at, with the derived category's hom universe free as
`HasDerivedCategory.{d}`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0GL1](https://stacks.math.columbia.edu/tag/0GL1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction restrictionComplex
  kFlat_restrictionComplex)

namespace Stacks.DerivedTensor.SliceRestriction

universe d u

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Modules X.O)]
  [HasDerivedCategory.{d} (Modules (X.O.over U))]

/-- **The derived tensor product commutes with restriction to a slice, at two K-flat
complexes.** For K-flat complexes `A` and `B` of `O`-modules, the restriction of
`A ⊗^L_O B` to the site over `U` is `A|_U ⊗^L_{O|_U} B|_U`.

K-flat complexes compute the derived tensor product on `C`, so the left-hand side is the
restriction of the class of `Tot(A ⊗_O B)`; that is the class of `Tot(A ⊗_O B)|_U` because
restriction is exact, and `Tot(A ⊗_O B)|_U = Tot(A|_U ⊗_{O|_U} B|_U)` by
`AlgebraicGeometry.RingedSite.tensorComplexOverIso`. The restrictions `A|_U` and `B|_U` are
K-flat by Stacks 0E8K, so that total complex computes the derived tensor product on `C/U`. -/
def derivedTensorRestrictIsoOfKFlat
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
    (TU : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (X.O.over U))
    (A B : CochainComplex (Modules X.O) ℤ)
    (hA : Stacks.SheafOfModules.KFlat X.O A)
    (hB : Stacks.SheafOfModules.KFlat X.O B) :
    (restriction X U).mapDerivedCategory.obj
        ((T.tensor.obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B)) ≅
      (TU.tensor.obj (DerivedCategory.Q.obj ((restrictionComplex X U).obj A))).obj
        (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) :=
  (restriction X U).mapDerivedCategory.mapIso (T.comparison A B hA hB) ≪≫
    (restriction X U).mapDerivedCategoryFactors.app (((tensorComplex X.O).obj A).obj B) ≪≫
    DerivedCategory.Q.mapIso (RingedSite.tensorComplexOverIso X U A B) ≪≫
    (TU.comparison ((restrictionComplex X U).obj A) ((restrictionComplex X U).obj B)
      (kFlat_restrictionComplex X U A hA) (kFlat_restrictionComplex X U B hB)).symm

/-- **The derived tensor product commutes with restriction to a slice, at two objects presented
by K-flat complexes.** `derivedTensorRestrictIsoOfKFlat` transported along the two presenting
isomorphisms, on the left through the derived tensor product on `C` and on the right through the
one on `C/U` and the derived restriction functor. -/
def derivedTensorRestrictIsoOfKFlatModels
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
    (TU : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (X.O.over U))
    (A B : CochainComplex (Modules X.O) ℤ)
    (hA : Stacks.SheafOfModules.KFlat X.O A)
    (hB : Stacks.SheafOfModules.KFlat X.O B)
    {K : DerivedCategory (Modules X.O)} (eK : DerivedCategory.Q.obj A ≅ K)
    {L : DerivedCategory (Modules X.O)} (eL : DerivedCategory.Q.obj B ≅ L) :
    (restriction X U).mapDerivedCategory.obj ((T.tensor.obj K).obj L) ≅
      (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj K)).obj
        ((restriction X U).mapDerivedCategory.obj L) :=
  (restriction X U).mapDerivedCategory.mapIso
      (((T.tensor.mapIso eK).app L).symm ≪≫
        ((T.tensor.obj (DerivedCategory.Q.obj A)).mapIso eL).symm) ≪≫
    derivedTensorRestrictIsoOfKFlat X U T TU A B hA hB ≪≫
    (TU.tensor.mapIso ((restriction X U).mapDerivedCategoryFactors.app A).symm).app
      (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) ≪≫
    (TU.tensor.mapIso ((restriction X U).mapDerivedCategory.mapIso eK)).app
      (DerivedCategory.Q.obj ((restrictionComplex X U).obj B)) ≪≫
    (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj K)).mapIso
      (((restriction X U).mapDerivedCategoryFactors.app B).symm ≪≫
        (restriction X U).mapDerivedCategory.mapIso eL)

/-- **The derived tensor product commutes with restriction to a slice.** Let `(C, O)` be a
ringed site and let `U` be an object of `C`. For objects `K` and `L` of `D(O)`,

`(K ⊗^L_O L)|_U ≅ K|_U ⊗^L_{O|_U} L|_U`.

This is the derived tensor product analogue of Stacks 08JB. It is
`derivedTensorRestrictIsoOfKFlatModels` at the K-flat models of
`Stacks.DerivedTensor.RingedSite.kFlatModel`, whose restrictions are K-flat by Stacks 0E8K. -/
def derivedTensorRestrictIso
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
    (TU : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (X.O.over U))
    (K L : DerivedCategory (Modules X.O)) :
    (restriction X U).mapDerivedCategory.obj ((T.tensor.obj K).obj L) ≅
      (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj K)).obj
        ((restriction X U).mapDerivedCategory.obj L) :=
  derivedTensorRestrictIsoOfKFlatModels X U T TU
    (Stacks.DerivedTensor.RingedSite.kFlatModel X.O K)
    (Stacks.DerivedTensor.RingedSite.kFlatModel X.O L)
    (Stacks.DerivedTensor.RingedSite.kFlatModel_kFlat X.O K)
    (Stacks.DerivedTensor.RingedSite.kFlatModel_kFlat X.O L)
    (Stacks.DerivedTensor.RingedSite.kFlatModelIso X.O K)
    (Stacks.DerivedTensor.RingedSite.kFlatModelIso X.O L)

end Stacks.DerivedTensor.SliceRestriction

end
