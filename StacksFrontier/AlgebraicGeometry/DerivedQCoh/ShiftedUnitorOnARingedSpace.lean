module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ShiftedStructureSheafTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ShiftedUnitorNaturality

/-!
# Tensoring with the structure sheaf in a shifted degree is a translation, naturally

`Stacks.RingedSpace.derivedTensorRightUnitorNatIso` is the right unit constraint
`- ⊗^𝐋_{𝒪_Z} 𝒪_Z[0] ≅ 𝟭 D(𝒪_Z)` of [Stacks, Tag 0FPT] for a ringed space, **as a natural
isomorphism**.  `Stacks.RingedSpace.shiftedUnitTensorLeftIso` is the shifted analogue in the
*left* variable, `𝒪_Z[-a] ⊗^𝐋_{𝒪_Z} N ≅ N⟦-a⟧`, but only one object `N` at a time: it is built
from `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift_left`, a structure field
produced by `Exists.choose` from a bare existence statement recording only exactness, so no
naturality in `N` can be extracted from it.

**This file supplies the right-variable analogue as a natural isomorphism**:

`- ⊗^𝐋_{𝒪_Z} 𝒪_Z[-a] ≅ (-)⟦-a⟧`.

It is obtained not from `commShift_right` — which is the same kind of `Exists.choose` — but from
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.shiftedUnitorNatIso`, which is built at the
level of complexes, where the translate of the unit complex is K-flat and the total tensor
complex commutes with the translation by [Stacks, Tag 0FNG].

## Main definitions

* `Stacks.RingedSpace.derivedShiftedUnitObjectIso`: the identification
  `Q(𝒪_Z[0]⟦-a⟧) ≅ 𝒪_Z[-a]` of the two spellings of the structure sheaf in degree `a`, one as
  the image of a translate of the unit complex and the other as a single-object functor.
* `Stacks.RingedSpace.derivedTensorShiftedUnitorNatIso`: the natural isomorphism above.

## Main results

* `Stacks.RingedSpace.derivedTensorShiftedUnitor_naturality`: its naturality square, with the
  tensor product of a morphism with an identity written through
  `CategoryTheory.Functor.uncurry`, which is the shape
  `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_shiftedUnit` consumes.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.DerivedTensor.RingedSite

open scoped CategoryTheory.Prod

universe u

namespace Stacks.RingedSpace

attribute [local instance] HasDerivedCategory.standard

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The two spellings of the structure sheaf in degree `a` agree**:
`Q(𝒪_Z[0]⟦-a⟧) ≅ 𝒪_Z[-a]`.  The left-hand side is the image of the translate of the unit
complex, which is where the derived tensor product with it is computable; the right-hand side is
`Stacks.RingedSpace.shiftedUnitObject`, the single-object functor in degree `a`.  The
identification is `DerivedCategory.Q`'s commutation with the translation followed by
`Stacks.RingedSpace.shiftedUnitShiftIso`. -/
def derivedShiftedUnitObjectIso (a : ℤ) :
    DerivedTensorProduct.shiftedUnitObject (toRingedSite Z) (-a) ≅ shiftedUnitObject Z a :=
  (DerivedCategory.Q.commShiftIso (-a)).app (unitComplex (toRingedSite Z)) ≪≫
    shiftedUnitShiftIso Z a

/-- **Tensoring with the structure sheaf in degree `a` is the translation by `-a`, naturally**:
`- ⊗^𝐋_{𝒪_Z} 𝒪_Z[-a] ≅ (-)⟦-a⟧`.

This is `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.shiftedUnitorNatIso` for the
canonical derived tensor product, read at the ringed site of the space and transported to the
single-object spelling of the structure sheaf in degree `a` by
`derivedShiftedUnitObjectIso`.

Unlike `Stacks.RingedSpace.shiftedUnitTensorLeftIso` this carries its naturality, which is
`derivedTensorShiftedUnitor_naturality`. -/
def derivedTensorShiftedUnitorNatIso (a : ℤ) :
    (derivedTensorProductFunctor Z.sheaf).flip.obj (shiftedUnitObject Z a) ≅
      CategoryTheory.shiftFunctor
        (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))) (-a) :=
  DerivedTensorProduct.shiftedUnitorNatIsoOfIso (toRingedSite Z)
    (canonicalDerivedTensorProduct Z.sheaf) (-a) (derivedShiftedUnitObjectIso Z a)

/-- **Naturality of `derivedTensorShiftedUnitorNatIso`**, with the tensor product of a morphism
with an identity written through `CategoryTheory.Functor.uncurry` of the derived tensor
bifunctor. -/
theorem derivedTensorShiftedUnitor_naturality (a : ℤ)
    {W W' : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))} (u : W ⟶ W') :
    (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)).map
          ((u ×ₘ 𝟙 (shiftedUnitObject Z a)) :
            ((W, shiftedUnitObject Z a) : _ × _) ⟶ (W', shiftedUnitObject Z a)) ≫
        ((derivedTensorShiftedUnitorNatIso Z a).app W').hom =
      ((derivedTensorShiftedUnitorNatIso Z a).app W).hom ≫
        (CategoryTheory.shiftFunctor
          (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))) (-a)).map u :=
  DerivedTensorProduct.shiftedUnitorNatIsoOfIso_naturality_uncurry (toRingedSite Z)
    (canonicalDerivedTensorProduct Z.sheaf) (-a) (derivedShiftedUnitObjectIso Z a) u

end Stacks.RingedSpace

end
