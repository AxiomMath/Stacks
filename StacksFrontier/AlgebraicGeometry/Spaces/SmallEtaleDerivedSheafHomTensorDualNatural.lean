module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDualHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategoryPerfect

/-!
# Tensoring with a perfect object on an algebraic space is a right adjoint

For a perfect `E` in `D(𝒪_X)`, tensoring with `E` is right adjoint to tensoring with its dual:
`- ⊗^L E^∨ ⊣ E ⊗^L -`. This combines Stacks 08J8 for `E^∨`, the natural form of Stacks 08JJ for
`E^∨` (the base's `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomTensorDualNatIso`) and
`(E^∨)^∨ ≅ E`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedTensorDualAdjunction`: `- ⊗^L E^∨ ⊣ E ⊗^L -` for `E`
  perfect.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Tensoring with a perfect object is right adjoint to tensoring with its dual**:
`- ⊗^L E^∨ ⊣ E ⊗^L -`, from Stacks 08J8 for `E^∨`, Stacks 08JJ for `E^∨` and `(E^∨)^∨ ≅ E`. -/
def smallEtaleDerivedTensorDualAdjunction (E : spaceDerivedCategory B S hS X)
    (hE : spaceIsPerfect B S hS X E) :
    (smallEtaleDerivedTensor B S hS X).flip.obj (smallEtaleDerivedDual B S hS X E) ⊣
      (smallEtaleDerivedTensor B S hS X).obj E :=
  (smallEtaleDerivedTensorSheafHomAdjunction B S hS X
      (smallEtaleDerivedDual B S hS X E)).ofNatIsoRight
    (smallEtaleDerivedSheafHomTensorDualNatIso B S hS X (smallEtaleDerivedDual B S hS X E)
        (isPerfect_smallEtaleDerivedDual B S hS X E hE) ≪≫
      (smallEtaleDerivedTensor B S hS X).mapIso (smallEtaleDerivedBidualIso B S hS X E hE))

end AlgebraicGeometry.Space

end
