module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SatisfiesRSStarEquivalenceOver
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingEquivalence
public import StacksFrontier.Deformation.Artin.Versality.OpennessObstruction
public import StacksFrontier.Deformation.Artin.Versality.OpennessTransfer

/-!
# Openness of versality for the stack of curves, from Artin's criterion 0CXU (towards Stacks 0D59)

Stacks 0D59 — the stack `Curves` satisfies openness of versality over `Spec(ℤ)` — is deduced in
the source from Stacks 0D3X, which is Artin's criterion Stacks 0CXU applied to
`Spaces'_{fp, flat, proper}`. The same criterion applies to `Curves` itself, whose inputs are
those of 0D3X restricted to families of relative dimension at most one: the diagonal
(Stacks 0D53), condition (RS*) (Stacks 0D56), limit preservation (Stacks 0D55), and the
effectivity of towers of square-zero thickenings that the proof of Stacks 0D3X establishes.

The library's forms of Stacks 0CXU,
`Deformation.Artin.isOpenVersality_of_isSquareZeroTowerEffectiveOnClasses` and its variant for
special towers `AlgebraicGeometry.C1590Private.specialTowerOpenVersality`, ask for a category
with morphisms in the universe of the schemes, so they are applied to the hom-shrunk model
`AlgebraicGeometry.curvesSmall` of the stack of curves. The diagonal, (RS*) and limit preservation
are moved to it along `AlgebraicGeometry.curvesSmallEquivalenceOver`, and openness of versality is
moved back (`Deformation.Artin.hasOpenVersality_of_equivalenceOver`). This file moves the
diagonal; the assembly is
`AlgebraicGeometry.C1590Private.hasOpenVersality_curvesFiberedCategory_of_inputs`, in
`StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs`, after the special-tower
form of Stacks 0CXU.

## Main results

* `AlgebraicGeometry.C1590Private.hasRepresentableDiagonal_curvesSmall`: the diagonal of the small
  model is representable when that of `Curves` is.

## Implementation notes

Nothing here carries a `stacks` attribute: the declaration takes a result the source proves
(the diagonal, Stacks 0D53) as an argument.

## References

* [Stacks Project, Tag 0D59](https://stacks.math.columbia.edu/tag/0D59)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.C1590Private

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The diagonal of the small model of `Curves` is representable when that of `Curves` is.**
Condition (1) of Stacks 045G is read through condition (3), which transports along the
equivalence over the site between the two models
(`AlgebraicGeometry.Stack.isRepresentableFromSchemes_of_equivalenceOver`). -/
theorem hasRepresentableDiagonal_curvesSmall
    (hdiag : Stack.HasRepresentableDiagonal B integerBase hZ (curvesFiberedCategory B hZ)) :
    Stack.HasRepresentableDiagonal B integerBase hZ (curvesSmall B hZ) :=
  (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B integerBase hZ _).2
    ((Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B integerBase hZ _).2
      (Stack.isRepresentableFromSchemes_of_equivalenceOver B integerBase hZ
        (𝒳 := curvesFiberedCategory B hZ) (𝒴 := curvesSmall B hZ)
        (curvesSmallEquivalenceOver B hZ).toBasedEquivalence
        ((Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B integerBase hZ _).1
          ((Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B integerBase hZ
            _).1 hdiag))))

end AlgebraicGeometry.C1590Private

end
