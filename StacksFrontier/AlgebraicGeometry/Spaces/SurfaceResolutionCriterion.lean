module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationGenericStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularLocalRings
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs

/-!
# The normalization criterion for resolving a two-dimensional algebraic space

Condition (4) of Stacks 0BHY asks of a two-dimensional integral Noetherian algebraic space `Y`
over a scheme `S` that the normalization `Y^ν ⟶ Y` be finite, that `Y^ν` have finitely many
singular points `y₁, …, yₘ`, and that for each `i` the completion of the henselian local ring
`𝒪^h_{Y^ν, yᵢ}` be normal. This file defines that condition.

## Main definitions

* `AlgebraicGeometry.Space.NormalizationData.IsSurfaceResolutionCriterion` is condition (4) of
  Stacks 0BHY for a normalization `D` of `Y`.

## Implementation notes

The normalization is an arbitrary `AlgebraicGeometry.Space.NormalizationData`; normalizations
exist (Stacks 07U4) and are unique up to unique isomorphism over `Y`. Finiteness of the
normalization morphism is `AlgebraicGeometry.Space.IsFinite`.

A singular point of `Y^ν` is a point of `|Y^ν|` at which `Y^ν` is not regular in the sense of
Stacks 0AH9, `AlgebraicGeometry.Space.IsRegularAt`. (The source writes `y₁, …, yₘ ∈ |Y|`, but the
points in question are singular points of `Y^ν`, so they lie in `|Y^ν|`.)

The henselian local ring of Stacks 0BGW is defined for a decent algebraic space; the
normalization of a decent algebraic space is decent
(`AlgebraicGeometry.Space.NormalizationData.isDecentSpace`), so the condition takes decency of
`Y` — a consequence of integrality — and no hypothesis on `Y^ν`. The completion is the adic
completion along the maximal ideal and normality is `IsNormalRing`, exactly as in clause (3) of
Stacks 0BHU.

## References

* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
* [Stacks Project, Tag 0AH9](https://stacks.math.columbia.edu/tag/0AH9)
* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

namespace NormalizationData

/-- **Condition (4) of Stacks 0BHY.** For a normalization `D : Y^ν ⟶ Y` of a decent algebraic
space `Y` over `S`: the normalization morphism is finite, `Y^ν` has finitely many singular
points (points at which it is not regular, Stacks 0AH9), and at each of them the completion of
the henselian local ring of `Y^ν` (Stacks 0BGW) along its maximal ideal is a normal ring. -/
def IsSurfaceResolutionCriterion (D : NormalizationData B S hS Y)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y) : Prop :=
  IsFinite B S hS D.hom ∧
    {y : points B S hS D.space | ¬ IsRegularAt B S hS D.space y}.Finite ∧
      ∀ y : points B S hS D.space, ¬ IsRegularAt B S hS D.space y →
        letI := henselianLocalRing_isLocalRing B S hS D.space D.isAlgebraicSpace y
          (D.isDecentSpace hY hYdec)
        IsNormalRing (AdicCompletion
          (IsLocalRing.maximalIdeal (henselianLocalRing B S hS D.space D.isAlgebraicSpace y
            (D.isDecentSpace hY hYdec) : Type (u + 1)))
          (henselianLocalRing B S hS D.space D.isAlgebraicSpace y
            (D.isDecentSpace hY hYdec) : Type (u + 1)))

end NormalizationData

end AlgebraicGeometry.Space

end
