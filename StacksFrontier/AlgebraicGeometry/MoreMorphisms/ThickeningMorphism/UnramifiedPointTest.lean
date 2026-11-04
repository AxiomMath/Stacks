module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.CartesianHom
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Unramifiedness over a cartesian thickening, at the point test of Section 04XB

This file restates **Stacks 0BPJ**, part (5), of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Unramified` with the square given
by morphisms of the category of algebraic spaces over `S` and unramifiedness by a morphism
property of that category.

## Main results

* `AlgebraicGeometry.Space.unramifiedMorphismProperty_iff_of_cartesianSquareOfThickeningHoms`:
  **Stacks 0BPJ**, part (5), at the point test of Section 04XB.

## Implementation notes

The point-test statement is the same equivalence with the two smaller spaces given by objects,
rather than by subfunctors, of the category of algebraic spaces over `S`; the bridge between the
two presentations is
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.CartesianHom`. That is the shape
in which the point test of **Stacks 03YK** reads a property of morphisms of algebraic spaces.

## References

* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0BPJ, part (5), at the point test of Section 04XB.** Let
`(f, f') : (X ⊂ X') → (Y ⊂ Y')` be a morphism of thickenings of algebraic spaces over `S` with
`f` and `f'` locally of finite type and `X = Y ×_{Y'} X'`. Then `f` is unramified if and only if
`f'` is unramified.

The two thickenings are given as morphisms `i : X ⟶ X'` and `j : Y ⟶ Y'` of the category of
algebraic spaces over `S` (`AlgebraicGeometry.Space.IsThickeningHom`) and the three properties
as morphism properties of that category, which is the shape the point test of **Stacks 03YK**
reads a property of morphisms of algebraic spaces in; see
`AlgebraicGeometry.Stack.HasRelativeProperty`. The equivalence itself is
`AlgebraicGeometry.Space.isUnramified_iff_of_cartesianMorphismOfThickenings`, the same statement
with the two smaller spaces presented as subfunctors of the two ambient ones. -/
@[stacks 0BPJ "part (5): unramified, at the Section 04XB point test"]
theorem unramifiedMorphismProperty_iff_of_cartesianSquareOfThickeningHoms
    {X X' Y Y' : AlgebraicSpaces B S hS} {i : X ⟶ X'} {j : Y ⟶ Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j) (hsq : IsPullback f i j f')
    (hft : locallyOfFiniteTypeProperty B S hS f)
    (hft' : locallyOfFiniteTypeProperty B S hS f') :
    unramifiedMorphismProperty B S hS f ↔ unramifiedMorphismProperty B S hS f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianSquareOfThickeningHoms _
    unramified_isEtaleLocalOnSourceAndTarget (fun E => E.unramified_iff) hi hj hsq hft hft'

end AlgebraicGeometry.Space

end
