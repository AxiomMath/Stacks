module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono

/-!
# A closed immersion of algebraic spaces is injective on points

A closed immersion of algebraic spaces over a scheme `S` induces an *injective* map on the
sets of points of Stacks 03BU.  The content is already in the library in two halves and this
file is only their composition: a closed immersion is a monomorphism of presheaves
(`AlgebraicGeometry.Space.mono_of_isClosedImmersion`), and a monomorphism of presheaves on the
big fppf site is injective on points (`AlgebraicGeometry.Space.pointsMap_injective_of_mono`,
which is Stacks 06RV).

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.pointsMap_injective_of_isClosedImmersion`: the map on points
  induced by a closed immersion of presheaves on the big fppf site of `S` is injective.
* `AlgebraicGeometry.Space.pointsMap_hom_injective_of_isClosedImmersion`: the same for a
  morphism of the category `AlgebraicGeometry.AlgebraicSpaces`, which is the shape consumers
  phrased in that category ask for.

## Implementation notes

The statement needs *no* algebraicity hypothesis on either presheaf, since neither of the two
inputs needs one: `AlgebraicGeometry.Space.mono_of_isClosedImmersion` transports the
monomorphism property of a closed immersion of schemes through the represented base changes,
and `AlgebraicGeometry.Space.pointsMap_injective_of_mono` uses only that the morphism is a
monomorphism.  Both results are therefore unconditional, and so is the composition.

No tag attribute is carried.  Injectivity on points of a monomorphism is Stacks 06RV and the
attribute sits on `AlgebraicGeometry.Space.pointsMap_injective_of_mono`; what is below is that
tag specialized along a named implication, not the content of a tag of its own.  In
particular this is weaker than universal injectivity
(`AlgebraicGeometry.Space.UniversallyInjective`), which 06RV does not give and which is not
claimed here.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed immersion is injective on points.**  The map on the points of Stacks 03BU
induced by a closed immersion of presheaves on the big fppf site of `S` is injective: a closed
immersion is a monomorphism of presheaves, and a monomorphism induces an injective map on
points by Stacks 06RV. -/
theorem pointsMap_injective_of_isClosedImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : IsClosedImmersion B S hS f) :
    Function.Injective (pointsMap B S hS F f) :=
  have : Mono f := mono_of_isClosedImmersion B S hS f hf
  pointsMap_injective_of_mono B S hS f

/-- **A closed immersion of algebraic spaces is injective on points**, for a morphism of the
category `AlgebraicGeometry.AlgebraicSpaces` of Stacks 02X2.  This is
`AlgebraicGeometry.Space.pointsMap_injective_of_isClosedImmersion` read on the underlying
natural transformation. -/
theorem pointsMap_hom_injective_of_isClosedImmersion {X Y : AlgebraicSpaces B S hS}
    (i : Y ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    Function.Injective (pointsMap B S hS Y.1 i.hom) :=
  pointsMap_injective_of_isClosedImmersion B S hS i.hom hi

end AlgebraicGeometry.Space

end
