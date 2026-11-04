module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheaves

/-!
# The chart morphisms of an algebraic space are relatively representable

The two families of morphisms of algebraic spaces that the chartwise descriptions of
Stacks 03LS, 03LY and 03LZ use are relatively representable in the sense of
`CategoryTheory.Functor.relativelyRepresentable`:

* the structure morphism `AlgebraicGeometry.Space.chartToSpace` of an étale scheme chart, by the
  diagonal criterion — the diagonal of an algebraic space is representable, which is
  `AlgebraicGeometry.Space.relativelyRepresentable_of_isAlgebraicSpace`;
* the morphism `AlgebraicGeometry.Space.chartMap` of represented algebraic spaces attached to a
  morphism of charts, because it is the Yoneda image of a morphism of the big fppf site and that
  site has fibre products.

Both facts are used wherever a statement about the chart families needs the base change of
charts of Stacks 03LP, which exists only along a relatively representable morphism.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The structure morphism of an étale scheme chart is relatively representable.**  It is a
morphism from a represented presheaf to an algebraic space, and the diagonal of an algebraic
space is representable. -/
theorem relativelyRepresentable_chartToSpace (U : SmallEtale B S hS X.1) :
    yoneda.relativelyRepresentable (chartToSpace B S hS X U).hom :=
  relativelyRepresentable_of_isAlgebraicSpace B S hS X.2 (chartToSpace B S hS X U).hom

/-- **The morphism of represented algebraic spaces attached to a morphism of étale scheme charts
is relatively representable.**  It is the Yoneda image of a morphism of the big fppf site, and
that site has fibre products. -/
theorem relativelyRepresentable_chartMap {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    yoneda.relativelyRepresentable (chartMap B S hS X f).hom :=
  Functor.relativelyRepresentable.map yoneda
    ((SmallEtale.inclusion B S hS X.1).map f).left

end AlgebraicGeometry.Space

end
