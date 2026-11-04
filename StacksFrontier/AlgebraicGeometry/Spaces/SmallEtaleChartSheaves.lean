module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism

/-!
# Restriction of sheaves on an algebraic space to its étale scheme charts

An étale scheme chart `U` of an algebraic space `X` over `S` represents an algebraic space over
`X` (Stacks 03G1), so Stacks 03G2, part (3) attaches to every morphism of charts, and to every
structure morphism of a chart, a morphism of small étale topoi.  Its inverse image is the
restriction of a sheaf on `X_étale` to a chart, which is the datum underlying the chartwise
description of sheaves in Stacks 03LS.

## Main definitions

* `AlgebraicGeometry.Space.chartSpace`, `AlgebraicGeometry.Space.chartToSpace` and
  `AlgebraicGeometry.Space.chartMap` are the algebraic space represented by an étale scheme
  chart, its structure morphism to the base, and the morphism of represented spaces attached to
  a morphism of charts.
* `AlgebraicGeometry.Space.chartInverseImage` is the small étale inverse image along a morphism
  of charts, and `AlgebraicGeometry.Space.chartRestriction` is restriction from the algebraic
  space to a chart.

## Main results

* `AlgebraicGeometry.Space.chartMap_comp` and
  `AlgebraicGeometry.Space.chartMap_comp_chartToSpace`: the represented morphisms compose, and
  commute with the structure morphisms to the base.
* `AlgebraicGeometry.Space.chartInverseImageComp`: **Stacks 03LS**, the canonical comparison
  identifying successive chartwise inverse images with the inverse image along the composite.
* `AlgebraicGeometry.Space.chartRestrictionComp`: **Stacks 03LS**, restriction to a chart
  followed by further chartwise inverse image is restriction to the smaller chart.

## Implementation notes

The three chart constructions are reducible abbreviations for the components of
`AlgebraicGeometry.Space.chartOver` and `AlgebraicGeometry.Space.comparisonFunctor`, which
already carry Stacks 03G1; they exist so that the statements below can be read without
unfolding a slice of a full subcategory.

Both comparisons are the adjoint-mate composition isomorphism
`AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage` of Stacks 03G2, part (3),
transported along an *equality* of morphisms of algebraic spaces — `chartMap_comp` and
`chartMap_comp_chartToSpace` — so the `CategoryTheory.eqToIso` in each proof is unavoidable:
the two composites are equal, not merely isomorphic, and the composition isomorphism is stated
about the composite morphism.

The remaining content of Stacks 03LS, that restriction to the charts is an *equivalence* onto
the category of chartwise glueing data, is not proved here.  Its two ingredients are both in the
library — `CategoryTheory.SiteGlueing.canonicalEquivalence` (Stacks 0GWK) for an arbitrary site
and `AlgebraicGeometry.Space.smallEtalePostcomp` (Stacks 03LP) for the identification of a slice
of the small étale site with the small étale site of the chart — and they have yet to be put
together.

## References

* [Stacks Project, Tag 03LS](https://stacks.math.columbia.edu/tag/03LS)
* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The algebraic space represented by an étale scheme chart of `X`. -/
abbrev chartSpace (U : SmallEtale B S hS X.1) : AlgebraicSpaces B S hS :=
  (chartOver B S hS X U).left

/-- The structure morphism of an étale scheme chart, as a morphism of algebraic spaces. -/
abbrev chartToSpace (U : SmallEtale B S hS X.1) : chartSpace B S hS X U ⟶ X :=
  (chartOver B S hS X U).hom

/-- The morphism of represented algebraic spaces attached to a morphism of étale scheme
charts. -/
abbrev chartMap {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartSpace B S hS X V ⟶ chartSpace B S hS X U :=
  ((comparisonFunctor B S hS X).map f).hom.left

/-- Passing to represented algebraic spaces takes composition of chart morphisms to composition
of morphisms of algebraic spaces, by functoriality of
`AlgebraicGeometry.Space.comparisonFunctor`. -/
theorem chartMap_comp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    chartMap B S hS X g ≫ chartMap B S hS X f = chartMap B S hS X (g ≫ f) :=
  (congrArg (fun m => m.hom.left) ((comparisonFunctor B S hS X).map_comp g f)).symm

/-- A morphism of étale scheme charts commutes with the structure morphisms of the two charts to
the algebraic space: this is the triangle over `X` of the morphism of the spaces-étale site. -/
theorem chartMap_comp_chartToSpace {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartMap B S hS X f ≫ chartToSpace B S hS X U = chartToSpace B S hS X V :=
  Over.w ((comparisonFunctor B S hS X).map f).hom

/-- The small étale inverse image along a morphism of étale scheme charts of `X`, that is, the
inverse image of the morphism of small étale topoi of Stacks 03G2, part (3), for the represented
morphism of algebraic spaces. -/
noncomputable def chartInverseImage {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    Sheaf (SmallEtale.topology B S hS (chartSpace B S hS X U).1) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B S hS (chartSpace B S hS X V).1) (Type (u + 1)) :=
  (smallToposMorphism B S hS (chartMap B S hS X f)).inverseImage

/-- **Stacks 03LS.** The canonical comparison of successive chartwise inverse images with the
inverse image along the composite morphism of charts: it is the adjoint-mate composition
isomorphism of Stacks 03G2, part (3), read through the equality `chartMap g ≫ chartMap f =
chartMap (g ≫ f)`. -/
@[stacks 03LS "canonical comparison of inverse images"]
noncomputable def chartInverseImageComp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U)
    (g : W ⟶ V) :
    chartInverseImage B S hS X f ⋙ chartInverseImage B S hS X g ≅
      chartInverseImage B S hS X (g ≫ f) :=
  (smallToposMorphism_comp_inverseImage B S hS (chartMap B S hS X g)
      (chartMap B S hS X f)).symm ≪≫
    eqToIso (congrArg (fun k => (smallToposMorphism B S hS k).inverseImage)
      (chartMap_comp B S hS X f g))

/-- Restriction of a sheaf on the small étale site of `X` to an étale scheme chart, by inverse
image along the structure morphism of the chart. -/
noncomputable def chartRestriction (U : SmallEtale B S hS X.1) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B S hS (chartSpace B S hS X U).1) (Type (u + 1)) :=
  (smallToposMorphism B S hS (chartToSpace B S hS X U)).inverseImage

/-- **Stacks 03LS.** Restriction to a chart commutes canonically with further restriction along
a morphism of charts: the composite of the structure morphism of the larger chart with the
morphism of charts is the structure morphism of the smaller chart. -/
@[stacks 03LS "compatibility of chart restriction with inverse image"]
noncomputable def chartRestrictionComp {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    chartRestriction B S hS X U ⋙ chartInverseImage B S hS X f ≅
      chartRestriction B S hS X V :=
  (smallToposMorphism_comp_inverseImage B S hS (chartMap B S hS X f)
      (chartToSpace B S hS X U)).symm ≪≫
    eqToIso (congrArg (fun k => (smallToposMorphism B S hS k).inverseImage)
      (chartMap_comp_chartToSpace B S hS X f))

end AlgebraicGeometry.Space

end
