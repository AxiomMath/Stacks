module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent

/-!
# Situation 084R in the category of algebraic spaces, for a descent situation

The stages of Situation 084R, its limit, its transition morphisms and its projections are
read as objects and morphisms of the category of algebraic spaces over `S` on
`AlgebraicGeometry.Space.LimitSituation`, by
`AlgebraicGeometry.Space.LimitSituation.stage`,
`AlgebraicGeometry.Space.LimitSituation.limitSpace`,
`AlgebraicGeometry.Space.LimitSituation.transition` and
`AlgebraicGeometry.Space.LimitSituation.projection`; that reading is what the statement of
Stacks 07SI, `AlgebraicGeometry.Space.LimitSituation.IsSectionsColimit`, is phrased in.

This file identifies those objects and morphisms, for the limit situation that
`AlgebraicGeometry.Space.DescentSituation.toLimitSituation` builds from a descent situation,
with the data the descent situation itself carries: the stages are the values of its inverse
system, the limit is the vertex of its chosen limiting cone, the transition morphisms are the
maps of its inverse system and the projections are the projections of that cone.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.toLimitSituation_stage_obj` and
  `AlgebraicGeometry.Space.DescentSituation.toLimitSituation_limitSpace_obj`: the underlying
  presheaves of the stages and of the limit.
* `AlgebraicGeometry.Space.DescentSituation.toLimitSituation_transition_hom` and
  `AlgebraicGeometry.Space.DescentSituation.toLimitSituation_projection_hom`: the underlying
  morphisms of presheaves of the transition morphisms and of the projections.

## Implementation notes

An object of `AlgebraicGeometry.Space.AlgebraicSpaces` is a presheaf together with a proof
that it is an algebraic space, and a morphism of that category is a morphism of presheaves,
so each identification below is an equation between presheaves or between morphisms of
presheaves and holds by `rfl`: the limit situation built from a descent situation has the
descent situation's inverse system as its `system` and its chosen cone as its `cone`.

The algebraicity of the limit is an argument of
`AlgebraicGeometry.Space.LimitSituation.limitSpace` and of
`AlgebraicGeometry.Space.LimitSituation.projection`, so the statements below quantify over
it; for a descent situation the canonical choice is its own
`AlgebraicGeometry.Space.DescentSituation.limitAlgebraicSpace`, and with that choice the
assertion of Stacks 07SI for a descent situation `D` and a module `ℱ₀` on its chosen stage is
`D.toLimitSituation.IsSectionsColimit ℱ₀ D.limitAlgebraicSpace`.

## References

* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **The stages of the limit situation of a descent situation are the values of its inverse
system**, read as algebraic spaces over the base. -/
theorem toLimitSituation_stage_obj (i : I) :
    (D.toLimitSituation.stage i).obj = D.system.obj (op i) := rfl

/-- **The limit of the limit situation of a descent situation is the vertex of its chosen
limiting cone**, read as an algebraic space over the base. -/
theorem toLimitSituation_limitSpace_obj (hX : IsAlgebraicSpace B S hS D.limitCone.pt) :
    (D.toLimitSituation.limitSpace hX).obj = D.limitCone.pt := rfl

/-- **The transition morphisms of the limit situation of a descent situation are the maps of
its inverse system**, read as morphisms of algebraic spaces over the base. -/
theorem toLimitSituation_transition_hom {i j : I} (h : i ≤ j) :
    (D.toLimitSituation.transition h).hom = D.system.map (homOfLE h).op := rfl

/-- **The projections of the limit situation of a descent situation are the projections of its
chosen limiting cone**, read as morphisms of algebraic spaces over the base. -/
theorem toLimitSituation_projection_hom (hX : IsAlgebraicSpace B S hS D.limitCone.pt) (i : I) :
    (D.toLimitSituation.projection hX i).hom = D.limitCone.π.app (op i) := rfl

end DescentSituation

end AlgebraicGeometry.Space

end
