module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasArrowSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationEtaleSource
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition

/-!
# The quotient-stack projection of a groupoid scheme with étale source is étale

Let `G = (U, R, s, t, c)` be a groupoid scheme over a scheme `S` of a big fppf site which
contains its object scheme, its arrow scheme and its scheme of composable pairs, and let
`π : S_U ⟶ [U/R]` be the canonical projection of **Stacks 044R** out of the realization of `G` as
a groupoid in algebraic spaces. If `s` is étale as a morphism of schemes, then `π` is étale in the
relative sense of **Stacks 03YK**.

This is **Stacks 04M9** read at étaleness: the self-square of `π` is the arrow space with legs
`s` and `t`, so a property of morphisms of algebraic spaces which is stable under base change and
local on the target for the fppf topology passes from `s` to `π`
(`AlgebraicGeometry.Stack.QuotientAtlas.relativeProperty_of_prop_source`), and étaleness is such
a property by **Stacks 03FU** and **Stacks 042B**. The source map of the realization is the Yoneda
image of `s`, which is étale as a morphism of algebraic spaces exactly when `s` is
(`AlgebraicGeometry.Space.isEtale_yoneda_map_iff`).

It is the step by which an étale presentation of an algebraic stack makes the chart étale over
it — the end of the proof of **Stacks 06N0**, where `U = Spec k₀` is the spectrum of the field of
invariants and `R` is the arrow scheme of the quotient groupoid of the division.

## Main results

* `Stacks.Groupoids.GroupoidScheme.relativeProperty_quotientStackProjection_realization`: a
  property of morphisms of algebraic spaces stable under base change and local on the target for
  the fppf topology passes from the source map of a groupoid scheme to the projection of its
  quotient stack.
* `Stacks.Groupoids.GroupoidScheme.isRelativelyEtale_quotientStackProjection_realization`:
  **the projection is étale when the source map is.**

## References

* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 042B](https://stacks.math.columbia.edu/tag/042B)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Stack

namespace Stacks.Groupoids.GroupoidScheme

universe u

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (Limits.pullback G.source G.target).left)

/-- **A property of morphisms of algebraic spaces which is stable under base change and local on
the target for the fppf topology passes from the source map of a groupoid scheme to the
projection of its quotient stack.**

This is `AlgebraicGeometry.Stack.QuotientAtlas.relativeProperty_of_prop_source` at the
realization of the groupoid scheme, whose source map is the Yoneda image of the source map of
schemes. -/
theorem relativeProperty_quotientStackProjection_realization
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} C S hS)]
    (hPs : P (realization G C hS hU hR hP).source) :
    RelativeProperty.{u, u + 1, u + 1} C S hS P
      (quotientStackProjectionHom (realization G C hS hU hR hP)) :=
  QuotientAtlas.relativeProperty_of_prop_source.{u, u}
    (realization G C hS hU hR hP) P hPs

/-- **The projection of the quotient stack of a groupoid scheme is étale when the source map of
the groupoid scheme is.** For `G = (U, R, s, t, c)` a groupoid scheme whose object scheme, arrow
scheme and scheme of composable pairs the site contains, and whose source map `s : R ⟶ U` is
étale, the canonical projection `π : S_U ⟶ [U/R]` of **Stacks 044R** is étale in the relative
sense of **Stacks 03YK**.

Étaleness of morphisms of algebraic spaces over `S` is stable under base change by
**Stacks 03FU** and local on the target for the fppf topology by **Stacks 042B**, so
`Stacks.Groupoids.GroupoidScheme.relativeProperty_quotientStackProjection_realization` applies;
the source map of the realization is the Yoneda image of `s`, and
`AlgebraicGeometry.Space.isEtale_yoneda_map_iff` turns étaleness of `s` into étaleness of that
morphism of algebraic spaces. -/
theorem isRelativelyEtale_quotientStackProjection_realization
    (hs : Etale G.source.left) :
    RelativeProperty.{u, u + 1, u + 1} C S hS (Space.etaleMorphisms C S hS)
      (quotientStackProjectionHom (realization G C hS hU hR hP)) := by
  refine relativeProperty_quotientStackProjection_realization G C hS hU hR hP
    (Space.etaleMorphisms C S hS) ?_
  show Space.IsEtale C S hS (realization G C hS hU hR hP).source.hom
  rw [realization_source G C hS hU hR hP]
  refine (Space.isEtale_yoneda_map_iff C S hS (Space.schemeSiteMap C hS hR hU G.source)).2 ?_
  rw [Space.toScheme_map_schemeSiteMap_eq C hS hR hU G.source]
  exact hs

end Stacks.Groupoids.GroupoidScheme

end
