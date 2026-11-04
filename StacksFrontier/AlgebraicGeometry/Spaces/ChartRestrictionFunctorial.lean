module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits

/-!
# Functoriality of the restriction of a module to an étale scheme chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `U` be an étale
scheme chart of `X`. The restriction `F ↦ F|_U` of an `𝒪_X`-module to the chart is
`AlgebraicGeometry.Space.restrictToChart`, built as a pushforward of sections followed by
Zariski sheafification. Each of those steps is a functor, and this file assembles them into a
functor of the module; in particular an isomorphism of `𝒪_X`-modules restricts to the chart.

## Main definitions

* `AlgebraicGeometry.Space.restrictToChartFunctor` is the restriction to an étale scheme chart
  as a functor of the module: the composite of the three steps of
  `AlgebraicGeometry.Space.restrictToChart` — raising the universe of the sections with
  `SheafOfModules.uliftForPresentationFunctor`, changing scalars along
  `AlgebraicGeometry.Space.chartRestrictionRingHom`, and sheafifying for the Zariski topology of
  the chart.
* `AlgebraicGeometry.Space.restrictToChartIso` restricts an isomorphism of `𝒪_X`-modules to an
  étale scheme chart.

## Main results

* `AlgebraicGeometry.Space.restrictToChartFunctor_obj`: the functor agrees with
  `AlgebraicGeometry.Space.restrictToChart` on objects.

## References

* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)

/-- The restriction of an `𝒪_X`-module to an étale scheme chart `U`, functorially in the
module: each of the three steps of `AlgebraicGeometry.Space.restrictToChart` — raising the
universe of the sections, changing scalars along
`AlgebraicGeometry.Space.chartRestrictionRingHom`, and Zariski sheafification — is a functor,
and this is their composite. -/
noncomputable def restrictToChartFunctor (U : SmallEtale B S hS X) :
    Modules.{u, m} B S hS X hX ⥤
      SheafOfModules.{max u m} (etaleChartScheme B S hS U).ringCatSheaf := by
  let J := Opens.grothendieckTopology (etaleChartScheme B S hS U)
  letI : HasSheafify J AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u m} _ _
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u m} _
  exact SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, m, u} ⋙
    SheafOfModules.forget _ ⋙
    PresheafOfModules.pushforward.{max u m} (chartRestrictionRingHom B S hS hX U) ⋙
    PresheafOfModules.sheafification.{max u m}
      (𝟙 (etaleChartScheme B S hS U).ringCatSheaf.obj)

/-- The functorial restriction to an étale scheme chart agrees with
`AlgebraicGeometry.Space.restrictToChart` on objects. -/
theorem restrictToChartFunctor_obj (G : Modules.{u, m} B S hS X hX)
    (U : SmallEtale B S hS X) :
    (restrictToChartFunctor B S hS hX U).obj G = restrictToChart B S hS hX G U :=
  rfl

/-- An isomorphism of `𝒪_X`-modules restricts to an isomorphism of their restrictions to an
étale scheme chart. -/
noncomputable def restrictToChartIso {G G' : Modules.{u, m} B S hS X hX} (e : G ≅ G')
    (U : SmallEtale B S hS X) :
    restrictToChart B S hS hX G U ≅ restrictToChart B S hS hX G' U :=
  (restrictToChartFunctor B S hS hX U).mapIso e

end AlgebraicGeometry.Space

end
