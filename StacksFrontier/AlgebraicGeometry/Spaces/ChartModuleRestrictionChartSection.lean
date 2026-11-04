module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators

/-!
# The identification of the chart restriction with the étale restriction, on a chart section

`AlgebraicGeometry.Space.chartModuleRestrictionIsoChartSmallEtaleRestriction` identifies the
inverse image of an `𝒪_X`-module along the structure morphism of an étale scheme chart with its
restriction to the small étale site of that chart. This file describes the value of this
identification on chart sections.

## Main results

* `chartModuleRestrictionIsoChartSmallEtaleRestriction_hom_val_app_modulePullbackUnitSection`:
  the identification carries the chart section of `s` along a diagram of charts over the
  structure morphism of the chart to the section of the étale restriction that the unit of
  `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` and the chartwise universal property
  of the direct image produce from `s`.

## Implementation notes

*The statement is on a chart section, not on an arbitrary one.*  The source of the
identification is an inverse image of modules, whose sections over a chart are a sheafification
of an extension of scalars and so have no description; the sections in the image of
`AlgebraicGeometry.Space.modulePullbackUnitSection` are the ones that do, and they generate.
This is the shape of
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_val_app_modulePullbackUnitSection`, which
reads the comparison of Stacks 03LU on the same family.

*The proof is naturality of the chartwise universal property, and nothing else.*  The chart
section is `AlgebraicGeometry.Space.modulePushforwardCounitApp` of the unit of the Stacks 03LU
adjunction, so moving the identification across it is
`AlgebraicGeometry.Space.modulePushforwardCounitApp_map`; and the unit of the Stacks 03LU
adjunction followed by the direct image of the identification *is* the unit of étale
restriction, by `AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_app`, which holds by
`Eq.refl`.  So no composite of morphisms of sheaves of modules is formed anywhere, which is what
keeps the cost at one lemma application: composing under the inverse image of modules sends
`whnf` through a sheafification left adjoint.

*The target is written as the étale pullback and not as
`AlgebraicGeometry.Space.chartSmallEtaleRestriction`.*  The two are definitionally equal — that
is what makes the identification typecheck at all — but
`AlgebraicGeometry.Space.modulePushforwardCounitApp` asks for a module on the chart space, and
that is the spelling the étale pullback has by construction.

Nothing here raises a compiler limit or disables a linter, and no declaration here carries a
`stacks` tag: this is the value of one factor of a composite, an input to the chart comparison of
Stacks 07SI rather than an assertion of any tag.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The identification of the chart restriction with the étale restriction, on a chart
section.**  For an étale scheme chart `A` of `X` and a diagram `d` of charts over the structure
morphism of `A`, the comparison
`AlgebraicGeometry.Space.chartModuleRestrictionIsoChartSmallEtaleRestriction` carries the chart
component `AlgebraicGeometry.Space.modulePullbackUnitSection` of the unit of the Stacks 03D7
adjunction at a section `s` to the section the unit of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` and the chartwise universal property of
the direct image produce from `s`.

This is the value description that
`AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail` lacked at this factor; see this
file's implementation notes. -/
theorem chartModuleRestrictionIsoChartSmallEtaleRestriction_hom_val_app_modulePullbackUnitSection
    (M : Modules.{u, u} B S hS X.1 X.2) (A : SmallEtale B S hS X.1)
    (d : ChartDiagram B S hS (chartSpace B S hS X A).1 X.1 (chartToSpace B S hS X A).hom)
    (s : M.val.obj (op d.V)) :
    (chartModuleRestrictionIsoChartSmallEtaleRestriction B S hS X M A).hom.val.app (op d.U)
        (modulePullbackUnitSection B S hS (chartToSpace B S hS X A) M d s) =
      modulePushforwardCounitApp B S hS (chartToSpace B S hS X A)
        ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X A)
          (isEtale_chartToSpace B S hS X A)).obj M) d
        (((etaleModulePullbackAdjunction B S hS (chartToSpace B S hS X A)
            (isEtale_chartToSpace B S hS X A)).unit.app M).val.app (op d.V) s) :=
  (modulePushforwardCounitApp_map B S hS (chartToSpace B S hS X A)
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X A)
      (isEtale_chartToSpace B S hS X A)).hom.app M) d
    (((modulePullbackAdjunction B S hS (chartToSpace B S hS X A)).unit.app M).val.app
      (op d.V) s)).symm

end AlgebraicGeometry.Space

end
