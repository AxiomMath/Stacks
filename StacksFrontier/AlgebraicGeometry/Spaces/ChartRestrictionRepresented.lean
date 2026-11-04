module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# The chart restriction as the identity-chart restriction of the chart pullback

Let `X` be an algebraic space over `S`, let `A` be an étale scheme chart of `X` and let `𝓕` be a
quasi-coherent `𝒪_X`-module. The chart restriction `𝓕|_A` of
`AlgebraicGeometry.Space.restrictToChart` is then the restriction, along the *identity* chart of
the algebraic space the chart represents, of the inverse image of `𝓕` on that algebraic space:

`𝓕|_A ≅ (p^*𝓕)|_{id}`, where `p : chartSpace A ⟶ X` is the structure morphism of the chart.

Both sides are readings of the same object, and the identification is the one the chart-space
machinery already supplies. On the small étale site, restricting `𝓕` to the chart is the étale
inverse image along `p` (`AlgebraicGeometry.Space.chartSmallEtaleRestrictionFunctorObjIso`,
which is definitional), and restricting `p^*𝓕` along the identity chart of the chart space is
the étale inverse image along the structure morphism of that identity chart, which is the
identity of the chart space. The two readings on the Zariski site of the chart scheme are then
matched by `AlgebraicGeometry.Space.restrictToChartIsoChartSchemeModule` and
`AlgebraicGeometry.Space.restrictToChartSchemeIsoChartSchemeModule`, both of which factor
through `AlgebraicGeometry.Space.chartSchemeModule`.

## Main results

* `AlgebraicGeometry.Space.chartToSpace_idEtaleChart_eq`: the structure morphism of the identity
  chart of the algebraic space an étale scheme chart represents is the identity.
* `AlgebraicGeometry.Space.chartSmallEtaleRestrictionIdEtaleChartIso`: the comparison on the
  small étale site of the chart.
* `AlgebraicGeometry.Space.chartSchemeModuleIdEtaleChartIso`: the comparison of the two
  chart-scheme transports.
* `AlgebraicGeometry.Space.restrictToChartIsoChartSpaceIdEtaleChart`: **the comparison itself**,
  for a quasi-coherent module.

## Implementation notes

Quasi-coherence is needed only because `AlgebraicGeometry.Space.chartSchemeModule`, through
which the two Zariski readings are matched, is defined only for a quasi-coherent module; the
comparison on the small étale site, `chartSmallEtaleRestrictionIdEtaleChartIso`, carries no
hypothesis.

The two sides are stated at the same chart scheme without any transport:
`AlgebraicGeometry.Space.chartSpace_eq_yoneda` makes the algebraic space a chart represents the
Yoneda algebraic space of the chart's object definitionally, so
`AlgebraicGeometry.Space.idEtaleChart` at that object is an étale chart of the chart space on
the nose and its chart scheme is the chart scheme one started with.

The identification of the étale inverse image of Equation 03LW with the inverse image of
Stacks 03LU along the same étale morphism is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`; it is used on both legs, so
that the unit law of Stacks 03LU can discharge the identity chart.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (A : SmallEtale B S hS X.1)

/-- The structure morphism of the identity chart of the algebraic space an étale scheme chart
represents is the identity of that algebraic space. -/
theorem chartToSpace_idEtaleChart_eq :
    chartToSpace B S hS (chartSpace B S hS X A)
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj A)) =
      𝟙 (chartSpace B S hS X A) :=
  ObjectProperty.hom_ext _ rfl

/-- **The restriction of an `𝒪_X`-module to an étale scheme chart, read on the small étale site
of the chart, is the restriction of its inverse image on the chart space along the identity
chart.** Both are the étale inverse image of Equation 03LW along the structure morphism of a
chart, and the structure morphism of an identity chart is an identity, so the unit law of
Stacks 03LU closes the comparison. -/
noncomputable def chartSmallEtaleRestrictionIdEtaleChartIso
    (F : Modules.{u, u} B S hS X.1 X.2) :
    chartSmallEtaleRestriction B S hS X F A ≅
      chartSmallEtaleRestriction B S hS (chartSpace B S hS X A)
        ((modulePullback B S hS (chartToSpace B S hS X A)).obj F)
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj A)) :=
  chartSmallEtaleRestrictionFunctorObjIso X F A ≪≫
    (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X A)
      (isEtale_chartToSpace B S hS X A)).symm.app F ≪≫
    (modulePullbackIdIso B S hS (chartSpace B S hS X A)).symm.app
      ((modulePullback B S hS (chartToSpace B S hS X A)).obj F) ≪≫
    eqToIso (congrArg
      (fun k : chartSpace B S hS X A ⟶ chartSpace B S hS X A ↦
        (modulePullback B S hS k).obj ((modulePullback B S hS
          (chartToSpace B S hS X A)).obj F))
      (chartToSpace_idEtaleChart_eq B S hS X A).symm) ≪≫
    (modulePullbackIsoEtaleModulePullback B S hS
      (chartToSpace B S hS (chartSpace B S hS X A)
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj A)))
      (isEtale_chartToSpace B S hS (chartSpace B S hS X A)
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj A)))).app _ ≪≫
    (chartSmallEtaleRestrictionFunctorObjIso (chartSpace B S hS X A)
      ((modulePullback B S hS (chartToSpace B S hS X A)).obj F)
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj A))).symm

/-- The chart-scheme transport of a quasi-coherent `𝒪_X`-module at a chart is the chart-scheme
transport of its inverse image on the chart space at the identity chart: the transport is an
equivalence applied to the reading on the small étale site of the chart, and those two readings
agree by `AlgebraicGeometry.Space.chartSmallEtaleRestrictionIdEtaleChartIso`. -/
noncomputable def chartSchemeModuleIdEtaleChartIso
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hN : ((modulePullback B S hS (chartToSpace B S hS X A)).obj F).IsQuasicoherentOnSite) :
    chartSchemeModule B S hS X F hF A ≅
      chartSchemeModule B S hS (chartSpace B S hS X A)
        ((modulePullback B S hS (chartToSpace B S hS X A)).obj F) hN
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj A)) :=
  (ObjectProperty.ι _).mapIso
    ((representedQuasicoherentSchemeEquivalence B S hS
      ((SmallEtale.toOver B S hS X.1).obj A)).inverse.mapIso
        ((ObjectProperty.fullyFaithfulι _).preimageIso
          (chartSmallEtaleRestrictionIdEtaleChartIso B S hS X A F)))

/-- **The restriction of a quasi-coherent `𝒪_X`-module to an étale scheme chart is the
restriction of its inverse image on the chart space along the identity chart of that chart
space.** Both Zariski readings factor through
`AlgebraicGeometry.Space.chartSchemeModule`, where the comparison is
`AlgebraicGeometry.Space.chartSchemeModuleIdEtaleChartIso`.

This is the compatibility of `AlgebraicGeometry.Space.restrictToChart` with the inverse image of
Stacks 03LU along a chart, in the only case in which the chart restriction is a restriction
along an identity chart; it is what lets a statement about the chart restriction on a chart of
`X` be read as a statement about the represented algebraic space the chart carries. -/
noncomputable def restrictToChartIsoChartSpaceIdEtaleChart
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    restrictToChart B S hS X.2 F A ≅
      restrictToChartScheme B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2
        ((modulePullback B S hS (chartToSpace B S hS X A)).obj F)
        (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj A)) :=
  have hN : ((modulePullback B S hS (chartToSpace B S hS X A)).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (chartToSpace B S hS X A) F hF
  restrictToChartIsoChartSchemeModule B S hS X F hF A ≪≫
    chartSchemeModuleIdEtaleChartIso B S hS X A F hF hN ≪≫
    (restrictToChartSchemeIsoChartSchemeModule B S hS (chartSpace B S hS X A)
      ((modulePullback B S hS (chartToSpace B S hS X A)).obj F) hN
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj A))).symm

end AlgebraicGeometry.Space

end
