module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ProjectiveBundleBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionPullbackIsoAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeReadingOfModule

/-!
# The projective bundle of a module on an algebraic space, over its étale charts

Let `X` be an algebraic space over a scheme `S` and `ℰ` a quasi-coherent `𝒪_X`-module on its
small étale site.  Over an étale scheme chart `V` of `X` the module gives a quasi-coherent module
`ℰ|_V` on the scheme `V` — the inverse image of `ℰ` to `V`, read on the Zariski site of the
scheme, which is the chart restriction of `ℰ` — and `V` carries the projective bundle
`𝐏(ℰ|_V) = Proj_V(Sym(ℰ|_V)) ⟶ V` of Stacks 01OB.  A morphism `h : V' ⟶ V` of étale charts
identifies `ℰ|_{V'}` with the pullback of `ℰ|_V`, so the base-change comparison of projective
bundles gives a morphism

`𝐏(ℰ|_{V'}) ⟶ 𝐏(ℰ|_V)`

over `h`, and the square it forms with the two projections is cartesian (Stacks 01O3 for the
symmetric algebra).  This file constructs this family and proves that it is a functor on the
category of étale charts: the morphism attached to a composite is the composite of the
morphisms, and the morphism attached to an identity is the identity.  These are the cocycle
conditions which glue the charts `𝐏(ℰ|_V)` into the projective bundle of `ℰ` over `X`.

## Main definitions

* `AlgebraicGeometry.Space.chartBundleModule`: the module `ℰ|_V` on the scheme of the chart.
* `AlgebraicGeometry.Space.chartBundleModuleIso`: the identification
  `ℰ|_{V'} ≅ h^* ℰ|_V`.
* `AlgebraicGeometry.Space.chartBundle` and `AlgebraicGeometry.Space.chartBundleToChart`: the
  projective bundle `𝐏(ℰ|_V)` and its projection to the chart.
* `AlgebraicGeometry.Space.chartBundleMap`: the morphism `𝐏(ℰ|_{V'}) ⟶ 𝐏(ℰ|_V)` over a
  morphism of charts.

## Main results

* `AlgebraicGeometry.Space.chartBundleModuleRestrictIso`: the chart module is the chart
  restriction `AlgebraicGeometry.Space.restrictToChartScheme`.
* `AlgebraicGeometry.Space.chartBundleModuleIso_cocycle`: the identifications of the chart
  modules satisfy the cocycle condition.
* `AlgebraicGeometry.Space.isPullback_chartBundleMap`: the square over a morphism of charts is
  cartesian.
* `AlgebraicGeometry.Space.chartBundleMap_comp` and `AlgebraicGeometry.Space.chartBundleMap_id`:
  functoriality in the chart.

## Implementation notes

The chart module is `AlgebraicGeometry.Space.schemeReading` at the structure morphism of the
chart, and the identifications are its comparisons
`AlgebraicGeometry.Space.schemeReadingPullbackIso`, rather than the chart restriction
`AlgebraicGeometry.Space.restrictToChartScheme` with its comparison
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`.  The two chart modules are
isomorphic (`AlgebraicGeometry.Space.chartBundleModuleRestrictIso`), but only the first comes
with comparisons along *arbitrary* morphisms of schemes over `X` that compose
(`AlgebraicGeometry.Space.schemeReadingPullbackIso_comp`); that is what identifies the twists
of the chart bundles along the relation of a presentation, and so what descends `𝒪(1)` to the
projective bundle of `ℰ`.

The composition law is `Stacks.RelativeProj.projectiveBundleBaseChange_comp`, whose hypothesis is
the cocycle condition of the module identifications.  The identity law is derived from the
composition law as for the relative spectrum
(`AlgebraicGeometry.Space.chartRelativeSpecChartMap_id`): the morphism attached to an identity is
idempotent, and it is an isomorphism, being a base change of an isomorphism.

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2)

/-- The restriction `ℰ|_V` of a module on the small étale site of `X` to the scheme of an étale
chart `V`, read as the inverse image of `ℰ` to the chart on the Zariski site of its scheme. -/
abbrev chartBundleModule (V : SmallEtale B S hS X.1) : (chartScheme V).Modules :=
  schemeReading E (chartToSpace B S hS X V)

/-- The chart module is the chart restriction `AlgebraicGeometry.Space.restrictToChartScheme`. -/
def chartBundleModuleRestrictIso (V : SmallEtale B S hS X.1) :
    chartBundleModule E V ≅ restrictToChartSchemeModules B S hS X.1 X.2 E V :=
  schemeReadingChartIso E V

/-- The structure morphism of a chart factors through a morphism of charts. -/
theorem representedSpaceMap_toOver_map_comp_chartToSpace {V V' : SmallEtale B S hS X.1}
    (h : V' ⟶ V) :
    representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map h) ≫ chartToSpace B S hS X V =
      chartToSpace B S hS X V' :=
  ObjectProperty.hom_ext _ (yoneda_map_toOver_map_comp_hom h)

/-- The morphism of chart schemes underlying a morphism of étale charts, in the spelling of the
morphisms of the associated big étale site, which is the one the comparisons of the readings are
stated in.  It is `AlgebraicGeometry.Space.chartSchemeMap`, by `rfl`. -/
abbrev chartSchemeMapOfSite {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    chartScheme V' ⟶ chartScheme V :=
  _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
    ((SmallEtale.toOver B S hS X.1).map h).left

/-- `AlgebraicGeometry.Space.chartSchemeMapOfSite h` is the morphism of chart schemes
`AlgebraicGeometry.Space.chartSchemeMap h`. -/
theorem chartSchemeMapOfSite_eq {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    chartSchemeMapOfSite h = chartSchemeMap h :=
  rfl

/-- The transport `AlgebraicGeometry.Scheme.Modules.pullbackCongr` along an equation whose two
sides are one morphism is the identity. -/
theorem pullbackCongr_self_hom_app {Y Z : Scheme.{u}} {p : Y ⟶ Z} (hp : p = p) (M : Z.Modules) :
    (Scheme.Modules.pullbackCongr hp).hom.app M = 𝟙 _ :=
  rfl

variable [hE : E.IsQuasicoherentOnSite]
include hE

/-- The restriction of a quasi-coherent module to the scheme of an étale chart is
quasi-coherent. -/
instance isQuasicoherent_chartBundleModule (V : SmallEtale B S hS X.1) :
    (chartBundleModule E V).IsQuasicoherent :=
  isQuasicoherent_schemeReading E hE (chartToSpace B S hS X V)

/-- The chart comparison of a quasi-coherent module along a morphism of étale charts is an
isomorphism. -/
instance isIso_restrictToChartSchemePullbackComparison_chartBundle
    {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    IsIso (restrictToChartSchemePullbackComparison B S hS X.1 X.2 E h) := by
  let : HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : HasSheafify (Opens.grothendieckTopology (chartScheme V')) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology (chartScheme V')).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact isIso_restrictToChartSchemePullbackComparison_of_isQuasicoherentOnSite B S hS X.2 E hE h

/-- The identification `ℰ|_{V'} ≅ h^* ℰ|_V` of the chart modules of a quasi-coherent module
along a morphism of étale charts: the comparison of the readings,
`AlgebraicGeometry.Space.schemeReadingPullbackIso`, read backwards. -/
def chartBundleModuleIso {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    chartBundleModule E V' ≅
      (Scheme.Modules.pullback (chartSchemeMapOfSite h)).obj (chartBundleModule E V) :=
  (schemeReadingPullbackIso E hE ((SmallEtale.toOver B S hS X.1).map h)
    (representedSpaceMap_toOver_map_comp_chartToSpace h)).symm

/-- The inverse of `AlgebraicGeometry.Space.chartBundleModuleIso h` is the comparison
`AlgebraicGeometry.Space.schemeReadingPullbackIso` of the readings along `h`. -/
@[simp]
theorem chartBundleModuleIso_inv {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    (chartBundleModuleIso E h).inv =
      (schemeReadingPullbackIso E hE ((SmallEtale.toOver B S hS X.1).map h)
        (representedSpaceMap_toOver_map_comp_chartToSpace h)).hom :=
  rfl

/-- **The cocycle condition of the identifications of the chart modules**, which is
`AlgebraicGeometry.Space.schemeReadingPullbackIso_comp`. -/
theorem chartBundleModuleIso_cocycle {V V' V'' : SmallEtale B S hS X.1} (h : V' ⟶ V)
    (h' : V'' ⟶ V') :
    (Scheme.Modules.pullbackComp (chartSchemeMapOfSite h') (chartSchemeMapOfSite h)).hom.app
          (chartBundleModule E V) ≫ (chartBundleModuleIso E (h' ≫ h)).inv =
      (Scheme.Modules.pullback (chartSchemeMapOfSite h')).map (chartBundleModuleIso E h).inv ≫
        (chartBundleModuleIso E h').inv := by
  have key := congrArg Iso.hom (schemeReadingPullbackIso_comp E hE
    ((SmallEtale.toOver B S hS X.1).map h') ((SmallEtale.toOver B S hS X.1).map h)
    (representedSpaceMap_toOver_map_comp_chartToSpace h)
    (representedSpaceMap_toOver_map_comp_chartToSpace h')
    (representedSpaceMap_toOver_map_comp_chartToSpace (h' ≫ h)))
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at key
  rw [chartBundleModuleIso_inv, chartBundleModuleIso_inv, chartBundleModuleIso_inv]
  refine Eq.trans ?_ (Eq.trans key.symm ?_)
  · rw [← pullbackCongr_hom_app_schemeReadingPullbackIso E hE
      ((SmallEtale.toOver B S hS X.1).map_comp h' h)
      (representedSpaceMap_toOver_map_comp_chartToSpace (h' ≫ h))
      (representedSpaceMap_toOver_map_comp_chartToSpace (h' ≫ h)),
      pullbackCongr_self_hom_app, Category.id_comp]
  · rfl

/-- **The projective bundle `𝐏(ℰ|_V)` over an étale chart `V`.** -/
abbrev chartBundle (V : SmallEtale B S hS X.1) : Scheme.{u} :=
  Stacks.RelativeProj.projectiveBundle (chartScheme V) (chartBundleModule E V)

/-- The projection `𝐏(ℰ|_V) ⟶ V`. -/
abbrev chartBundleToChart (V : SmallEtale B S hS X.1) : chartBundle E V ⟶ chartScheme V :=
  Stacks.RelativeProj.projectiveBundleToBase (chartScheme V) (chartBundleModule E V)

/-- **The morphism of chart projective bundles over a morphism of étale charts**
`𝐏(ℰ|_{V'}) ⟶ 𝐏(ℰ|_V)`: the base-change comparison of projective bundles along
`chartSchemeMap h` for the identification `chartBundleModuleIso`. -/
def chartBundleMap {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    chartBundle E V' ⟶ chartBundle E V :=
  Stacks.RelativeProj.projectiveBundleBaseChange (chartSchemeMapOfSite h) (chartBundleModule E V)
    (chartBundleModule E V') (chartBundleModuleIso E h)

/-- **The square of chart projective bundles over a morphism of charts is cartesian**:
`𝐏(ℰ|_{V'}) = V' ×_V 𝐏(ℰ|_V)`. -/
theorem isPullback_chartBundleMap {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    IsPullback (chartBundleMap E h) (chartBundleToChart E V') (chartBundleToChart E V)
      (chartSchemeMap h) :=
  Stacks.RelativeProj.isPullback_projectiveBundleBaseChange (chartSchemeMapOfSite h)
    (chartBundleModule E V) (chartBundleModule E V') (chartBundleModuleIso E h)

/-- The morphism of chart projective bundles lies over the morphism of charts. -/
@[reassoc]
theorem chartBundleMap_comp_chartBundleToChart {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    chartBundleMap E h ≫ chartBundleToChart E V = chartBundleToChart E V' ≫ chartSchemeMap h :=
  (isPullback_chartBundleMap E h).w

/-- **Functoriality of the chart projective bundles: the composition law.** -/
theorem chartBundleMap_comp {V V' V'' : SmallEtale B S hS X.1} (h : V' ⟶ V) (h' : V'' ⟶ V') :
    chartBundleMap E (h' ≫ h) = chartBundleMap E h' ≫ chartBundleMap E h :=
  (Stacks.RelativeProj.projectiveBundleBaseChange_comp (chartSchemeMapOfSite h')
    (chartSchemeMapOfSite h)
    (chartBundleModule E V) (chartBundleModule E V') (chartBundleModule E V'')
    (chartBundleModuleIso E h) (chartBundleModuleIso E h') (chartBundleModuleIso E (h' ≫ h))
    (chartBundleModuleIso_cocycle E h h')).symm

/-- **Functoriality of the chart projective bundles: the identity law.** -/
theorem chartBundleMap_id (V : SmallEtale B S hS X.1) :
    chartBundleMap E (𝟙 V) = 𝟙 (chartBundle E V) := by
  have : IsIso (chartBundleMap E (𝟙 V)) :=
    (isPullback_chartBundleMap E (𝟙 V)).isIso_fst_of_isIso
      (show IsIso (𝟙 (chartScheme V)) from inferInstance)
  have hidem := chartBundleMap_comp E (𝟙 V) (𝟙 V)
  rw [Category.comp_id] at hidem
  refine ((cancel_epi (chartBundleMap E (𝟙 V))).mp ?_).symm
  rw [Category.comp_id]
  exact hidem

end AlgebraicGeometry.Space

end
