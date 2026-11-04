module

public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionCounitEssImage

/-!
# The glueing step of Stacks 0GQD: from the charts of `X` to all of `𝒳`

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`X`, and let `π_X^* ⊣ i_X^*` be the adjunction
`AlgebraicGeometry.Space.projectionModulePullbackAdjunction`, whose right adjoint is restriction
to the small étale site of `X` (equation 075K).  The second input of Stacks 0GQD is
`AlgebraicGeometry.Space.ProjectionPullbackCounitIsIso`, equivalently the object-level
`AlgebraicGeometry.Space.ProjectionPullbackEssImage`.

This file supplies the **globalization**: the passage from the chart-local statements to the
single global one.  The source's proof of that input reads "choose a surjective étale `U ⟶ X`
and check the claim after restricting to `𝒳_étale/x = (Sch/U)_étale`", and this file is exactly
that sentence, with the two halves separated:

* the **covering** half, which is free.  The objects `u_X W` of `𝒳` coming from the étale charts
  `W` of `X` cover the final object of the inherited étale site of `𝒳`
  (`AlgebraicGeometry.Space.restrictionFunctor_coversTop`, Stacks 073M), and invertibility of a
  morphism of sheaves of modules is local on a site
  (`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over`).  So the counit is
  invertible as soon as it is invertible over each chart slice `𝒳/u_X W`, and that reduction is
  `AlgebraicGeometry.Space.projectionPullbackCounitIsIso_of_chartSlice`.  It is not a
  strengthening: `AlgebraicGeometry.Space.chartSliceCounitIsIso_iff` is an equivalence.
* the **chart** half, of which the part at the chart objects themselves is also free.  The
  counit is already an isomorphism *on sections over every object `u_X W`*, at every
  `𝒪_𝒳`-module and with no quasi-coherence hypothesis
  (`AlgebraicGeometry.Space.isIso_val_app_projectionPullbackCounit_chart`): the counit becomes
  an isomorphism after restriction along `u_X` for formal reasons
  (`AlgebraicGeometry.Space.isIso_moduleRestriction_map_projectionPullbackCounit`), restriction
  along `u_X` is a `CategoryTheory.SheafOfModules.pushforward`, and the components of a
  pushforward are the components at the objects in the image.

## What is left, and where it has to come from

What the reduction leaves is
`AlgebraicGeometry.Space.ChartSliceCounitIsIso`: the counit is invertible over the *slice* of
`𝒳` at a chart object, not merely at that object.  By the localization equivalence of
Stacks 06W0 that slice is `(Sch/W)_étale`, the **big** étale site of the scheme `W` below
`u_X W`, whose objects are arbitrary schemes over `W` and not only étale ones.

Of the source's two further appeals, **Descent, Section 03DR for the scheme `W` is no longer
missing**: the essential-surjectivity half of Descent, Proposition 03DX (1) *on the slice* is a
theorem at every topology and with no hypothesis,
`AlgebraicGeometry.FibredSite.quasicoherentIsEssImageLocalizationAssociatedModuleKind`, and what
it gives for a *map* is the conservativity statement
`AlgebraicGeometry.FibredSite.isIso_of_isIso_val_app_localizationOpens`: a morphism of
quasi-coherent modules on the slice is invertible as soon as its components at the slice objects
lying over the **opens** of `W` are.  Both are at the module universe `u`, which the statements
below reach (see the next section).

What remains is the identification of those slice objects as chart objects.  The components at
the chart objects are free, by the second bullet above; the opens of `W` are étale over `W` and
so over `X`, so the slice objects over them *ought* to be chart objects, and
`AlgebraicGeometry.Space.chartOpens` is the inclusion of the Zariski opens of a chart into the
small étale site of `X` that says as much upstairs.  What is not in the tree is the comparison of
that inclusion with `AlgebraicGeometry.FibredSite.localizationEquivalence`, which is what would
let the free half discharge the hypothesis of the conservativity.  Note that
`AlgebraicGeometry.Space.chartRestriction_iso` is **not** the missing piece: it is Remark 0GQA at
the *small* étale site of `W`, which is `Over W` inside `X_étale`
(`AlgebraicGeometry.Space.chartLocalSliceFunctor_comp_overPost`), so its objects are again chart
objects and the counit is already invertible there by the free half.

## The universes: free, and `hunit` is why

Everything here is stated at the module universe `max u m`, with `u` the universe of the schemes
and `v`, `w` the two universes of `𝒳`.  At `m := u` that is `u`, the universe at which Descent,
Proposition 03DX (1) lives; at `m := max (u + 1) w m'` it is the universe of the two
conditional 0GQD statements.  **No universe is lost by the globalization**, which is the point of
routing it through `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over`: that lemma
leaves the module universe of the sheaves free.

**The module universe is not pinned at `max (u + 1) w m`.**  Using
`AlgebraicGeometry.Space.isIso_unit_moduleRestriction` in place of `hunit` would pin it there, so
the statements ask for invertibility of the unit instead.  With `hunit` a hypothesis the
module universe is free, and the hypothesis is discharged above `u + 1` by
`AlgebraicGeometry.Space.isIso_unit_projectionModulePullbackAdjunction` and at `u` by
`AlgebraicGeometry.Space.isIso_unit_moduleRestriction'`.  That is what lets this reduction meet
Descent, Proposition 03DX (1), whose module universe cannot be raised —
`AlgebraicGeometry.Scheme.Modules` is `CategoryTheory.SheafOfModules.{u}` with no module universe
parameter, and `CategoryTheory.SheafOfModules.isQuasicoherent` ties the module universe to the
ring universe, so no `ULift` transport bridges the gap.

## Main definitions

* `AlgebraicGeometry.Space.ChartSliceCounitIsIso`: **the glueing hypothesis** — the counit of
  `π_X^* ⊣ i_X^*` is invertible over the slice of `𝒳` at each chart object.

## Main results

* `AlgebraicGeometry.Space.isIso_val_app_projectionPullbackCounit_chart`: the counit is
  invertible on sections over every chart object, at every module and with no hypothesis beyond
  `hunit`.
* `AlgebraicGeometry.Space.projectionPullbackCounitIsIso_of_chartSlice` and
  `AlgebraicGeometry.Space.projectionPullbackEssImage_of_chartSlice`: **the globalization** —
  the glueing hypothesis discharges the second input of Stacks 0GQD.
* `AlgebraicGeometry.Space.chartSliceCounitIsIso_iff`: the glueing hypothesis is *equivalent* to
  that input, so nothing is smuggled in by reformulating it chart-locally.

## References

* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 03DR](https://stacks.math.columbia.edu/tag/03DR)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u v w m

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (X.1 ⋙ typeToCat)).p)

/-! ### The counit at a chart object -/

/-- **The counit of `π_X^* ⊣ i_X^*` is invertible on sections over every chart object**, at
every `𝒪_𝒳`-module and with no quasi-coherence hypothesis.

Restriction along `u_X : X_étale ⥤ 𝒳` is a `CategoryTheory.SheafOfModules.pushforward`
(`AlgebraicGeometry.Space.moduleRestriction`), the counit becomes invertible after it for formal
reasons (`AlgebraicGeometry.Space.isIso_moduleRestriction_map_projectionPullbackCounit`), and the
component at `W` of a pushforward along `u_X` is the restriction of scalars of the component at
`u_X W`, which reflects invertibility.  So this is the whole of the source's "the restricted map
is the map for the scheme `U`, where it is an isomorphism" at the chart objects themselves; the
content of Stacks 0GQD's second input lies at the objects of `𝒳` lying over a chart object
without being one. -/
theorem isIso_val_app_projectionPullbackCounit_chart
    (hunit : IsIso (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e).unit)
    (ℱ : SheafOfModules.{max u m}
      (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale))
    (W : SmallEtale B S hS X.1) :
    IsIso (((projectionModulePullbackAdjunction.{u, v, w, m}
      B S hS X p hp e).counit.app
      ℱ).val.app (op ((restrictionFunctor B S hS X.1 p e).obj W))) := by
  let := restrictionFunctor_isContinuous B S hS X.1 p hp e
  have h : IsIso ((SheafOfModules.pushforward.{max u m}
      (restrictionStructureHom B S hS X p hp e)).map
      ((projectionModulePullbackAdjunction.{u, v, w, m}
        B S hS X p hp e).counit.app ℱ)) :=
    isIso_moduleRestriction_map_projectionPullbackCounit.{u, v, w, m} B S hS X p hp e hunit ℱ
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward
    (restrictionStructureHom B S hS X p hp e) _ h (op W)

/-! ### The glueing hypothesis -/

/-- **The glueing hypothesis of Stacks 0GQD**: for every quasi-coherent `𝒪_𝒳`-module, the counit
`π_X^*(ℱ|_{X_étale}) ⟶ ℱ` is invertible after restriction to the slice of `𝒳` at the object
`u_X W` attached to an étale chart `W` of `X`.

This is the source's "check the claim after restricting to `𝒳_étale/x = (Sch/U)_étale`" for a
chart `x = u_X W`.  By the localization equivalence of Stacks 06W0 that slice is the *big* étale
site of the scheme below `u_X W`, so the hypothesis is strictly more than invertibility at the
chart objects, which
`AlgebraicGeometry.Space.isIso_val_app_projectionPullbackCounit_chart` already gives from
`hunit` alone: the slice contains every scheme over that scheme, and only the étale ones are
chart objects.  What closes the remaining distance is Descent, Proposition 03DX (1) on the slice
together with the identification of the slice objects over the opens of the scheme as chart
objects; see the module docstring. -/
abbrev ChartSliceCounitIsIso : Prop :=
  ∀ (M : FibredSite.quasicoherentModules.{u, v, w, max u m} B S hS p hp)
      (W : SmallEtale B S hS X.1),
    IsIso (((projectionModulePullbackAdjunction.{u, v, w, m}
      B S hS X p hp e).counit.app
      ((FibredSite.toSiteModules B S hS p hp SiteKind.etale).obj M)).over
      ((restrictionFunctor B S hS X.1 p e).obj W))

/-! ### The globalization -/

/-- **The globalization of Stacks 0GQD's second input: the chart slices suffice.**  If the
counit of `π_X^* ⊣ i_X^*` is invertible over the slice of `𝒳` at every chart object, then it is
invertible.

Two facts combine, and both are already in the tree.  The chart objects cover the final object
of the inherited étale site of `𝒳`, which is Stacks 073M
(`AlgebraicGeometry.Space.restrictionFunctor_coversTop`; a single surjective étale chart already
suffices, by `AlgebraicGeometry.Space.exists_restrictionFunctor_coversTop_singleton`).  And
invertibility of a morphism of sheaves of modules is local on a site, by
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over`, which leaves the module
universe free — so the reduction is available at every module universe the quasi-inverse is
defined at. -/
theorem projectionPullbackCounitIsIso_of_chartSlice
    (h : ChartSliceCounitIsIso.{u, v, w, m} B S hS X p hp e) :
    ProjectionPullbackCounitIsIso.{u, v, w, m} B S hS X p hp e := fun M =>
  Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over
    (restrictionFunctor_coversTop B S hS X.1 p X.2 hp e) _ (h M)

/-- **The globalization, read on objects**: if the counit of `π_X^* ⊣ i_X^*` is invertible over
the slice of `𝒳` at every chart object, then every quasi-coherent `𝒪_𝒳`-module is `π_X^*` of an
`𝒪_X`-module.

This is `AlgebraicGeometry.Space.projectionPullbackCounitIsIso_of_chartSlice` followed by
`AlgebraicGeometry.Space.projectionPullbackCounitIsIso_iff_essImage`, which says that the
map-level and object-level readings of Stacks 0GQD's second input agree. -/
theorem projectionPullbackEssImage_of_chartSlice
    (hunit : IsIso (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e).unit)
    (h : ChartSliceCounitIsIso.{u, v, w, m} B S hS X p hp e) :
    ProjectionPullbackEssImage.{u, v, w, m} B S hS X p hp e :=
  (projectionPullbackCounitIsIso_iff_essImage.{u, v, w, m} B S hS X p hp e hunit).1
    (projectionPullbackCounitIsIso_of_chartSlice.{u, v, w, m} B S hS X p hp e h)

/-- The glueing hypothesis is *implied* by the input it is used for: restriction to a slice is a
functor, so it carries an invertible counit to an invertible one. -/
theorem chartSliceCounitIsIso_of_projectionPullbackCounitIsIso
    (h : ProjectionPullbackCounitIsIso.{u, v, w, m} B S hS X p hp e) :
    ChartSliceCounitIsIso.{u, v, w, m} B S hS X p hp e := fun M W =>
  let := h M
  (SheafOfModules.overFunctor (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale)
    ((restrictionFunctor B S hS X.1 p e).obj W)).map_isIso _

/-- **The glueing hypothesis and Stacks 0GQD's second input are equivalent.**  So nothing is
lost by reformulating that input over the chart slices, and nothing is smuggled in either: the
reformulation is exactly the source's reduction to `𝒳_étale/x = (Sch/U)_étale`, made available
to whoever discharges it. -/
theorem chartSliceCounitIsIso_iff :
    ChartSliceCounitIsIso.{u, v, w, m} B S hS X p hp e ↔
      ProjectionPullbackCounitIsIso.{u, v, w, m} B S hS X p hp e :=
  ⟨projectionPullbackCounitIsIso_of_chartSlice.{u, v, w, m} B S hS X p hp e,
    chartSliceCounitIsIso_of_projectionPullbackCounitIsIso.{u, v, w, m} B S hS X p hp e⟩

end AlgebraicGeometry.Space

end
