module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSliceCounitResidueLocation
public import StacksFrontier.AlgebraicGeometry.Stacks.ProjectionModulePullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationConservative
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpaceExtensions

/-!
# Descent on the chart slice closes Stacks 0GQD

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`X`.  The input Stacks 0GQD still needed was
`AlgebraicGeometry.Space.ProjectionPullbackCounitIsIso`, equivalently the chart-local
`AlgebraicGeometry.Space.ChartSliceCounitIsIso`: the counit of `π_X^* ⊣ i_X^*` is invertible
over the slice of `𝒳` at each chart object `u_X W`.

This file runs the source's argument on that slice.  What the argument reduces to is **not about
modules at all**:

> `AlgebraicGeometry.Space.ChartSliceOpensAreCharts`: for a chart `W` of `X` and an open `V` of
> the scheme below `u_X W`, the object of `𝒳/u_X W` lying over `V` under the Stacks 06W0
> identification `𝒳_étale/u_X W = (Sch/W)_étale` is isomorphic to a chart object.

and that statement is a theorem, `AlgebraicGeometry.Space.chartSliceOpensAreCharts`, at every
pair of universes for `𝒳`.  So both clauses of Stacks 0GQD hold here with no hypothesis beyond
the source's, for `𝒳 : Type (u + 1)` with `Category.{u} 𝒳` and at the module universe `u`.

The three inputs that reduce the glueing hypothesis to that statement are theorems of the library:

* **Descent, Proposition 03DX (1) on the slice**, in the map-level form a counit argument needs:
  `AlgebraicGeometry.FibredSite.isIso_of_isIso_val_app_localizationOpens` — a morphism of
  modules quasi-coherent on `𝒳_τ/x` is invertible as soon as its components at the slice objects
  over the opens of the scheme below `x` are.  Unconditional, every `τ`.  At `τ = .etale` this is
  Descent, Section 03DR for the scheme below the chart, which is what the source appeals to.
* **the free half of the chart statement**:
  `AlgebraicGeometry.Space.isIso_val_app_projectionPullbackCounit_of_iso_chart` — the counit is
  invertible on sections over every object isomorphic to a chart object, at every module, from
  invertibility of the unit alone.  This is the source's "the restricted map is the map for the
  scheme `U`, where it is an isomorphism".
* **quasi-coherence of the two modules the counit runs between**: of its target by Stacks 0EM8 at
  `τ = .etale`, `AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_etale`, and of its source
  by Modules on Sites 03DO for `π_X`,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_projectionModulePullback`, applied to the
  restriction, which `hres` says is quasi-coherent.  Quasi-coherence then descends to the slice by
  `Stacks.SheafOfModules.isQuasicoherentOnSite_over`.

## How the chart statement is proved

The obstacle was that `AlgebraicGeometry.FibredSite.localizationEquivalence'` is built from
essential surjectivity of `CategoryTheory.Over.post p` and so has no formula on objects; the
object of `𝒳/u_X W` lying over an open can only be named through its *inverse*.  What closes it
is that the *functor* of that equivalence does have a formula, and is literally the chart-local
localization functor the identification of Remark 0GQA is stated against:

* `AlgebraicGeometry.Space.localizationEquivalence_functor_eq_chartLocalOverPost` — the functor
  of Stacks 06WI at a chart object **is** `AlgebraicGeometry.Space.chartLocalOverPost`, by `rfl`.
* `AlgebraicGeometry.Space.chartLocalInclusion_obj_opensObj` — the small étale inclusion of
  Stacks 06W1 carries an open of the scheme below the chart object, read as an object of its
  small étale site by `AlgebraicGeometry.SmallEtale.opensObj`, to the object
  `(AlgebraicGeometry.BigFppfOver.opensToBig …).obj V` the criterion names, again by `rfl`.

So `AlgebraicGeometry.Space.chartLocalSliceFunctor_comp_overPost` — the object-level half of
Remark 0GQA, an *equality* of functors — says that the functor of Stacks 06WI carries the slice
object `(AlgebraicGeometry.Space.chartLocalSliceFunctor …).obj V` to exactly the object the
criterion names.  That slice object is `CategoryTheory.Over.post u_X` of an object of `U_étale/W`,
so its `.left` is a chart object on the nose; the unit isomorphism of the equivalence then moves
it across to the inverse's value, and `CategoryTheory.Over.forget` reads the isomorphism in `𝒳`.

Nothing is transported along the equality of schemes
`AlgebraicGeometry.Space.restrictionChartObject_base_eq`.  The open `V` is taken on the scheme
below the chart *object*, which is where the criterion puts it, and the discrepancy with the
scheme below the chart is already absorbed by
`AlgebraicGeometry.Space.chartLocalSiteEquivalence`, which is
`AlgebraicGeometry.Space.chartSchemeEquivalence` transported along that equality.  In particular
the inclusion `AlgebraicGeometry.Space.chartOpens` of the Zariski opens of a chart into the small
étale site of `X`, whose opens live on `AlgebraicGeometry.Space.etaleChartScheme`, is not used.

## Main definitions

* `AlgebraicGeometry.Space.ChartSliceOpensAreCharts`: the object-level statement about the chart
  slices of `𝒳` the source's argument reduces to.

## Main results

* `AlgebraicGeometry.Space.chartSliceOpensAreCharts`: **that statement, unconditionally**, at
  every pair of universes for `𝒳`.
* `AlgebraicGeometry.Space.chartSliceCounitIsIso` and
  `AlgebraicGeometry.Space.projectionPullbackCounitIsIso`: Stacks 0GQD's glueing input at the
  module universe `u`, over `hunit` and `hres`.
* `AlgebraicGeometry.Space.projectionPullbackCounitIsIso'`: the same with `hunit` and `hres`
  discharged, for `𝒳 : Type (u + 1)` with `Category.{u} 𝒳`.
* `AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_unconditional` and
  `AlgebraicGeometry.Space`
  `.nonempty_inv_toSiteModules_iso_projectionModulePullback_unconditional`:
  **both clauses of Stacks 0GQD, with no hypothesis beyond the source's.**

## References

* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 03DR](https://stacks.math.columbia.edu/tag/03DR)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u v w

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (X.1 ⋙ typeToCat)).p)

/-- **The statement about objects the source's proof of Stacks 0GQD reduces to.**  For an étale
chart `W` of the algebraic space `X` and a Zariski open `V` of the scheme below the chart object
`u_X W`, the object of the slice `𝒳/u_X W` which corresponds to `V` under the Stacks 06W0
identification `𝒳_étale/u_X W = (Sch/W)_étale` is isomorphic to a chart object.

The object is named through the *inverse* of
`AlgebraicGeometry.FibredSite.localizationEquivalence'` because that equivalence has no formula on
objects: it is got from essential surjectivity of `CategoryTheory.Over.post p`.  That is the form
in which `AlgebraicGeometry.FibredSite.isIso_of_isIso_val_app_localizationOpens` — Descent,
Proposition 03DX (1) on the slice, read on a map — leaves it to its consumer, and the free half
of the chart statement settles its conclusion at a chart object.

It is a theorem, `AlgebraicGeometry.Space.chartSliceOpensAreCharts`. -/
abbrev ChartSliceOpensAreCharts : Prop :=
  ∀ (W : SmallEtale B S hS X.1)
      (V : (FibredSite.baseScheme' B S hS p ((restrictionFunctor B S hS X.1 p e).obj W)).Opens),
    ∃ W' : SmallEtale B S hS X.1,
      Nonempty ((restrictionFunctor B S hS X.1 p e).obj W' ≅
        ((FibredSite.localizationEquivalence' B S hS p hp
              ((restrictionFunctor B S hS X.1 p e).obj W)).inverse.obj
            ((BigFppfOver.opensToBig B
              (FibredSite.baseScheme' B S hS p ((restrictionFunctor B S hS X.1 p e).obj W))
              (FibredSite.contains_baseScheme' B S hS p
                ((restrictionFunctor B S hS X.1 p e).obj W))).obj V)).left)

include hp in
/-- **The functor of the equivalence of Stacks 06WI at a chart object is the chart-local
localization functor**, on the nose.

`AlgebraicGeometry.FibredSite.localizationEquivalence'` is `CategoryTheory.Over.post p` followed
by `CategoryTheory.Over.iteratedSliceEquiv`, and that composite sends a slice object `f : Y ⟶ x`
to `(p.map f).left`, which is what `CategoryTheory.Over.post (p ⋙ CategoryTheory.Over.forget _)`
— `AlgebraicGeometry.Space.chartLocalOverPost` — sends it to.  The two codomains are the same
category as well, `AlgebraicGeometry.BigFppfSite.obj` of a contained scheme being the object of
the bounded category it was read off.

This is the comparison the object-level half of Remark 0GQA,
`AlgebraicGeometry.Space.chartLocalSliceFunctor_comp_overPost`, is stated against; having it as
an equality is what lets that half be used on the inverse, which has no formula on objects. -/
theorem localizationEquivalence_functor_eq_chartLocalOverPost (W : SmallEtale B S hS X.1) :
    (FibredSite.localizationEquivalence' B S hS p hp
        (restrictionChartObject B S hS X p e W)).functor =
      chartLocalOverPost B S hS X p e W :=
  rfl

/-- **The small étale inclusion of Stacks 06W1 carries an open of the scheme below a chart object
to the object Descent, Proposition 03DX (1) on the slice names.**  Both sides are the open
immersion of `V`, read in the big fppf slice at that scheme; the small étale site it passes
through has the same size cutoff, so the change of bounded category is the identity on it. -/
theorem chartLocalInclusion_obj_opensObj (W : SmallEtale B S hS X.1)
    (V : (FibredSite.baseScheme' B S hS p (restrictionChartObject B S hS X p e W)).Opens) :
    (chartLocalInclusion B S hS X p e W).obj
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B) _ _ V) =
      (BigFppfOver.opensToBig B
        (FibredSite.baseScheme' B S hS p (restrictionChartObject B S hS X p e W))
        (FibredSite.contains_baseScheme' B S hS p
          (restrictionChartObject B S hS X p e W))).obj V :=
  rfl

include hp in
/-- **The objects of a chart slice lying over the opens of the scheme below the chart are chart
objects**, at every pair of universes for `𝒳`.

The witness is produced, not chosen.  Read the open `V` as an object `T` of the small étale site
of the scheme below `u_X W` (`AlgebraicGeometry.SmallEtale.opensObj`) and push it into the slice
of `𝒳` at `u_X W` by `AlgebraicGeometry.Space.chartLocalSliceFunctor`, the chart-local
equivalence of sites followed by `CategoryTheory.Over.post u_X`.  Its underlying object of `𝒳` is
then `u_X` of an étale chart by construction, which is the chart object asked for.

That it is the right object is the object-level half of Remark 0GQA,
`AlgebraicGeometry.Space.chartLocalSliceFunctor_comp_overPost`: composed with the chart-local
localization functor, `chartLocalSliceFunctor` is the small étale inclusion of Stacks 06W1.  By
`AlgebraicGeometry.Space.localizationEquivalence_functor_eq_chartLocalOverPost` that localization
functor is the functor of the equivalence of Stacks 06WI, and by
`AlgebraicGeometry.Space.chartLocalInclusion_obj_opensObj` the inclusion sends `T` to
`(AlgebraicGeometry.BigFppfOver.opensToBig …).obj V`.  So the equivalence carries the slice
object to that object; its unit isomorphism moves the slice object to the value of the inverse
there, and `CategoryTheory.Over.forget` reads the isomorphism in `𝒳`. -/
theorem chartSliceOpensAreCharts : ChartSliceOpensAreCharts B S hS X p hp e := by
  intro W V
  let T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      (p.obj (restrictionChartObject B S hS X p e W)).left.1
      (Stack.contains_base B (associatedBigEtaleSite B) rfl S hS p
        (restrictionChartObject B S hS X p e W)) :=
    _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B) _ _ V
  refine ⟨((chartLocalSiteEquivalence B S hS X p e W).functor.obj T).left, ⟨?_⟩⟩
  let E := FibredSite.localizationEquivalence' B S hS p hp (restrictionChartObject B S hS X p e W)
  have hkey : E.functor.obj ((chartLocalSliceFunctor B S hS X p e W).obj T) =
      (BigFppfOver.opensToBig B
        (FibredSite.baseScheme' B S hS p (restrictionChartObject B S hS X p e W))
        (FibredSite.contains_baseScheme' B S hS p
          (restrictionChartObject B S hS X p e W))).obj V :=
    (Functor.congr_obj
        (localizationEquivalence_functor_eq_chartLocalOverPost B S hS X p hp e W) _).trans
      ((Functor.congr_obj (chartLocalSliceFunctor_comp_overPost B S hS X p e W) T).trans
        (chartLocalInclusion_obj_opensObj B S hS X p e W V))
  exact (Over.forget _).mapIso
    (E.unitIso.app ((chartLocalSliceFunctor B S hS X p e W).obj T) ≪≫
      E.inverse.mapIso (eqToIso hkey))

include hp in
/-- **The glueing hypothesis of Stacks 0GQD at the module universe `u`**, over `hunit` and `hres`.

Over each chart slice the counit runs between two modules quasi-coherent there — its target by
Stacks 0EM8 at `τ = .etale` (`AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_etale`) and
its source by Modules on Sites 03DO for `π_X`
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_projectionModulePullback`) applied to the
restriction, which `hres` says is quasi-coherent — so Descent, Proposition 03DX (1) on the slice
applies in the form
`AlgebraicGeometry.FibredSite.isIso_of_isIso_val_app_localizationOpens`, and asks only for the
components at the slice objects lying over the opens of the scheme below the chart.
`AlgebraicGeometry.Space.chartSliceOpensAreCharts` identifies those objects as chart objects,
where the components are invertible by the free half
`AlgebraicGeometry.Space.isIso_val_app_projectionPullbackCounit_of_iso_chart`. -/
theorem chartSliceCounitIsIso
    (hunit : IsIso (projectionModulePullbackAdjunction.{u, v, w, u} B S hS X p hp e).unit)
    (hres : RestrictionPreservesQuasicoherent.{u, v, w, u} B S hS X p hp e) :
    ChartSliceCounitIsIso.{u, v, w, u} B S hS X p hp e := by
  intro M W
  refine FibredSite.isIso_of_isIso_val_app_localizationOpens B S hS p hp SiteKind.etale
    ((restrictionFunctor B S hS X.1 p e).obj W)
    (Stacks.SheafOfModules.isQuasicoherentOnSite_over _
      (isQuasicoherentOnSite_projectionModulePullback B S hS X p hp e _ (hres M)) _)
    (Stacks.SheafOfModules.isQuasicoherentOnSite_over _
      (FibredSite.quasicoherentOnSiteOfLeFppf_etale B S hS p hp M.obj M.property) _)
    _ fun V => ?_
  obtain ⟨W', ⟨α⟩⟩ := chartSliceOpensAreCharts B S hS X p hp e W V
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_pushforward_map (𝟙 _) _ _
    (isIso_val_app_projectionPullbackCounit_of_iso_chart.{u, v, w, u} B S hS X p hp e hunit _ W' α)

include hp in
/-- **Stacks 0GQD's glueing input at the module universe `u`**, over `hunit` and `hres`, by the
globalization `AlgebraicGeometry.Space.projectionPullbackCounitIsIso_of_chartSlice`: the chart
objects cover the final object of the inherited étale site of `𝒳` (Stacks 073M) and invertibility
of a morphism of sheaves of modules is local. -/
theorem projectionPullbackCounitIsIso
    (hunit : IsIso (projectionModulePullbackAdjunction.{u, v, w, u} B S hS X p hp e).unit)
    (hres : RestrictionPreservesQuasicoherent.{u, v, w, u} B S hS X p hp e) :
    ProjectionPullbackCounitIsIso.{u, v, w, u} B S hS X p hp e :=
  projectionPullbackCounitIsIso_of_chartSlice.{u, v, w, u} B S hS X p hp e
    (chartSliceCounitIsIso B S hS X p hp e hunit hres)

end General

section SmallFibred

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (X.1 ⋙ typeToCat)).p)

include hp in
/-- **Stacks 0GQD's glueing input, unconditionally**, for `𝒳 : Type (u + 1)` with
`Category.{u} 𝒳` — the size a category fibred in groupoids over `(Sch/S)_fppf` actually has.
Both remaining hypotheses are theorems there: `hunit` is
`AlgebraicGeometry.Space.isIso_unit_moduleRestriction'` and `hres` is
`AlgebraicGeometry.Space.restrictionPreservesQuasicoherent`. -/
theorem projectionPullbackCounitIsIso' :
    ProjectionPullbackCounitIsIso.{u, u + 1, u, u} B S hS X p hp e :=
  projectionPullbackCounitIsIso.{u, u + 1, u} B S hS X p hp e
    (isIso_unit_moduleRestriction'.{u, u + 1, u} B S hS X p hp e
      (projectionModulePullbackAdjunction.{u, u + 1, u, u} B S hS X p hp e))
    (restrictionPreservesQuasicoherent B S hS X p hp e)

include hp in
/-- Restriction to the small étale site of `X` — equation 075K read on sheaves of modules — is an
equivalence `QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_X)` for a category fibred in groupoids representable by the
algebraic space `X`.

No hypothesis beyond the source's.  This is
`AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_counitIsIso` with its one
hypothesis discharged by `AlgebraicGeometry.Space.projectionPullbackCounitIsIso'`: the source's
argument on a chart slice, whose object-level residue
`AlgebraicGeometry.Space.chartSliceOpensAreCharts` is a theorem.  The module universe is `u` and
`𝒳` has the size a category fibred in groupoids over `(Sch/S)_fppf` has; the two conditional
carriers
`AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_descentInputs` and
`AlgebraicGeometry.Space.nonempty_inv_comp_toSiteModules_iso_projectionModulePullback` are at the
module universe `max (u + 1) w m` and two free universes for `𝒳`, which this does not reach. -/
theorem isEquivalence_quasicoherentRestriction_unconditional :
    (quasicoherentRestriction.{u, u + 1, u, u} B S hS X p hp e
      (restrictionPreservesQuasicoherent B S hS X p hp e)).IsEquivalence :=
  isEquivalence_quasicoherentRestriction_of_counitIsIso B S hS X p hp e
    (projectionPullbackCounitIsIso' B S hS X p hp e)

include hp in
/-- The quasi-inverse of restriction to the small étale site: the inverse of that equivalence is
`𝒢 ↦ π_X^*𝒢`, read on underlying modules.  No hypothesis beyond the source's. -/
theorem nonempty_inv_toSiteModules_iso_projectionModulePullback_unconditional :
    letI := isEquivalence_quasicoherentRestriction_unconditional B S hS X p hp e
    Nonempty ((quasicoherentRestriction.{u, u + 1, u, u} B S hS X p hp e
          (restrictionPreservesQuasicoherent B S hS X p hp e)).inv ⋙
        FibredSite.toSiteModules B S hS p hp .etale ≅
      (quasicoherentModulesProperty.{u, u} B S hS X).ι ⋙
        projectionModulePullback.{u, u + 1, u, u} B S hS X p hp e) :=
  nonempty_inv_toSiteModules_iso_projectionModulePullback_of_counitIsIso B S hS X p hp e
    (projectionPullbackCounitIsIso' B S hS X p hp e)

end SmallFibred

end AlgebraicGeometry.Space

end
