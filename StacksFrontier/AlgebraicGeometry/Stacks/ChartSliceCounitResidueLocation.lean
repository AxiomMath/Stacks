module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSliceCounitGlobalization

/-!
# Where the residue of Stacks 0GQD's second input sits, object by object

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`X`, and let `π_X^* ⊣ i_X^*` be the adjunction
`AlgebraicGeometry.Space.projectionModulePullbackAdjunction`.  The glueing hypothesis
`AlgebraicGeometry.Space.ChartSliceCounitIsIso` of
`StacksFrontier/AlgebraicGeometry/Stacks/ChartSliceCounitGlobalization.lean` asks the counit of that
adjunction to be invertible *over the slice* of `𝒳` at each chart object `u_X W`.  This file
reads that hypothesis off the components of the counit, with no slice site left in the statement:

`AlgebraicGeometry.Space.chartSliceCounitIsIso_iff_forall_isIso_val_app` says it is **equivalent**
to invertibility of the component of the counit at every object of `𝒳` carrying a morphism to a
chart object.

The point of the reformulation is that the free half of the chart statement then applies
directly.  The counit is invertible on sections over every chart object, at every module and with
no hypothesis beyond `hunit`, by
`AlgebraicGeometry.Space.isIso_val_app_projectionPullbackCounit_chart`; and
`AlgebraicGeometry.Space.isIso_val_app_projectionPullbackCounit_of_iso_chart` extends that to every
object *isomorphic* to a chart object.  So of the objects of the slice quantified over above, those
isomorphic to a chart object are already done, and **the residue is exactly the components at the
objects of the chart slices that are not isomorphic to chart objects** — by Stacks 06W0 the slice
`𝒳/u_X W` is the big étale site of the scheme below `u_X W`, whose objects are arbitrary schemes
over it, while the chart objects in it are the ones whose structure morphism to `X` is étale.

## Nothing here is a new name for the residue

The residue already has a name: it is
`AlgebraicGeometry.Space.ProjectionPullbackCounitIsIso`, equivalently the object-level
`AlgebraicGeometry.Space.ProjectionPullbackEssImage`
(`AlgebraicGeometry.Space.projectionPullbackCounitIsIso_iff_essImage`), equivalently the
chart-local `AlgebraicGeometry.Space.ChartSliceCounitIsIso`
(`AlgebraicGeometry.Space.chartSliceCounitIsIso_iff`).  All three are the same Prop up to
`Iff`, and this file adds a fourth reading of it rather than a fifth hypothesis.

## The universe gap is closed; what is left is not a universe

What the source supplies at the objects of the slice that are not chart objects is Descent,
Section 03DR for the scheme below the chart, that is the essential-surjectivity half of Descent,
Proposition 03DX (1) at the big étale site.  In this development that half is a theorem — over
every base and at each of the five topologies, by `AlgebraicGeometry.BigFppfOver`
`.baseQuasicoherentIsEssImageAssociatedModule`, and *on the slice* `𝒳_τ/x` by
`AlgebraicGeometry.FibredSite.quasicoherentIsEssImageLocalizationAssociatedModuleKind` — **but
only at the module universe `u`**, and that cannot be changed: the functor `𝓕 ↦ 𝓕^a`,
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleQcoh`, has
`(CategoryTheory.SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory` as its source,
and `CategoryTheory.SheafOfModules.isQuasicoherent` is an
`CategoryTheory.ObjectProperty (SheafOfModules.{u₁, u₂, u₃, u₁} R)`: its module universe *is* the
universe of its sheaf of rings.

**The module universe of these statements is not forced above that `u`.**  Using `hunit` —
`AlgebraicGeometry.Space.isIso_unit_moduleRestriction`, whose adjoint-triple argument runs
against a direct image of sheaves of modules indexed by a comma category of the small étale site
of `X` — would force it above `u + 1`.  Instead these statements take invertibility of the unit
as a hypothesis, are stated at the module universe `max u m`, and so are available at `u`, where
`AlgebraicGeometry.Space`
`.isIso_unit_moduleRestriction'` discharges it.  So the two sides meet, and the map-level
consequence of 03DX on the slice,
`AlgebraicGeometry.FibredSite.isIso_of_isIso_val_app_localizationOpens`, is usable here.

What is still owed is therefore not a universe but a comparison of functors: the objects of the
chart slice `𝒳/u_X W` lying over the *opens* of the scheme `W` — the objects at which that
conservativity statement asks for invertibility — have to be identified with chart objects, so
that the free half settles them.  Upstairs the corresponding statement is in the tree,
`AlgebraicGeometry.Space.chartOpens`: a Zariski open of an étale chart of `X` is again an étale
chart of `X`.  What is missing is its comparison with
`AlgebraicGeometry.FibredSite.localizationEquivalence`, the Stacks 06W0 identification
`𝒳_étale/u_X W = (Sch/W)_étale`, whose functor has no formula on objects.

Note which notion of quasi-coherence does *not* obstruct: the modules this file quantifies over
are quasi-coherent in the sense of `CategoryTheory.SheafOfModules.IsQuasicoherentOnSite`
(Stacks 03DL (6)), through `AlgebraicGeometry.FibredSite.quasicoherentModules`, and that predicate
leaves the module universe free.  The obstruction is confined to the *source* of `𝓕 ↦ 𝓕^a`, the
quasi-coherent modules of the scheme itself.

## Main results

* `AlgebraicGeometry.Space.isIso_val_app_projectionPullbackCounit_of_iso_chart`: the counit is
  invertible on sections over every object isomorphic to a chart object, at every module and with
  no hypothesis beyond `hunit`.
* `AlgebraicGeometry.Space.chartSliceCounitIsIso_iff_forall_isIso_val_app`: the glueing hypothesis
  of Stacks 0GQD is invertibility of the counit's components at the objects of the chart slices.

## References

* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
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

/-! ### The free half, at the objects isomorphic to a chart object -/

/-- **The counit of `π_X^* ⊣ i_X^*` is invertible on sections over every object isomorphic to a
chart object**, at every `𝒪_𝒳`-module and with no quasi-coherence hypothesis.

`AlgebraicGeometry.Space.isIso_val_app_projectionPullbackCounit_chart` is the statement at the
chart objects themselves, and invertibility of a component depends only on the isomorphism class
of the object, by `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso_obj`.  This is
the form the free half is used in below: the objects of a chart slice are objects of `𝒳`, and the
ones among them that the free half settles are those isomorphic to a chart object, not only the
chart objects on the nose. -/
theorem isIso_val_app_projectionPullbackCounit_of_iso_chart
    (hunit : IsIso (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e).unit)
    (ℱ : SheafOfModules.{max u m}
      (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale))
    (W : SmallEtale B S hS X.1) {Z : 𝒳}
    (α : (restrictionFunctor B S hS X.1 p e).obj W ≅ Z) :
    IsIso (((projectionModulePullbackAdjunction.{u, v, w, m}
      B S hS X p hp e).counit.app
      ℱ).val.app (op Z)) :=
  Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso_obj _ α
    (isIso_val_app_projectionPullbackCounit_chart.{u, v, w, m} B S hS X p hp e hunit ℱ W)

/-! ### The glueing hypothesis, read on components -/

/-- **The glueing hypothesis of Stacks 0GQD is a condition on the components of the counit.**  The
counit of `π_X^* ⊣ i_X^*` is invertible over the slice of `𝒳` at every chart object if and only if
its component is invertible at every object of `𝒳` carrying a morphism to a chart object.

Both directions are the two readings of `CategoryTheory.SheafOfModules.overFunctor` as a
`CategoryTheory.SheafOfModules.pushforward`:
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward` for the forward
one and `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_over_of_isIso_val_app` for the
converse.

Read with
`AlgebraicGeometry.Space.isIso_val_app_projectionPullbackCounit_of_iso_chart`, which settles the
objects isomorphic to a chart object unconditionally, this locates the residue of Stacks 0GQD's
second input at the objects of the chart slices which are not isomorphic to chart objects; see the
module docstring for what the source supplies there and what the tree still owes. -/
theorem chartSliceCounitIsIso_iff_forall_isIso_val_app :
    ChartSliceCounitIsIso.{u, v, w, m} B S hS X p hp e ↔
      ∀ (M : FibredSite.quasicoherentModules.{u, v, w, max u m} B S hS p hp)
          (W : SmallEtale B S hS X.1)
          (Z : Over ((restrictionFunctor B S hS X.1 p e).obj W)),
        IsIso (((projectionModulePullbackAdjunction.{u, v, w, m}
          B S hS X p hp e).counit.app
          ((FibredSite.toSiteModules B S hS p hp SiteKind.etale).obj M)).val.app (op Z.left)) := by
  constructor
  · intro h M W Z
    exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward
      (𝟙 _) _ (h M W) (op Z)
  · intro h M W
    exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_over_of_isIso_val_app _ _ (h M W)

end AlgebraicGeometry.Space

end
