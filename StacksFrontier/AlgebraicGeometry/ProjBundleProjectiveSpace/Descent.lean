module

public import StacksFrontier.AlgebraicGeometry.LimitApproxFunctor.Stage
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.Generic
public import StacksFrontier.AlgebraicGeometry.RelativeProjGlue.Basic

/-!
# The relative homogeneous spectrum is determined by its charts

Tag 01NQ glues the absolute `Proj Γ(U, 𝒜)` over the affine opens `U` of a base scheme `S` into
`Proj_S(𝒜) ⟶ S`; `Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProjToBase` is that glued
scheme over `S`. This file proves the **uniqueness** half: a scheme `Y ⟶ S` carrying the same
charts, cartesianly over the affine opens and compatibly with the transitions, is canonically
isomorphic to `Proj_S(𝒜)` over `S`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily`: the data of such a chart family on
  a scheme over `S`.
* `Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily.desc`: the induced morphism
  `Proj_S(𝒜) ⟶ Y`, obtained from the universal property of the colimit.
* `Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily.iso`: that morphism as an
  isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily.isIso_desc`: **the comparison is an
  isomorphism.**
* `Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily.iso_hom_comp`: it is an isomorphism
  over `S`.
* `Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily.chart_iso_hom`: it carries the chart
  of `Proj_S(𝒜)` over an affine open to the given chart of `Y`.

## Implementation notes

**Why the compatibility asked for is only along the arrows of the site.** `Proj_S(𝒜)` is the
*colimit* of the chart functor on `S.AffineZariskiSite`
(`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.glued` is `CategoryTheory.Limits.colimit`),
so a morphism out of it is exactly a cocone, and a cocone over a thin index category is a family
of morphisms compatible with the arrows. No cocycle condition on intersections appears, which is
what makes this cheap: the hard gluing was already done in building the colimit.

**Why the comparison is an isomorphism.** Being an isomorphism is Zariski-local on the target,
in the form
`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_of_isPullback_cover`. The cover of `Y` is by the
inverse images of the affine opens of `S`, which cover because the affine opens cover `S`; over
the inverse image of `U` the comparison is pulled back to the identity of `Proj Γ(U, 𝒜)`,
because both the chart of `Proj_S(𝒜)` and the chart of `Y` are cartesian over `U` and the
comparison commutes with them. The square with the identity on one side is obtained from the two
cartesian squares by `CategoryTheory.IsPullback.of_bot`.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)

## Not done here

No project tag is attached. Tag 01NQ's assertion is the *existence* of the glued datum, which is
already available as `Stacks.AlgebraicGeometry.RelativeProj.relativeProj` and tagged there;
uniqueness is not registered against a tag here.

Nothing here identifies any particular `Y` with a relative `Proj`; this file only supplies the
comparison once the charts are given.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue

namespace Stacks.AlgebraicGeometry.RelativeProjDescent

universe u

variable {S : Scheme.{u}} (𝒜 : GradedAlgebra S)

/-- **A chart family on a scheme over the base**: for every affine open `U` of `S` a morphism
from the absolute `Proj Γ(U, 𝒜)`, cartesian over the inclusion of `U`, and compatible with the
transition morphisms of the chart functor.

These are exactly the three conditions
`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData` records for the glued scheme, so a
`ChartFamily` is the same data as a `RelativeProjData` whose scheme and structure morphism are
`Y` and `p`. -/
public structure ChartFamily (Y : Scheme.{u}) (p : Y ⟶ S) where
  /-- The chart over an affine open of the base. -/
  chart (U : S.AffineZariskiSite) : 𝒜.projOver U ⟶ Y
  /-- Each chart is the inverse image of its affine open. -/
  isPullback (U : S.AffineZariskiSite) :
    IsPullback (𝒜.toOpen U) (chart U) U.toOpens.ι p
  /-- The charts are compatible with the transition morphisms. -/
  transition {U V : S.AffineZariskiSite} (φ : U ⟶ V) :
    (chartFunctor 𝒜).map φ ≫ chart V = chart U

/-- The inverse images of the affine opens of the base cover any scheme over the base. -/
public theorem iSup_preimage_eq_top {Y : Scheme.{u}} (p : Y ⟶ S) :
    ⨆ U : S.AffineZariskiSite, p ⁻¹ᵁ U.toOpens = (⊤ : Y.Opens) := by
  have h : (⨆ U : S.AffineZariskiSite, U.toOpens) = (⊤ : S.Opens) := by
    simpa using (Scheme.AffineZariskiSite.directedCover S).iSup_opensRange
  have h2 : p ⁻¹ᵁ (⨆ U : S.AffineZariskiSite, U.toOpens)
      = ⨆ U : S.AffineZariskiSite, p ⁻¹ᵁ U.toOpens :=
    TopologicalSpace.Opens.map_iSup _ _
  rw [← h2, h]
  simp

namespace ChartFamily

variable {𝒜} {Y : Scheme.{u}} {p : Y ⟶ S} (c : ChartFamily 𝒜 Y p)

/-- The chart family read as a cocone on the chart functor. -/
public def cocone : Cocone (relativeGluingData 𝒜).functor where
  pt := Y
  ι :=
    { app := c.chart
      naturality := fun {_U _V} φ =>
        (c.transition φ).trans (Category.comp_id (c.chart _U)).symm }

/-- **The comparison morphism `Proj_S(𝒜) ⟶ Y`**, from the universal property of the colimit. -/
public def desc : relativeProj 𝒜 ⟶ Y :=
  colimit.desc _ c.cocone

/-- The comparison morphism carries the chart over an affine open to the given chart. -/
@[reassoc (attr := simp)]
public theorem chart_desc (U : S.AffineZariskiSite) :
    RelativeProjGlue.chart 𝒜 U ≫ c.desc = c.chart U :=
  colimit.ι_desc c.cocone U

/-- On the chart over an affine open, the comparison morphism is a morphism over the base. -/
public theorem chart_desc_comp (U : S.AffineZariskiSite) :
    RelativeProjGlue.chart 𝒜 U ≫ c.desc ≫ p
      = RelativeProjGlue.chart 𝒜 U ≫ relativeProjToBase 𝒜 := by
  rw [← Category.assoc, c.chart_desc, chart_relativeProjToBase, ← 𝒜.toOpen_ι U]
  exact ((c.isPullback U).w).symm

/-- The comparison morphism is a morphism over the base. -/
public theorem desc_comp : c.desc ≫ p = relativeProjToBase 𝒜 :=
  colimit.hom_ext fun U => (Category.assoc _ _ _).trans (c.chart_desc_comp U)

/-- Each chart of `Y` is an open immersion, being a base change of the inclusion of an affine
open. -/
public theorem isOpenImmersion_chart (U : S.AffineZariskiSite) :
    IsOpenImmersion (c.chart U) :=
  MorphismProperty.of_isPullback (c.isPullback U) inferInstance

/-- The range of the chart of `Y` over an affine open is the inverse image of that open. -/
public theorem range_chart (U : S.AffineZariskiSite) :
    Set.range (c.chart U).base = (p ⁻¹ᵁ U.toOpens : Set Y) := by
  have : IsOpenImmersion (c.chart U) := c.isOpenImmersion_chart U
  have h := AlgebraicGeometry.preimage_opensRange_of_isPullback (c.isPullback U).flip
  rw [Scheme.Opens.opensRange_ι] at h
  exact congrArg (fun V : Y.Opens => (V : Set Y)) h.symm

/-- Over the inverse image of an affine open, the comparison is the identity: the square formed
by the two charts, the comparison and the identity is cartesian. -/
public theorem isPullback_chart_desc (U : S.AffineZariskiSite) :
    IsPullback (RelativeProjGlue.chart 𝒜 U) (𝟙 (𝒜.projOver U)) c.desc (c.chart U) := by
  refine IsPullback.of_bot ?_ (by simp) (c.isPullback U).flip
  rw [Category.id_comp, c.desc_comp]
  exact (isPullback_chart 𝒜 U).flip

/-- **The comparison morphism is an isomorphism.** -/
public instance isIso_desc : IsIso c.desc := by
  refine Stacks.AlgebraicGeometry.ProjBaseChange.isIso_of_isPullback_cover c.desc
    (fun U : S.AffineZariskiSite => p ⁻¹ᵁ U.toOpens) (iSup_preimage_eq_top p)
    (fun U => 𝒜.projOver U) c.chart c.isOpenImmersion_chart c.range_chart
    (fun U => 𝒜.projOver U) (fun U => RelativeProjGlue.chart 𝒜 U) (fun _ => 𝟙 _)
    c.isPullback_chart_desc (fun _ => inferInstance)

/-- **A scheme over the base carrying a chart family is the relative homogeneous spectrum.** -/
public def iso : relativeProj 𝒜 ≅ Y :=
  asIso c.desc

/-- The isomorphism is an isomorphism over the base. -/
public theorem iso_hom_comp : c.iso.hom ≫ p = relativeProjToBase 𝒜 :=
  c.desc_comp

/-- The isomorphism carries each chart of `Proj_S(𝒜)` to the given chart of `Y`. -/
public theorem chart_iso_hom (U : S.AffineZariskiSite) :
    RelativeProjGlue.chart 𝒜 U ≫ c.iso.hom = c.chart U :=
  c.chart_desc U

end ChartFamily

end Stacks.AlgebraicGeometry.RelativeProjDescent

end
