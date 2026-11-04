module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction

/-!
# Comparing the two parallel restrictions of a module to an étale chart

This development restricts an `𝒪_X`-module to an étale scheme chart `U` of an algebraic space
twice over.  `AlgebraicGeometry.Space.restrictToChart` sheafifies the sections along
`AlgebraicGeometry.Space.chartOpens`, and
`AlgebraicGeometry.Space.restrictToChartScheme` sheafifies them along
`AlgebraicGeometry.Space.openChartFunctor`.  The two functors send a Zariski open of the chart
scheme to the same open subscheme, read as an étale chart of `X` in two ways: through
`AlgebraicGeometry.Space.chartOpenOverι`, which is the open inclusion made a morphism of the
site with `CategoryTheory.ObjectProperty.homMk`, and through
`AlgebraicGeometry.Space.openSubHom`, which is the same inclusion made a morphism of the site
with the fullness inverse `CategoryTheory.Functor.preimage`.  This file identifies what the two
readings share.

## Main results

* `AlgebraicGeometry.Space.homMk_opens_ι_eq_preimage`: the two readings of the inclusion of a
  Zariski open as a morphism of `Sch_κ` agree.
* `AlgebraicGeometry.Space.chartOpenOver_eq_openSub`: consequently the two readings of a
  Zariski open of a chart as an object of the big fppf category over `S` agree.
* `AlgebraicGeometry.Space.chartRestrictionRingHom_eq`: the two change-of-scalars maps along
  which the two restrictions extend scalars are *equal*, by `rfl`.

## Implementation notes

The two restrictions are not definitionally equal, and the obstruction is exactly the use of
`CategoryTheory.Functor.preimage`: it is a choice of preimage under a fully faithful functor,
so it is opaque, and `with_unfolding_all rfl` on the two restrictions fails on it.  What
`AlgebraicGeometry.Space.chartRestrictionRingHom_eq` records is that the obstruction does not
reach the coefficients: the structure sheaf of the small étale site evaluated at a chart sees
only the underlying scheme of that chart, which the two readings share definitionally, so the
semilinearity data of the two restrictions is one and the same map.  Only the sections of the
module differ, and they differ by evaluating the module at two objects of the small étale site
which `AlgebraicGeometry.Space.chartOpenOver_eq_openSub` shows to be equal.

What remains for an isomorphism of the two restrictions is the equality of the two index
functors, `CategoryTheory.Functor.ext` over the identification of objects recorded here
together with the matching of the two inclusions `AlgebraicGeometry.Space.chartOpenOverι` and
`AlgebraicGeometry.Space.openSubHom` as morphisms *over* `S`.  The obstruction is not that the
two functors disagree on objects: the underlying objects of the site do agree, by
`AlgebraicGeometry.Space.chartOpenOver_eq_openSub`.  That is carried out in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionReadingsFunctor.lean`, which builds the
isomorphism of the two restrictions on top of this file.

`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionReadingsIso.lean` settles it, and without
the transport: since the two objects of the site agree, the identity of the common underlying
scheme is a morphism of the two charts in both directions, and
`AlgebraicGeometry.Space.chartOpensIsoOpenChartFunctor` assembles those into an isomorphism of
the two index functors — an isomorphism, not the equality described above, which is all the
comparison of the two restrictions needs.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The inclusion of a Zariski open of the scheme underlying an object of the big fppf site,
read as a morphism of `Sch_κ` with `CategoryTheory.ObjectProperty.homMk`, is its reading
through the fullness inverse of the inclusion of `Sch_κ` into all schemes. -/
theorem homMk_opens_ι_eq_preimage (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    (ObjectProperty.homMk O.ι :
        (⟨(O : Scheme), lt_of_le_of_lt (Scheme.size_coe_opens_le _ O) A.left.property⟩ :
          B.Schemes) ⟶ A.left) =
      B.inclusion.preimage
        (show B.inclusion.obj
            ⟨(O : Scheme), lt_of_le_of_lt (Scheme.size_coe_opens_le _ O) A.left.property⟩ ⟶
          B.inclusion.obj A.left from O.ι) := by
  apply B.inclusion.map_injective
  rw [Functor.map_preimage]
  rfl

/-- The two readings of a Zariski open of an étale chart as an object of the big fppf category
over `S` agree: the one of `AlgebraicGeometry.Space.chartOpenOver`, used by
`AlgebraicGeometry.Space.restrictToChart`, and the one of
`AlgebraicGeometry.Space.openSub`, used by `AlgebraicGeometry.Space.restrictToChartScheme`. -/
theorem chartOpenOver_eq_openSub (U : SmallEtale B S hS X)
    (O : (etaleChartScheme B S hS U).Opens) :
    chartOpenOver B S hS U O = openSub ((SmallEtale.toOver B S hS X).obj U) O :=
  congrArg (fun k ↦ Over.mk k)
    (congrArg (fun k ↦ k ≫ ((SmallEtale.toOver B S hS X).obj U).hom)
      (homMk_opens_ι_eq_preimage B S hS ((SmallEtale.toOver B S hS X).obj U) O))

/-- The change-of-scalars map along which `AlgebraicGeometry.Space.restrictToChart` extends
scalars is the one along which `AlgebraicGeometry.Space.restrictToChartScheme` extends them.

The structure sheaf of the small étale site evaluated at a chart depends only on the underlying
scheme of the chart, which the two readings of a Zariski open of the chart share
definitionally; so the two maps are literally the same map. -/
theorem chartRestrictionRingHom_eq (U : SmallEtale B S hS X) :
    chartRestrictionRingHom B S hS hX U = chartSchemeRestrictionRingHom B S hS X U :=
  rfl

end AlgebraicGeometry.Space

end
