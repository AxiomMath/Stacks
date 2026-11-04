module

public import StacksFrontier.AlgebraicGeometry.PsiCompat.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne

/-!
# The chart data of Tag 01NR's twist datum, for the glued twists

`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is the structure Tag 01NR asserts the
existence of. `Stacks.AlgebraicGeometry.Tag01NRPsiCompat.mk` reduces it to five fields: the glued
graded algebra `B`, its chart data, the condition that the chart identifications respect the
product and the unit, the homogeneous-section map, and that map's chart description.

**This file discharges the second of those five, relative to the first.** Once the homogeneous
pieces of `B` are the glued twists
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist`, the chart data of `B` needs no
further input: its two geometric fields are
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart` and `chart_image_top`, and
its chart identifications are `Stacks.Tag01VMVeryAmple.gluedChartIso` transported along the
identification of the pieces with the glued twists.

So a construction of the twists whose glued pieces are the glued twists owes, in place of the
five fields, the four that are *about the algebra structure* — the graded algebra itself (with
its pieces identified with the glued twists), the condition on its product and unit, the section
map and its chart description — together with the nested cocycle in every degree, which that
algebra's pieces already depend on.

## Main definitions

* `Stacks.AlgebraicGeometry.GluedTwistChartData.chartData`: **the chart data of a graded algebra
  on a relative Proj whose homogeneous pieces are the glued twists.**
* `Stacks.AlgebraicGeometry.GluedTwistChartData.mk`: **Tag 01NR's twist datum from four fields**,
  for such an algebra.

## What is not done here

**No `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is constructed**, and no field of one
is discharged outright: both definitions below take the glued graded algebra as a hypothesis, and
no graded algebra on a relative Proj with the glued twists as its pieces exists in either tree —
neither the multiplication nor the unit of one is constructed anywhere.

Both are also conditional on `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle A n`
in *every* integer degree, which is Stacks Tag 01MZ's third assertion for the restriction maps of
`A` and is proved here only in degree one
(`Stacks.AlgebraicGeometry.ChartCocycleRigidity.isNestedCocycle_one`). The glued
twist `gluedTwist A n hcoc` does not exist without it, so the hypothesis is not an artefact of
this file: it is the hypothesis of the object the chart data is about.

No `stacks` attribute is attached. Tag 01NR's existence assertion is earned only by a term of
`TwistData`; a reduction of one of its five remaining fields to another of them is not a covering
set for it.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.GluedTwistChartData

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- **The chart data of a graded algebra on a relative Proj whose homogeneous pieces are the
glued twists.** This is the `chartData` field of Tag 01NR's twist datum, for any such algebra: the
chart over an affine open of the base is an open immersion with image the inverse image of that
affine open, and the restriction of the `n`-th piece along it is the absolute twist `𝒪(n)` of the
projective spectrum of the graded ring of sections, by
`Stacks.Tag01VMVeryAmple.gluedChartIso`. -/
public def chartData (hcoc : ∀ n : ℤ, IsNestedCocycle A n)
    (B : SchemeGradedAlgebra (relativeProj A).scheme)
    (e : ∀ n : ℤ, B.piece n ≅ gluedTwist A n (hcoc n)) : ChartData A B :=
  RelativeProjTwistGlue.chartData B fun U hU n =>
    (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).mapIso (e n) ≪≫
      Tag01VMVeryAmple.gluedChartIso A n (hcoc n) U hU

/-- **Tag 01NR's twist datum for a graded algebra whose pieces are the glued twists.** Of the
five fields `Stacks.AlgebraicGeometry.Tag01NRPsiCompat.mk` asks for, the chart data is no longer
among them: it is `Stacks.AlgebraicGeometry.GluedTwistChartData.chartData`.

What remains is the algebra `B` together with the identification `e` of its pieces with the glued
twists, the condition that its product and unit agree on the charts with those of the absolute
twists, the homogeneous-section map, and that map's chart description. -/
public def mk (hcoc : ∀ n : ℤ, IsNestedCocycle A n)
    (B : SchemeGradedAlgebra (relativeProj A).scheme)
    (e : ∀ n : ℤ, B.piece n ≅ gluedTwist A n (hcoc n))
    (hD : IsGradedChartIso (chartData hcoc B e))
    (psi : ∀ n : ℕ, A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj (B.piece (n : ℤ)))
    (hpsi : Tag01NRPsiCompat.PsiChart (chartData hcoc B e) psi) : TwistData A :=
  Tag01NRPsiCompat.mk B (chartData hcoc B e) hD psi hpsi

end Stacks.AlgebraicGeometry.GluedTwistChartData

end
