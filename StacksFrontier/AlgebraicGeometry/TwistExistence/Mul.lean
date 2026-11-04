module

public import StacksFrontier.AlgebraicGeometry.TwistExistence.Chart

/-!
# The chart comparison of two twist data is multiplicative

`StacksFrontier/AlgebraicGeometry/TwistExistence/Chart.lean` builds, for two sets of twist data
`D`, `E` on a relative Proj and an affine open `U` of the base, the comparison
`Stacks.AlgebraicGeometry.TwistExistence.cmp` of their glued homogeneous pieces over the inverse
image of `U`. This file proves that the comparison respects the products of the two glued graded
algebras.

The input is each datum's own `isGradedChartIso`, in the form
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.chartIso_mul`: the chart identification
carries the canonical product of absolute twist sections to the product of the glued algebra, in
every integer degree and on every open of the chart. **Nothing about Tag 01NO's transition
comparisons is used**, and in particular not their multiplicativity, which is what the glueing of
the twists themselves is blocked on.

## Main results

* `Stacks.AlgebraicGeometry.TwistExistence.mapSection_chartLoc`: the section comparison of a
  twist datum undoes its own chart identification — the bridge between
  `Stacks.AlgebraicGeometry.TwistExistence.chartLoc` and
  `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.mapSection`.
* `Stacks.AlgebraicGeometry.TwistExistence.chartLoc_mul`: **the chart identification of a twist
  datum carries the product of the glued algebra to the canonical product of absolute twist
  sections**, on the sections over every open inside the inverse image of the affine open.
* `Stacks.AlgebraicGeometry.TwistExistence.cmp_mul`: **the comparison of two twist data is
  multiplicative.**

## The route

`chartLoc` is the unit of the restriction--pushforward adjunction followed by the chart
identification, so composing it with `mapSection` — which is the *inverse* chart identification,
the identity isomorphism `restrictAppIso` costing nothing — cancels the identification and leaves
the restriction map of the unit. That is `mapSection_chartLoc`, and it is one cancellation.

With it, `chartLoc_mul` is the datum's `chartIso_mul` read backwards: both sides have the same
image under `mapSection`, which is injective, and the comparison of the two images is exactly the
compatibility of the glued product with restriction — the `naturality` field of the bilinear map.

Then `cmp_mul` needs no new input: each datum's `chartLoc` is multiplicative in that sense, and
`cmp` is characterised by being carried to the first datum's `chartLoc` by the second's.

## What is not done here

The comparisons over two different affine charts are still not compared, and nothing is glued. No
`stacks` attribute is attached.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistExistence

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- The chart identification of a twist datum, on the sections over an open inside the inverse
image of the affine open: the unit's restriction map followed by the identification itself. -/
public theorem chartLoc_app_eq (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece n).val.obj (op V)) :
    (chartLoc D U hU n).app V hV x =
      (D.chartData.chartIso U hU n).hom.val.app
        (op ((relativeProj A).chart U hU ⁻¹ᵁ V))
        ((D.algebra.piece n).val.map
          (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x) :=
  (chartLoc_app D U hU n V hV x).trans (chartPush_val_app D U hU n V x)

/-- **The section comparison of a twist datum undoes its own chart identification.** This is the
bridge between `Stacks.AlgebraicGeometry.TwistExistence.chartLoc` and
`Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.mapSection`. -/
public theorem mapSection_chartLoc (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece n).val.obj (op V)) :
    D.chartData.mapSection U hU n ((relativeProj A).chart U hU ⁻¹ᵁ V)
        ((chartLoc D U hU n).app V hV x) =
      (D.algebra.piece n).val.map
        (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x :=
  Eq.trans
    (congrArg
      (D.chartData.mapSection U hU n ((relativeProj A).chart U hU ⁻¹ᵁ V))
      (chartLoc_app_eq D U hU n V hV x))
    (TwistRigidity.iso_inv_app_hom_app (D.chartData.chartIso U hU n)
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) _)

/-- **The chart identification of a twist datum carries the product of its glued algebra to the
canonical product of absolute twist sections**, in every pair of integer degrees and on the
sections over every open inside the inverse image of the affine open. -/
public theorem chartLoc_mul (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (i j : ℤ)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece i).val.obj (op V)) (y : (D.algebra.piece j).val.obj (op V)) :
    (chartLoc D U hU (i + j)).app V hV ((D.algebra.mul i j).app (op V) x y) =
      absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V)
        ((chartLoc D U hU i).app V hV x) ((chartLoc D U hU j).app V hV y) := by
  refine TwistRigidity.mapSection_injective D.chartData U hU (i + j)
    ((relativeProj A).chart U hU ⁻¹ᵁ V) ?_
  refine Eq.trans (mapSection_chartLoc D U hU (i + j) V hV _) ?_
  refine Eq.trans ((D.algebra.mul i j).naturality
    (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x y) ?_
  refine Eq.trans ?_ (D.chartIso_mul U hU i j ((relativeProj A).chart U hU ⁻¹ᵁ V) _ _).symm
  exact TwistRigidity.mul_app_congr D.algebra i j _
    (mapSection_chartLoc D U hU i V hV x).symm (mapSection_chartLoc D U hU j V hV y).symm

/-- **The comparison of two twist data over one affine chart is multiplicative.** -/
public theorem cmp_mul (D E : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (i j : ℤ)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece i).val.obj (op V)) (y : (D.algebra.piece j).val.obj (op V)) :
    (cmp D E U hU (i + j)).app V hV ((D.algebra.mul i j).app (op V) x y) =
      (E.algebra.mul i j).app (op V)
        ((cmp D E U hU i).app V hV x) ((cmp D E U hU j).app V hV y) := by
  refine cmp_eq_of_chartLoc_eq D E U hU (i + j) V hV ?_
  refine Eq.trans (chartLoc_mul E U hU i j V hV _ _) ?_
  refine Eq.trans ?_ (chartLoc_mul D U hU i j V hV x y).symm
  exact congrArg₂ (absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V))
    (chartLoc_cmp D E U hU i V hV x) (chartLoc_cmp D E U hU j V hV y)

end Stacks.AlgebraicGeometry.TwistExistence

end
