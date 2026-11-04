module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.RelativeProj
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Local
public import StacksFrontier.AlgebraicGeometry.TwistUnique.Basic

/-!
# The comparison of two twist data over one affine chart

Tag 01NR's first uniqueness assertion is an `∃!`, and its uniqueness half is proved in
`StacksFrontier/AlgebraicGeometry/TwistUnique/Basic.lean`: what remains of the assertion is the
bare existence, for every two sets of twist data `D`, `E` on a relative Proj, of one isomorphism
of their glued graded algebras commuting with the homogeneous-section maps
(`Stacks.AlgebraicGeometry.TwistUnique.isUniqueTwistData_of_exists`).

This file builds that isomorphism **over a single affine chart**, where it is no more than the
two data's own chart identifications cancelled against each other. Nothing about Tag 01NO's
transition comparisons is used, and in particular nothing about their multiplicativity, which is
the statement the glueing of the twists themselves is blocked on
(`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle`).

## Main definitions

* `Stacks.AlgebraicGeometry.TwistExistence.chartPush`: the homogeneous piece of a twist datum's
  algebra, compared with the direct image of the absolute twist along the chart. This is the unit
  of the restriction--pushforward adjunction followed by the datum's own chart identification.
* `Stacks.AlgebraicGeometry.TwistExistence.chartLoc`: that comparison read as a
  `TopCat.Sheaf.LocalModuleEquiv` over the inverse image of the affine open.
* `Stacks.AlgebraicGeometry.TwistExistence.cmp`: **the comparison of two twist data over one
  affine chart**, the first datum's identification followed by the inverse of the second's.

## Main results

* `Stacks.AlgebraicGeometry.TwistExistence.isIso_app_chartPush`: the comparison is an isomorphism
  on the sections over every open inside the inverse image of the affine open. Only the unit
  factor has to be checked, and there it is a restriction map between two opens which are equal.
* `Stacks.AlgebraicGeometry.TwistExistence.chartLoc_cmp`: **the characterisation of `cmp`** — it
  is the unique map carried to the first datum's identification by the second's.

## The route

The unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` at a sheaf of modules `M` has,
over an open `V`, the component `M.presheaf.map (homOfLE (f.image_preimage_le V)).op`
(`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`, an `rfl`). For `V` inside
the image of the open immersion `f` the two opens `f ''ᵁ f ⁻¹ᵁ V` and `V` are **equal**
(`Stacks.AlgebraicGeometry.TwistUnique.image_preimage_eq_self`), so that component is an
isomorphism; the image of the chart over an affine open of the base is the inverse image of that
open, by `Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top`. The second factor is
the pushforward of an isomorphism and so an isomorphism outright.

Both comparisons land in the *same* object — the direct image of the absolute twist on the chart
— so no transition morphism and no further identification is needed to cancel them:
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.modelPair` is exactly the cancellation.

## What is not done here

The comparisons over two different affine charts are not compared, so nothing here glues and no
isomorphism of the glued algebras is produced. Neither the multiplicativity of `cmp` nor its
compatibility with the homogeneous-section maps is proved here. No `stacks` attribute is
attached: nothing in this file is a complete covering set for any label of Tag 01NR.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
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

/-- **The homogeneous piece of a twist datum's algebra, compared with the direct image of the
absolute twist along an affine chart.** The unit of the restriction--pushforward adjunction,
followed by the pushforward of the datum's own chart identification. -/
public def chartPush (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ) :
    D.algebra.piece n ⟶
      (Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
        (twistingSheaf (A.grading U) n) :=
  (Scheme.Modules.restrictAdjunction ((relativeProj A).chart U hU)).unit.app
      (D.algebra.piece n) ≫
    (Scheme.Modules.pushforward ((relativeProj A).chart U hU)).map
      (D.chartData.chartIso U hU n).hom

/-- **The chart comparison on sections, factored.** Over an open `V` of the relative Proj it is
the restriction map of the adjunction unit — the restriction from `V` to the image of its
preimage in the chart — followed by the datum's own chart identification on the sections over
that preimage. -/
public theorem chartPush_val_app (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (relativeProj A).scheme.Opens) (x : (D.algebra.piece n).val.obj (op V)) :
    (chartPush D U hU n).val.app (op V) x =
      (D.chartData.chartIso U hU n).hom.val.app
        (op ((relativeProj A).chart U hU ⁻¹ᵁ V))
        ((D.algebra.piece n).val.map
          (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x) :=
  rfl

/-- **The comparison is bijective on the sections over every open inside the inverse image of the
affine open.** Its two factors are: a restriction map between two opens which are *equal* there,
hence invertible by the reverse restriction map; and an isomorphism of sheaves of modules, which
cancels on sections. -/
public theorem bijective_chartPush (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U) :
    Function.Bijective ((chartPush D U hU n).val.app (op V)).hom := by
  have heq : ((relativeProj A).chart U hU) ''ᵁ (((relativeProj A).chart U hU) ⁻¹ᵁ V) = V :=
    TwistUnique.image_preimage_eq_self ((relativeProj A).chart U hU)
      (hV.trans (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).ge)
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun a => (D.algebra.piece n).val.map (homOfLE heq.ge).op
      ((D.chartData.chartIso U hU n).inv.val.app
        (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) a), fun x => ?_, fun a => ?_⟩
  · beta_reduce
    rw [chartPush_val_app]
    erw [TwistRigidity.iso_inv_app_hom_app]
    exact PresheafOfModules.map_map_eq_self (D.algebra.piece n).val _ _ x
  · beta_reduce
    refine (chartPush_val_app D U hU n V _).trans ?_
    erw [PresheafOfModules.map_map_eq_self (D.algebra.piece n).val]
    exact TwistRigidity.iso_hom_app_inv_app (D.chartData.chartIso U hU n) _ a

/-- **The chart identification of a twist datum, as a local isomorphism.** Over every open of the
relative Proj inside the inverse image of the affine open, an isomorphism of modules over the
sections of the structure sheaf there between the sections of the glued homogeneous piece and
those of the direct image of the absolute twist. -/
public def chartLoc (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ) :
    TopCat.Sheaf.LocalModuleEquiv (D.algebra.piece n).val
      (ChartTransNonNested.pushforwardVal ((relativeProj A).chart U hU)
        (twistingSheaf (A.grading U) n))
      ((relativeProj A).toBase ⁻¹ᵁ U) :=
  ChartTransRelativeProj.localModuleEquivOfBijective (chartPush D U hU n).val
    ((relativeProj A).toBase ⁻¹ᵁ U) (bijective_chartPush D U hU n)

@[simp]
public theorem chartLoc_app (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece n).val.obj (op V)) :
    (chartLoc D U hU n).app V hV x = (chartPush D U hU n).val.app (op V) x :=
  ChartTransRelativeProj.localModuleEquivOfBijective_app _ _ _ V hV x

/-- **The comparison of two twist data over one affine chart.** The first datum's chart
identification followed by the inverse of the second's — both land in the direct image of the
same absolute twist, so the cancellation needs nothing else. -/
public def cmp (D E : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ) :
    TopCat.Sheaf.LocalModuleEquiv (D.algebra.piece n).val (E.algebra.piece n).val
      ((relativeProj A).toBase ⁻¹ᵁ U) :=
  ChartTransRelativeProj.modelPair (chartLoc D U hU n) (chartLoc E U hU n)

/-- **The characterisation of the chart comparison.** The second datum's chart identification
carries the comparison to the first datum's. This is the only property of `cmp` used below; it
determines `cmp` because the second identification is an isomorphism. -/
public theorem chartLoc_cmp (D E : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece n).val.obj (op V)) :
    (chartLoc E U hU n).app V hV ((cmp D E U hU n).app V hV x) =
      (chartLoc D U hU n).app V hV x :=
  (congrArg ((chartLoc E U hU n).app V hV)
      (ChartTransRelativeProj.modelPair_app (chartLoc D U hU n) (chartLoc E U hU n) V hV x)).trans
    (LinearEquiv.apply_symm_apply ((chartLoc E U hU n).app V hV) _)

/-- The comparison is determined by the characterisation: any section carried by the second
datum's identification to the image of a given one under the first is the image of that one. -/
public theorem cmp_eq_of_chartLoc_eq (D E : TwistData A) (U : S.Opens) (hU : IsAffineOpen U)
    (n : ℤ) (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    {x : (D.algebra.piece n).val.obj (op V)} {y : (E.algebra.piece n).val.obj (op V)}
    (hxy : (chartLoc E U hU n).app V hV y = (chartLoc D U hU n).app V hV x) :
    (cmp D E U hU n).app V hV x = y :=
  ((chartLoc E U hU n).app V hV).injective ((chartLoc_cmp D E U hU n V hV x).trans hxy.symm)

end Stacks.AlgebraicGeometry.TwistExistence

end
