module

public import StacksFrontier.AlgebraicGeometry.ChartCocycleRigidity.Generic
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeTwistRigidity.Basic

/-!
# The chart cocycle of a relative projective spectrum as a rigidity statement

For a chain `W ⊆ W' ⊆ U` of affine opens of the base, the chart cocycle
`Stacks.AlgebraicGeometry.NestedCocycleTail.IsChartCocycle` asserts that the comparison
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.restrictTwistIso` of twists for the outer pair is
the composite of the two comparisons through the chart of `W'`, on sections over every open and for
every inclusion of opens.

This file defines the endomorphism family `cocycleEndo` of the twists on the chart of `W`, the
outer comparison cancelled against the composite of the two comparisons through the chart of
`W'`, and shows that the chart cocycle holds as soon as this family is the identity in every
integer degree. It also states two assertions about a single inclusion of affine opens:

* `IsLegMultiplicative`: the comparison respects the canonical product of absolute twist
  sections, on every open of the smaller chart and in all integer degrees.
* `IsLegDegreeSection`: the comparison carries the restricted homogeneous global section of a
  homogeneous element to the homogeneous global section of the restricted element.

## Main definitions

* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.chainIncl`: the identification of the two
  readings of the image, in the chart of `U`, of an open of the chart of `W`.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.cocycleEndo`: the endomorphism family of the
  twists on the chart of `W` whose being the identity gives the chart cocycle.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.IsLegMultiplicative` and `IsLegDegreeSection`:
  the two single-inclusion assertions.

## Main results

* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.cocycleEndo_eq`: `cocycleEndo` is the generic
  `legEndo`, as an equation of morphisms.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.res_res_subtype`: restriction of homogeneous
  elements along a chain of opens composes.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.isChartCocycle_of_cocycleEndo_eq_id` and
  `isNestedCocycle_of_cocycleEndo_eq_id`: the chart cocycle, and hence
  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle`, follow from `cocycleEndo`
  being the identity.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.NestedCocycleReduction
open Stacks.AlgebraicGeometry.NestedCocycleTail
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.ChartCocycleRigidity

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### The two per-leg assertions -/

section Legs

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- The comparison `restrictTwistIso` of twists for an inclusion `W ⊆ U` of affine opens respects
the canonical product of absolute twist sections, over every open of the chart of `W` and in all
integer degrees. -/
public def IsLegMultiplicative (W U : S.Opens) (h : W ≤ U) (hW : IsAffineOpen W)
    (hU : IsAffineOpen U) : Prop :=
  ∀ (i j : ℤ) (T : (AlgebraicGeometry.Proj (A.grading W)).Opens)
    (a : (twistingSheaf (A.grading U) i).val.obj
      (op (projInclusionMap A W U h hW hU ''ᵁ T)))
    (b : (twistingSheaf (A.grading U) j).val.obj
      (op (projInclusionMap A W U h hW hU ''ᵁ T))),
    (restrictTwistIso A W U h hW hU (i + j)).hom.val.app (op T)
        (absoluteTwistProduct (A.grading U) i j
          (projInclusionMap A W U h hW hU ''ᵁ T) a b) =
      absoluteTwistProduct (A.grading W) i j T
        ((restrictTwistIso A W U h hW hU i).hom.val.app (op T) a)
        ((restrictTwistIso A W U h hW hU j).hom.val.app (op T) b)

/-- The comparison `restrictTwistIso` of twists for an inclusion `W ⊆ U` of affine opens carries
the restricted homogeneous global section of a homogeneous element of degree `k` to the
homogeneous global section of its restriction. -/
public def IsLegDegreeSection (W U : S.Opens) (h : W ≤ U) (hW : IsAffineOpen W)
    (hU : IsAffineOpen U) : Prop :=
  ∀ (k : ℕ) (c : (A.grading U) k),
    (restrictTwistIso A W U h hW hU (k : ℤ)).hom.val.app (op ⊤)
        ((twistingSheaf (A.grading U) (k : ℤ)).val.map (homOfLE le_top).op
          (degreeSection (A.grading U) k c)) =
      degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩

/-- Restriction of homogeneous elements of degree `k` along a chain `W ≤ W' ≤ U` of opens
composes: restricting from `U` to `W'` and then to `W` agrees with restricting from `U` to `W`. -/
public theorem res_res_subtype (W W' U : S.Opens) (hWW' : W ≤ W') (hW'U : W' ≤ U)
    (hWU : W ≤ U) (k : ℕ) (c : (A.grading U) k) :
    (⟨A.res hWW' (A.res hW'U c), (A.res hWW').map_mem ((A.res hW'U).map_mem c.2)⟩ :
        (A.grading W) k) = ⟨A.res hWU c, (A.res hWU).map_mem c.2⟩ := by
  apply Subtype.ext
  show (A.resRingHom hWW') ((A.resRingHom hW'U) (c : A.sectionRing U)) =
    (A.resRingHom (hWW'.trans hW'U)) (c : A.sectionRing U)
  rw [A.resRingHom_comp hWW' hW'U]
  rfl

end Legs

/-! ### The endomorphism whose being the identity is the cocycle -/

section Chain

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W W' U : S.Opens) (hWW' : W ≤ W')
  (hW'U : W' ≤ U) (hWU : W ≤ U) (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
  (hU : IsAffineOpen U)

/-- The inclusion of opens identifying the two readings of the image, in the chart of `U`, of an
open of the chart of `W`: directly, and through the chart of `W'`. -/
public def chainIncl (T : (AlgebraicGeometry.Proj (A.grading W)).Opens) :
    projInclusionMap A W' U hW'U hW' hU ''ᵁ
        (projInclusionMap A W W' hWW' hW hW' ''ᵁ T) ⟶
      projInclusionMap A W U hWU hW hU ''ᵁ T :=
  eqToHom (image_eq_image_image (projInclusionMap A W W' hWW' hW hW')
    (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
    (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU) T)

/-- The endomorphism of the degree-`n` twist on the chart of `W` given by the comparison
`restrictTwistIso` for the outer pair `W ⊆ U`, cancelled against the composite of the two
comparisons through the chart of `W'`. -/
public def cocycleEndo (n : ℤ) :
    twistingSheaf (A.grading W) n ⟶ twistingSheaf (A.grading W) n :=
  legEndo (projInclusionMap A W W' hWW' hW hW') (projInclusionMap A W' U hW'U hW' hU)
    (projInclusionMap A W U hWU hW hU)
    (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
    (restrictTwistIso A W' U hW'U hW' hU n) (restrictTwistIso A W W' hWW' hW hW' n)
    (restrictTwistIso A W U hWU hW hU n)

/-- `cocycleEndo` is the generic `legEndo` applied to the three comparisons, as an equation of
morphisms. -/
public theorem cocycleEndo_eq (n : ℤ) :
    cocycleEndo A W W' U hWW' hW'U hWU hW hW' hU n =
      legEndo (projInclusionMap A W W' hWW' hW hW')
        (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
        (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
        (restrictTwistIso A W' U hW'U hW' hU n) (restrictTwistIso A W W' hWW' hW hW' n)
        (restrictTwistIso A W U hWU hW hU n) :=
  rfl

end Chain

/-! ### The reduction -/

section Reduction

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- If `cocycleEndo` is the identity for every chain of affine opens and in every integer degree,
then the chart cocycle `IsChartCocycle A` holds: the comparison for the outer pair of a chain of
affine opens is the composite of the two comparisons through the middle chart. -/
public theorem isChartCocycle_of_cocycleEndo_eq_id
    (hid : ∀ (W W' U : S.Opens) (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U)
      (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hU : IsAffineOpen U) (n : ℤ),
      cocycleEndo A W W' U hWW' hW'U hWU hW hW' hU n =
        𝟙 (twistingSheaf (A.grading W) n)) :
    IsChartCocycle A := fun W W' U hWW' hW'U hWU hW hW' hU n _ _ _ i₁ j₂ j₃ =>
  isEvalComposite_of_legEndo_eq_id (projInclusionMap A W W' hWW' hW hW')
    (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
    (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
    (restrictTwistIso A W' U hW'U hW' hU n) (restrictTwistIso A W W' hWW' hW hW' n)
    (restrictTwistIso A W U hWU hW hU n)
    (hid W W' U hWW' hW'U hWU hW hW' hU n) i₁ j₂ j₃

/-- If `cocycleEndo` is the identity for every chain of affine opens and in every integer degree,
then the nested cocycle `IsNestedCocycle A n` holds in every degree `n`. -/
public theorem isNestedCocycle_of_cocycleEndo_eq_id
    (hid : ∀ (W W' U : S.Opens) (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U)
      (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hU : IsAffineOpen U) (n : ℤ),
      cocycleEndo A W W' U hWW' hW'U hWU hW hW' hU n =
        𝟙 (twistingSheaf (A.grading W) n))
    (n : ℤ) :
    IsNestedCocycle A n :=
  isNestedCocycle_of_isChartCocycle A (isChartCocycle_of_cocycleEndo_eq_id A hid) n

end Reduction

end Stacks.AlgebraicGeometry.ChartCocycleRigidity

end
