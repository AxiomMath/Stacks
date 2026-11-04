/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.BaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.TwistingModule
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSubfunctorRepresentedProper
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport

/-!
# The reduction of Stacks 0DPB to affine bases

Let `F/X/B` be a Quot situation with a projective frame `X = B × ℙⁿ_ℤ`, `F` of finite type, and
`𝓛` the pullback of `𝒪(1)`.  `Quot^{P, 𝓛}_{F/X/B}` is an algebraic space proper over `B` as soon
as, for every framed situation over an affine scheme `W`, `Quot^{P, 𝓛}` is represented by a scheme
proper over `W` (Stacks 083R): the base change of `F/X/B` to an affine `W ⟶ B` is again framed,
by the pasted frame, its `𝓛` is the pullback of `𝓛` (Stacks 03LU), and its module is of finite
type.

## Main results

* `isProperAlgebraicSpaceOver_hilbertPolynomialQuot_twistingModule_of_affine`.

## References

* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The pullback of `𝓛` to a base change is the `𝓛` of the pasted frame (Stacks 03LU). -/
def twistingModuleBaseChangeIso {D : Space.QuotSituation B integerBase B.contains_integerBase}
    (E : ProjectiveFrame B n D) {Y' : AlgebraicSpaces B integerBase B.contains_integerBase}
    (p : Y' ⟶ D.Y) :
    (Space.modulePullback B integerBase B.contains_integerBase
        (D.baseChangedSourceProjection p)).obj (twistingModule E) ≅
      twistingModule (E.baseChange p) :=
  (Space.modulePullbackCompIso B integerBase B.contains_integerBase
    (D.baseChangedSourceProjection p) E.toProjective).app (twistingModuleBase B n)

/-- **The reduction of Stacks 0DPB to framed affine bases.**  If over every affine scheme `W`
every framed Quot situation with module of finite type has `Quot^{P, 𝓛}` represented by a scheme
proper over `W`, then for every framed situation `F/X/B` with `F` of finite type,
`Quot^{P, 𝓛}_{F/X/B}` is an algebraic space proper over `B`. -/
theorem isProperAlgebraicSpaceOver_hilbertPolynomialQuot_twistingModule_of_affine {P : ℤ → ℤ}
    (haff : ∀ (D' : Space.QuotSituation B integerBase B.contains_integerBase)
      (E' : ProjectiveFrame B n D') (W : BigFppfOver B integerBase B.contains_integerBase)
      (_ : schemeSpace W ≅ D'.Y), IsAffine ((𝒯).obj W) →
        SheafOfModules.IsFiniteTypeOnSite D'.F →
          D'.IsRepresentedProper (D'.hilbertPolynomialQuot (twistingModule E') P))
    (D : Space.QuotSituation B integerBase B.contains_integerBase) (E : ProjectiveFrame B n D)
    (hft : SheafOfModules.IsFiniteTypeOnSite D.F) :
    D.IsProperAlgebraicSpaceOver (D.hilbertPolynomialQuot (twistingModule E) P) := by
  refine D.isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_isRepresentedProper
    (twistingModule E) P fun W ξ hW => ?_
  let p : schemeSpace W ⟶ D.Y := ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ
  exact Space.QuotSituation.IsRepresentedProper.of_eq
    (Space.QuotSituation.hilbertPolynomialQuot_congr (D := D.canonicalBaseChanged p) _
      (hL := Space.isInvertible_modulePullback B integerBase B.contains_integerBase
        (D.baseChangedSourceProjection p) (twistingModule E))
      (hL' := isInvertible_twistingModule (E.baseChange p))
      (twistingModuleBaseChangeIso E p) P).symm
    (haff (D.canonicalBaseChanged p) (E.baseChange p) W (Iso.refl _) hW
      (Space.isFiniteTypeOnSite_modulePullback B integerBase B.contains_integerBase _ D.F hft))

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
