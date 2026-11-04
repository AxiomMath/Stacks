module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmooth
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable

/-!
# The moduli stacks of smooth and of stable curves (Stacks 0E82, 0E77)

Stacks 0E82 names `𝓜 = Curves^{smooth, h0}` the *moduli stack of smooth proper curves*: the
substack of the stack of curves of families `f : X → S` which are smooth of relative dimension one
with `f_*𝒪_X = 𝒪_S` universally (Stacks 0E81). Stacks 0E77 names `𝓜̄ = Curves^{stable}` the
*moduli stack of stable curves*: the substack of stable families (Stacks 0E75, 0E76).

This file records both as strictly full subcategories of the category of families of curves,
fibred in groupoids over the big fppf site of `Spec(ℤ)`, through
`AlgebraicGeometry.curvesSubstack`.

## Main definitions

* `AlgebraicGeometry.IsSmoothH0Family`: the defining condition of `Curves^{smooth, h0}`,
  condition (1)(b) of Stacks 0E81.
* `AlgebraicGeometry.moduliSmoothCurves`: the stack `𝓜` of Stacks 0E82, with inclusion
  `AlgebraicGeometry.moduliSmoothCurvesInclusion` into `Curves`.
* `AlgebraicGeometry.moduliStableCurves`: the stack `𝓜̄` of Stacks 0E77, with inclusion
  `AlgebraicGeometry.moduliStableCurvesInclusion` into `Curves`.

## Implementation notes

The source calls `𝓜` and `𝓜̄` *algebraic stacks*. They are open substacks of the algebraic stack
`Curves` (Stacks 0D5A), the openness being Stacks 0E81 and Stacks 0E76, and an open substack of an
algebraic stack is algebraic. The categories fibred in groupoids recorded here are those
substacks, the objects the definitions name; their openness and algebraicity are the content of
Stacks 0E81 and 0E76 and are not asserted in this file. The moduli stack `𝓜̄_g` of stable curves of
genus `g`, the other half of Stacks 0E77, is `AlgebraicGeometry.moduliStableCurvesOfGenus`.

Membership in `𝓜` passes to base changes because smoothness of relative dimension one does
(`AlgebraicGeometry.CurveFamily.isSmoothDimOneFamily_of_hom`) and the universal bijectivity of
global functions does
(`AlgebraicGeometry.CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hom`); membership in
`𝓜̄` by `AlgebraicGeometry.CurveFamily.isStableCurveFamily_of_hom`.

## References

* [Stacks Project, Tag 0E82](https://stacks.math.columbia.edu/tag/0E82)
* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
* [Stacks Project, Tag 0E77](https://stacks.math.columbia.edu/tag/0E77)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The defining condition of `Curves^{smooth, h0}` (condition (1)(b) of Stacks 0E81): the family
of curves `f : X → S` is smooth of relative dimension one and `f_*𝒪_X = 𝒪_S`, universally. -/
abbrev IsSmoothH0Family (X : CurveFamily B hZ) : Prop :=
  IsSmoothDimOneFamily B hZ X ∧ HasUniversallyBijectiveGlobalFunctions B hZ X

/-- A family of curves mapping to a family in `Curves^{smooth, h0}` is in
`Curves^{smooth, h0}`. -/
theorem CurveFamily.isSmoothH0Family_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsSmoothH0Family B hZ Y) : IsSmoothH0Family B hZ X :=
  ⟨CurveFamily.isSmoothDimOneFamily_of_hom B hZ φ hY.1,
    CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hom φ hY.2⟩

/-- **The moduli stack `𝓜 = Curves^{smooth, h0}` of smooth proper curves**: the substack of the
stack of curves of the families of curves `f : X → S` which are smooth of relative dimension one
with `f_*𝒪_X = 𝒪_S`, this holding after any base change (condition (1)(b) of Stacks 0E81), as a
category fibred in groupoids over the big fppf site of `Spec(ℤ)`. -/
@[stacks 0E82 "the moduli stack of smooth proper curves, 𝓜 = Curves^{smooth, h0}"]
def moduliSmoothCurves :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesSubstack B hZ (IsSmoothH0Family B hZ) (CurveFamily.isSmoothH0Family_of_hom B hZ)

/-- The inclusion `𝓜 ⟶ Curves`. -/
def moduliSmoothCurvesInclusion : moduliSmoothCurves B hZ ⟶ curvesFiberedCategory B hZ :=
  curvesSubstackInclusion B hZ (IsSmoothH0Family B hZ) (CurveFamily.isSmoothH0Family_of_hom B hZ)

/-- **The moduli stack `𝓜̄ = Curves^{stable}` of stable curves**: the substack of the stack of
curves of the families of curves which are stable (Stacks 0E75), as a category fibred in groupoids
over the big fppf site of `Spec(ℤ)`. -/
@[stacks 0E77 "the moduli stack of stable curves, 𝓜̄ = Curves^{stable}"]
def moduliStableCurves :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesSubstack B hZ (IsStableCurveFamily B hZ) CurveFamily.isStableCurveFamily_of_hom

/-- The inclusion `𝓜̄ ⟶ Curves`. -/
def moduliStableCurvesInclusion : moduliStableCurves B hZ ⟶ curvesFiberedCategory B hZ :=
  curvesSubstackInclusion B hZ (IsStableCurveFamily B hZ) CurveFamily.isStableCurveFamily_of_hom

end AlgebraicGeometry

end
