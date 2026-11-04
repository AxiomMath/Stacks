module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurves
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesUnconditional

/-!
# The stack of polarized curves, with no hypothesis (Stacks 0DPY)

Stacks 0DPY defines *PolarizedCurves* as the 2-fibre product
`𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized`. The square, its apex and its projection to
`𝒫olarized` are `AlgebraicGeometry.polarizedCurvesSquare`,
`AlgebraicGeometry.polarizedCurvesFiberedCategory` and
`AlgebraicGeometry.polarizedCurvesToPolarized`, stated on the second assertion of Stacks 0D3Z
read over the big fppf site of `Spec(ℤ)`. Here that assertion is discharged by
`AlgebraicGeometry.polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids`, giving the
stack of polarized curves with no hypothesis.

## Main results

* `AlgebraicGeometry.polarizedCurvesSquareUnconditional`,
  `AlgebraicGeometry.polarizedCurves` and `AlgebraicGeometry.polarizedCurvesToPolarizedStack`,
  `AlgebraicGeometry.polarizedCurvesToCurves`: the 2-fibre product square, its apex
  *PolarizedCurves* and its two projections.

## References

* [Stacks Project, Tag 0DPY](https://stacks.math.columbia.edu/tag/0DPY)
* [Stacks Project, Tag 0D3Z](https://stacks.math.columbia.edu/tag/0D3Z)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The 2-fibre product square defining the stack of polarized curves: the cospan is the
forgetful 1-morphism `𝒫olarized ⟶ 𝒮paces'_{fp, flat, proper}` of Stacks 0D3Y and the inclusion
`𝒞urves ⟶ 𝒮paces'_{fp, flat, proper}` of Stacks 0D50, and the apex is the canonical 2-fibre
product of Stacks 0040. -/
@[stacks 0DPY "the 2-fibre product square defining PolarizedCurves"]
def polarizedCurvesSquareUnconditional :
    Bicategory.TwoCommSq
      (polarizedToCartesianProperFlatHom B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B))
      (curvesToCartesianProperFlatHom B hZ) :=
  polarizedCurvesSquare B hZ (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)

/-- *PolarizedCurves* `= 𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized`, the stack of
families of curves endowed with a relatively ample invertible module, as a category fibred in
groupoids over the big fppf site of `Spec(ℤ)`. -/
@[stacks 0DPY "PolarizedCurves, the apex of the 2-fibre product"]
def polarizedCurves :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  (polarizedCurvesSquareUnconditional B hZ).pt

/-- The projection `PolarizedCurves ⟶ 𝒫olarized`. -/
@[stacks 0DPY "the projection to Polarized"]
def polarizedCurvesToPolarizedStack :
    polarizedCurves B hZ ⟶
      polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B) :=
  (polarizedCurvesSquareUnconditional B hZ).fst

/-- The projection `PolarizedCurves ⟶ 𝒞urves`, forgetting the polarization. -/
@[stacks 0DPY "the projection to Curves"]
def polarizedCurvesToCurves : polarizedCurves B hZ ⟶ curvesFiberedCategory B hZ :=
  (polarizedCurvesSquareUnconditional B hZ).snd

/-- The square of `AlgebraicGeometry.polarizedCurvesSquareUnconditional` is a 2-fibre product,
being the canonical one. -/
@[stacks 0DPY "the square is a 2-fibre product"]
def isTwoFibreProduct_polarizedCurvesSquareUnconditional :
    Bicategory.IsTwoFibreProduct (polarizedCurvesSquareUnconditional B hZ) :=
  isTwoFibreProduct_polarizedCurvesSquare B hZ
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)

end AlgebraicGeometry

end
