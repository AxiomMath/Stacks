module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyProperFlatPicardSituation
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSmoothRegistered
public import StacksFrontier.AlgebraicGeometry.Quot.PicardToBaseAlgebraicStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesSmoothPicardAmple

/-!
# Stacks 0D04 and 0DPJ at the families of curves

For every family of curves `X ⟶ T`, the Picard stack `Picardstack_{X/T}` is an algebraic stack
(Stacks 0D04) and its structure morphism `Picardstack_{X/T} ⟶ 𝒮_T` is smooth (Stacks 0DPJ). The
structure morphism of a family of curves is flat, proper and of finite presentation, and has
relative dimension at most one (Stacks 0D4Z), so both tags apply to it.

## Main results

* `AlgebraicGeometry.is0D04ForCurveFamilies`: the Picard stack of every family of curves is an
  algebraic stack.
* `AlgebraicGeometry.is0DPJForCurveFamilies`: the structure morphism of the Picard stack of every
  family of curves is smooth.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Stacks 0D04 at the families of curves: for every family of curves `X ⟶ T`, the Picard stack
`Picardstack_{X/T}` is an algebraic stack. -/
theorem is0D04ForCurveFamilies : Is0D04ForCurveFamilies.{u, w} B hZ := fun X =>
  Space.isAlgebraicStack_picardCFG.{u, w} (properFlatCoherentSituation X.toCartesianProperFlat)
    (properFlatCoherentSituation_isFlat X.toCartesianProperFlat)
    (properFlatCoherentSituation_isProper X.toCartesianProperFlat)

/-- Stacks 0DPJ at the families of curves: for every family of curves `X ⟶ T`, the structure
morphism `Picardstack_{X/T} ⟶ 𝒮_T` is smooth. -/
theorem is0DPJForCurveFamilies :
    Is0DPJForCurveFamilies.{u, w} B hZ (is0D04ForCurveFamilies.{u, w} B hZ) := fun X =>
  Space.isSmooth_picardToBaseAlgebraic_of_isSmooth_picardStructureMorphism.{u, w}
    (properFlatCoherentSituation X.toCartesianProperFlat) _
    (Space.isSmooth_picardStructureMorphism.{u, w}
      (properFlatCoherentSituation X.toCartesianProperFlat)
      (properFlatCoherentSituation_isFlat X.toCartesianProperFlat)
      (properFlatCoherentSituation_isProper X.toCartesianProperFlat) X.relativeDimensionLE)

end AlgebraicGeometry

end
