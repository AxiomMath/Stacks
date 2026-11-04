module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesRelativeDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothOfLimitPreserving

/-!
# `Curves^{nodal}` is smooth over `ℤ`

Stacks 0E00: the morphism `Curves^{nodal} → Spec(ℤ)` is smooth.

## Main results

* `AlgebraicGeometry.isSmoothOverIntegers_nodal_unconditional`: the morphism
  `Curves^{nodal} → Spec(ℤ)` is smooth.

## References

* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0E00.** The morphism `Curves^{nodal} → Spec(ℤ)` is smooth: the open substack of
`Curves` cut out by the at-worst-nodal families of relative dimension one is smooth over
`Spec(ℤ)`. -/
theorem isSmoothOverIntegers_nodal_unconditional :
    IsSmoothOverIntegers B hZ (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
      (isOpenCurvesLocus_isAtWorstNodal B hZ) :=
  isSmoothOverIntegers_nodal_of_isLimitPreserving B hZ _
    (AlgebraicGeometry.C1590Private.isLimitPreserving_curvesFiberedCategory B hZ)

end AlgebraicGeometry

end
