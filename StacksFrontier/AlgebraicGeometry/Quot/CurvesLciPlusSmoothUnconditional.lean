module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLciPlusSmooth

/-!
# `Curves^{lci+} → Spec(ℤ)` is smooth (Stacks 0DZX, part (1))

The open substack `Curves^{lci+} = Curves^{lci} ∩ Curves^{+}` of the stack of curves is smooth over
`Spec(ℤ)`.

The open substack itself and parts (2) and (3) of Stacks 0DZX are
`AlgebraicGeometry.curvesLciPlus_isOpenSubstack`, `AlgebraicGeometry.factors_curvesLciPlus_iff`
and `AlgebraicGeometry.factors_curvesLciPlus_over_field_iff`.

## Main results

* `AlgebraicGeometry.isSmoothOverIntegers_curvesLciPlus`: `Curves^{lci+} → Spec(ℤ)` is smooth.

## References

* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
* [Stacks Project, Tag 0DZU](https://stacks.math.columbia.edu/tag/0DZU)
* [Stacks Project, Tag 0DZQ](https://stacks.math.columbia.edu/tag/0DZQ)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
-/

@[expose] public section

universe u z

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The morphism `Curves^{lci+} → Spec(ℤ)` is smooth. Here
`Curves^{lci+} = Curves^{lci} ∩ Curves^{+}` is the open substack of the algebraic stack of curves
(Stacks 0D5A) of the families of curves which are local complete intersection morphisms with
singular locus finite over the base, and smoothness over `Spec(ℤ)` is smoothness of its inclusion
followed by the structure morphism of the stack of curves. -/
@[stacks 0DZX "part (1): Curves^{lci+} → Spec(ℤ) is smooth, on the algebraic stack of curves"]
theorem isSmoothOverIntegers_curvesLciPlus :
    IsSmoothOverIntegers B hZ (curvesFiberedCategory_isAlgebraicStack.{u, z} B hZ)
      (isOpenCurvesLocus_lciPlus B hZ) :=
  isSmoothOverIntegers_lciPlus B hZ _ (curvesAlgebraicStack_isLocallyOfFinitePresentation B hZ)

end AlgebraicGeometry

end
