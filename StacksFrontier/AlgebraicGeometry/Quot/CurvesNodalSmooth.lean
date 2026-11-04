module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLciPlusSmooth
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedLocallyFinitePresentation

/-!
# `Curves^{nodal}` is smooth over `Spec(ℤ)` (Stacks 0E00)

**Stacks 0E00.** The morphism `Curves^{nodal} → Spec(ℤ)` is smooth.

Here `Curves` is the stack of curves, which is algebraic (Stacks 0D5A), and `Curves^{nodal}` is
its open substack of families of curves that are at-worst-nodal of relative dimension one
(Stacks 0DSY).

## Main results

* `AlgebraicGeometry.isSmoothOverIntegers_curvesNodal`: the morphism `Curves^{nodal} → Spec(ℤ)`
  is smooth.

## Implementation notes

The stack of curves is algebraic by
`AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory` (Stacks 0D5A), so it has
the small model `AlgebraicGeometry.curvesAlgebraicStack`. `Curves^{nodal}` is the open substack of
that model cut out by the property "at-worst-nodal of relative dimension one", with condition (o)
of Section 0E0E `AlgebraicGeometry.isOpenCurvesLocus_isAtWorstNodal`, and smoothness over
`Spec(ℤ)` is `AlgebraicGeometry.IsSmoothOverIntegers`: smoothness of the inclusion followed by the
structure morphism of Stacks 050D.

## References

* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0DSY](https://stacks.math.columbia.edu/tag/0DSY)
-/

@[expose] public section

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The morphism `Curves^{nodal} → Spec(ℤ)` is smooth. Here `Curves^{nodal}` is the open substack
of the algebraic stack of curves (Stacks 0D5A) of the families of curves which are at-worst-nodal
of relative dimension one (Stacks 0DSY). -/
@[stacks 0E00]
theorem isSmoothOverIntegers_curvesNodal :
    IsSmoothOverIntegers B hZ (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
      (isOpenCurvesLocus_isAtWorstNodal B hZ) :=
  isSmoothOverIntegers_nodal B hZ _
    (isQuasiSeparated_and_isLocallyOfFinitePresentation_curvesAlgebraicStack.{u, w} B hZ).2

end AlgebraicGeometry

end
