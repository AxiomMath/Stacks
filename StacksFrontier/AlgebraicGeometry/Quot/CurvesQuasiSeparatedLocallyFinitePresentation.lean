module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonalUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedFinitePresentation

/-!
# `Curves → Spec(ℤ)` is quasi-separated and locally of finite presentation (Stacks 0DSS)

**Stacks 0DSS**: the morphism `Curves → Spec(ℤ)` is quasi-separated and locally of finite
presentation. `Curves` is the stack of curves as an algebraic stack, its algebraicity (Stacks
0D5A) being `AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory`; it is the
algebraic stack Stacks 0DSQ is stated on
(`AlgebraicGeometry.isSeparated_and_isRelativelyFinitePresentation_diagonal_curves`).

The source's proof: quasi-separatedness asks that the diagonal be quasi-compact and
quasi-separated, which is immediate from Stacks 0DSQ; local finite presentation is Stacks 0CMY
applied to the limit preservation of `Curves`, Stacks 0D55
(`AlgebraicGeometry.isLimitPreserving_curvesFiberedCategory_unconditional`). The two steps are
`isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack`.

## Main results

* `AlgebraicGeometry.isQuasiSeparated_and_isLocallyOfFinitePresentation_curvesAlgebraicStack`:
  **Stacks 0DSS.**

## References

* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public section

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0DSS.** The morphism `Curves → Spec(ℤ)` of the algebraic stack of curves is
quasi-separated and locally of finite presentation.

Quasi-separatedness is the quasi-compactness and quasi-separatedness of the diagonal, given by
the finite presentation of the diagonal in Stacks 0DSQ
(`AlgebraicGeometry.isSeparated_and_isRelativelyFinitePresentation_diagonal_curves`); local
finite presentation is Stacks 0CMY applied to Stacks 0D55
(`AlgebraicGeometry.isLimitPreserving_curvesFiberedCategory_unconditional`). -/
@[stacks 0DSS]
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_curvesAlgebraicStack :
    Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ
          (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ))) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ
          (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ))) :=
  isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ
    (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
    (isLimitPreserving_curvesFiberedCategory_unconditional B hZ)
    (isSeparated_and_isRelativelyFinitePresentation_diagonal_curves.{u, w} B hZ).2

end AlgebraicGeometry

end
