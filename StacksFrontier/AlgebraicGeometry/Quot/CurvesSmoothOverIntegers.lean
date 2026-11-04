module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothOfLimitPreserving

/-!
# The smooth curves are smooth over `Spec(ℤ)` (Stacks 0E1N)

The morphism `Curves^{smooth} → Spec(ℤ)` is smooth. A smooth family of curves is a local complete
intersection morphism with empty singular locus, so `Curves^{smooth} ⊂ Curves^{lci+}`
(`AlgebraicGeometry.isSmoothFamily_le_lciPlus`), and `Curves^{lci+} → Spec(ℤ)` is smooth by
part (1) of Stacks 0DZX; smoothness over the base passes to a smaller open substack
(`AlgebraicGeometry.isSmoothOverIntegers_of_imp`).

Both open substacks are read on the small model `AlgebraicGeometry.curvesAlgebraicStack B hZ h`
of the stack of curves, where `h` is the algebraicity of the stack of curves (Stacks 0D5A,
`AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory`). Part (1) of Stacks 0DZX
is `AlgebraicGeometry.isSmoothOverIntegers_lciPlus_of_isLimitPreserving`, applied to the limit
preservation of the stack of curves (Stacks 0D55,
`AlgebraicGeometry.isLimitPreserving_curvesFiberedCategory_unconditional`).

## Main results

* `AlgebraicGeometry.isSmoothOverIntegers_isSmoothFamily_of_lciPlus`: if `Curves^{lci+}` is
  smooth over `Spec(ℤ)`, so is `Curves^{smooth}`.
* `AlgebraicGeometry.isSmoothOverIntegers_isSmoothFamily`: `Curves^{smooth} → Spec(ℤ)` is
  smooth.

## Implementation notes

Smoothness of an open substack over `Spec(ℤ)` (`AlgebraicGeometry.IsSmoothOverIntegers`) is stated
on the algebraic stack `AlgebraicGeometry.curvesAlgebraicStack B hZ h`, which takes the
algebraicity `h` of the stack of curves as an argument; in
`AlgebraicGeometry.isSmoothOverIntegers_isSmoothFamily` that argument is the theorem that the stack
of curves is algebraic, so the statement has no hypothesis beyond the site `B` containing
`Spec(ℤ)`.

## References

* [Stacks Project, Tag 0E1N](https://stacks.math.columbia.edu/tag/0E1N)
* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
-/

@[expose] public section

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- If `Curves^{lci+}` is smooth over `Spec(ℤ)`, so is `Curves^{smooth}`, as
`Curves^{smooth} ⊂ Curves^{lci+}`. -/
theorem isSmoothOverIntegers_isSmoothFamily_of_lciPlus
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hsm : IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_lciPlus B hZ)) :
    IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_isSmoothFamily B hZ) :=
  isSmoothOverIntegers_of_imp B hZ h _ _ (isSmoothFamily_le_lciPlus B hZ) hsm

/-- The morphism `Curves^{smooth} → Spec(ℤ)` is smooth: the open substack of the algebraic stack
of curves (Stacks 0D5A) where the family of curves is smooth, followed by the structure morphism
to `Spec(ℤ)`, is a smooth morphism of algebraic stacks. -/
@[stacks 0E1N "Curves^{smooth} → Spec(ℤ) is smooth, on the algebraic stack of curves"]
theorem isSmoothOverIntegers_isSmoothFamily :
    IsSmoothOverIntegers B hZ (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
      (isOpenCurvesLocus_isSmoothFamily B hZ) :=
  isSmoothOverIntegers_isSmoothFamily_of_lciPlus B hZ _
    (isSmoothOverIntegers_lciPlus_of_isLimitPreserving B hZ _
      (isLimitPreserving_curvesFiberedCategory_unconditional B hZ))

end AlgebraicGeometry

end
