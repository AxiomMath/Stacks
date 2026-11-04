module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOverSpaceAlgebraic

/-!
# The stack `Curves` is algebraic (Stacks 0D53, 0D5A)

The diagonal of the stack `Curves` of families of curves (Situation 0D4Z) is representable by
algebraic spaces (Stacks 0D53), and `Curves` is an algebraic stack; so is, for every algebraic
space `A`, the stack `A-Curves` of families of curves over `A` (Remark 0D54) (Stacks 0D5A).

## Main results

* `AlgebraicGeometry.C1590Private.hasRepresentableDiagonal_curvesFiberedCategory`: Stacks 0D53,
  the diagonal of `Curves` is representable by algebraic spaces.
* `AlgebraicGeometry.isAlgebraicStack_curvesStack_and_curveFamilyOver`: Stacks 0D5A, `Curves` is
  an algebraic stack, and so is `A-Curves` for every algebraic space `A`.

## References

* [Stacks Project, Tag 0D53](https://stacks.math.columbia.edu/tag/0D53)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0D54](https://stacks.math.columbia.edu/tag/0D54)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### Stacks 0D53

The diagonal `Δ : Curves ⟶ Curves × Curves` is representable by algebraic spaces:
`AlgebraicGeometry.C1590Private.hasRepresentableDiagonal_curvesFiberedCategory`. -/

add_to_stacks 0D53 AlgebraicGeometry.C1590Private.hasRepresentableDiagonal_curvesFiberedCategory

/-- The stack `Curves` (Situation 0D4Z) is algebraic. In fact, for every algebraic space `A` the
stack `A-Curves` of families of curves over `A` (Remark 0D54) is algebraic. -/
@[stacks 0D5A]
theorem isAlgebraicStack_curvesStack_and_curveFamilyOver :
    Stack.IsAlgebraicStack.{u, u + 1, u + 1, u + 1} B integerBase hZ
        (curvesFiberedCategory B hZ).val ∧
      ∀ A : AlgebraicSpaces B integerBase hZ,
        Stack.IsAlgebraicStack.{u, u + 1} B integerBase hZ (curveFamilyOverBased B hZ A) :=
  ⟨curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ, fun A =>
    curveFamilyOver_isAlgebraicStack_of_isAlgebraicStack B hZ A
      (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)⟩

end AlgebraicGeometry

end
