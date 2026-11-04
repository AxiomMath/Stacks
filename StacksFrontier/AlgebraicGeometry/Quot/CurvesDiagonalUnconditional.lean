/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomQuasiCompactNoetherian
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomProjectiveQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving

/-!
# The diagonal of the stack of curves is separated and of finite presentation (Stacks 0DSQ)

**Stacks 0DSQ**: the diagonal `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of finite
presentation.

The statement is that of
`isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack`
(`AlgebraicGeometry.CurvesDiagonal`), with all of its inputs discharged: the algebraicity of
`Curves` (Stacks 0D5A) and its limit preservation (Stacks 0D55) from
`AlgebraicGeometry.C1590Private`, and the quasi-compactness of `Isom_T(Y, X) ⟶ T` for families of
curves `Y` and `X` over a common base `T`. The last is local on `T`, so `T` may be taken affine
(`AlgebraicGeometry.CurveFamily.isQuasiCompact_isomFunctorProjection_of_affine`), then Noetherian,
`Curves` being limit preserving
(`AlgebraicGeometry.CurveFamily.isQuasiCompactSpace_isomFunctor_of_isLimitPreserving`). Étale
locally on a Noetherian affine `T` both families are H-projective schemes
(`AlgebraicGeometry.CurveFamily.isQuasiCompact_isomFunctorProjection_of_projectiveCharts`), and
then the graphs of the field-valued points of `Isom_T(Y, X)` lie in finitely many Hilbert schemes
of a projective space over `T`: Riemann–Roch (Stacks 0AYX) computes their Hilbert polynomials
from Euler characteristics of the fibres, which are locally constant on `T` (Stacks 0B9T)
(`AlgebraicGeometry.CurveFamily.isQuasiCompact_isomFunctorProjection_of_isProjectiveMorphism`).

## Main results

* `AlgebraicGeometry.isSeparated_and_isRelativelyFinitePresentation_diagonal_curves`.

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0DSQ.** The diagonal of the algebraic stack `Curves` over `Spec ℤ` is separated and
of finite presentation. -/
@[stacks 0DSQ]
theorem isSeparated_and_isRelativelyFinitePresentation_diagonal_curves :
    Stack.IsSeparated B integerBase hZ
        (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ
          (curvesAlgebraicStack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)).val
          (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ))).hom) ∧
      Stack.AlgebraicStacks.IsRelativelyFinitePresentation B integerBase hZ
        (Stack.AlgebraicStacks.relativeDiagonal B integerBase hZ
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)))) := by
  have hlim := C1590Private.isLimitPreserving_curvesFiberedCategory B hZ
  refine isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack B hZ
    (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ) hlim ?_
  intro F G hb
  have halg := C1590Private.curveIsomFunctorsAlgebraic_of_curveMorFunctorsAlgebraic B hZ
    (C1590Private.curveMorFunctorsAlgebraic_of_projectiveMorFunctorsBounded B hZ
      (C1590Private.projectiveMorFunctorsBounded_of_projectiveSpaceHilbertModelsBounded B hZ
        (C1590Private.projectiveSpaceHilbertModelsBounded B hZ)))
  exact CurveFamily.isQuasiCompact_isomFunctorProjection_of_affine F G hb (halg F G hb)
    fun F' G' hb' haff => CurveFamily.isQuasiCompactSpace_isomFunctor_of_isLimitPreserving hlim
      (fun F'' G'' hb'' ha hn =>
        CurveFamily.isQuasiCompact_isomFunctorProjection_of_projectiveCharts
          (fun F₀ G₀ hb₀ ha₀ hn₀ Z₁ Z₂ q₁ q₂ e₁ e₂ he₁ he₂ hq₁ hq₂ =>
            CurveFamily.isQuasiCompact_isomFunctorProjection_of_isProjectiveMorphism F₀ G₀ hb₀ ha₀
              hn₀ Z₁ Z₂ q₁ q₂ e₁ e₂ he₁ he₂ hq₁ hq₂) F'' G'' hb'' ha hn) F' G' hb' haff

end AlgebraicGeometry

end
