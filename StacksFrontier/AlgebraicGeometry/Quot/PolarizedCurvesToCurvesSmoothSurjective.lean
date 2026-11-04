module

public import StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesRemark
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesSmoothReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothSchemeChartDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothBaseChange

/-!
# The projection `PolarizedCurves ⟶ 𝒞urves` is smooth and surjective (Stacks 0DQ0)

Stacks 0DQ0 says that the projection `PolarizedCurves ⟶ 𝒞urves` is smooth and surjective. It is
a statement about a 1-morphism of the 2-category of algebraic stacks of Stacks 03YP, so writing it
down uses that both stacks are algebraic: Stacks 0D4X for `𝒫olarized`, whence `PolarizedCurves`
by Stacks 0DPZ and Stacks 05UM
(`AlgebraicGeometry.isAlgebraicStack_polarizedCurvesUnconditional_of_h0D4X`), and Stacks 0D5A
for `𝒞urves`. The 1-morphism is then
`AlgebraicGeometry.polarizedCurvesToCurvesAlgebraicOfPolarized`, smoothness is Stacks 075U and
surjectivity is Stacks 04ZS.

## Main results

* `AlgebraicGeometry.isSmooth_polarizedCurvesToCurves`: the smoothness clause of Stacks 0DQ0.
* `AlgebraicGeometry.isSmooth_and_isSurjective_polarizedCurvesToCurves`: the projection
  `PolarizedCurves ⟶ 𝒞urves` is smooth and surjective.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
* [Stacks Project, Tag 0DN7](https://stacks.math.columbia.edu/tag/0DN7)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0DPZ](https://stacks.math.columbia.edu/tag/0DPZ)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The projection `PolarizedCurves ⟶ 𝒞urves` is smooth in the sense of Stacks 075U. -/
theorem isSmooth_polarizedCurvesToCurves :
    Stack.AlgebraicStacks.IsSmooth B integerBase hZ
      (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ
        (polarizedCurvesToCurves_isAlgebraic_smooth_surjective.{w, u} B hZ).2.1.1
        (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)) := by
  let C := curvesAlgebraicStack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)
  obtain ⟨U, a, hasm, hasurj⟩ :=
    Stack.exists_smooth_surjective_schemeStack.{u, w} B integerBase hZ C
  have hsm := Stack.isSmooth_versalChartSliceMap B integerBase hZ C a hasm
  exact Stack.AlgebraicStacks.isSmooth_of_baseChange B integerBase hZ _
    (Stack.versalChartSliceMap B integerBase hZ C a)
    (Stack.isSurjective_versalChartSliceMap B integerBase hZ C a hasurj)
    (Stack.AlgebraicStacks.isFlat_of_isSmooth B integerBase hZ _ hsm)
    (Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B integerBase hZ _ hsm)
    ((polarizedCurvesToCurves_isAlgebraic_smooth_surjective.{w, u} B hZ).2.2.2.2.1 U
      (Stack.versalChartPoint B integerBase hZ C a)
      (Stack.versalChartPoint_comp B integerBase hZ C a))

/-- The projection `PolarizedCurves ⟶ 𝒞urves` is smooth and surjective.

The 1-morphism is `AlgebraicGeometry.polarizedCurvesToCurvesAlgebraicOfPolarized`, the projection
of the 2-fibre product `PolarizedCurves = 𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized` of
Stacks 0DPY, read in the 2-category of algebraic stacks of Stacks 03YP; smoothness is Stacks 075U
and surjectivity is Stacks 04ZS. -/
@[stacks 0DQ0]
theorem isSmooth_and_isSurjective_polarizedCurvesToCurves :
    Stack.AlgebraicStacks.IsSmooth B integerBase hZ
        (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ
          (polarizedCurvesToCurves_isAlgebraic_smooth_surjective.{w, u} B hZ).2.1.1
          (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)) ∧
      Stack.IsSurjective B integerBase hZ
        (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ
          (polarizedCurvesToCurves_isAlgebraic_smooth_surjective.{w, u} B hZ).2.1.1
          (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)) :=
  ⟨isSmooth_polarizedCurvesToCurves.{u, w} B hZ,
    isSurjective_polarizedCurvesToCurvesAlgebraicOfPolarized.{u, w} B hZ _ _⟩

end AlgebraicGeometry

end
