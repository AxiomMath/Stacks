module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesSmoothUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesSeparatedOfH2H3
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpenUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurvesSmoothOverSpecZ

/-!
# `𝓜̄` and `𝓜̄_g` are smooth over `Spec(ℤ)`, and `𝓜̄_g` is separated for `g ≥ 2`

The morphisms `𝓜̄ → Spec(ℤ)` and `𝓜̄_g → Spec(ℤ)` are smooth (Stacks 0E79), and for `g ≥ 2` the
morphism `𝓜̄_g → Spec(ℤ)` is separated (Stacks 0E9A).

Both are stated on the small model `curvesAlgebraicStack B hZ h` of the stack of curves, which is
algebraic by `AlgebraicGeometry.curvesFiberedCategory_isAlgebraicStack` (Stacks 0D5A); `𝓜̄` and
`𝓜̄_g` are its open substacks cut out by the stable families, resp. the stable families of genus
`g`.

## Main results

* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus_unconditional`: the stable
  families of genus `g` form an open substack of `Curves` (the openness part of Stacks 0E78).
* `AlgebraicGeometry.isSmoothOverIntegers_stable_and_stableOfGenus_unconditional`: `𝓜̄` and
  `𝓜̄_g` are smooth over `Spec(ℤ)`.
* `AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_unconditional`: `𝓜̄_g` is separated
  over `Spec(ℤ)` for `g ≥ 2`.

## References

* [Stacks Project, Tag 0E79](https://stacks.math.columbia.edu/tag/0E79)
* [Stacks Project, Tag 0E9A](https://stacks.math.columbia.edu/tag/0E9A)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The stable families of genus `g` form an open substack of `Curves`**, with no
hypotheses. -/
alias isOpenCurvesLocus_isStableCurveFamilyOfGenus_unconditional :=
  isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_fibreGenus

/-- The morphisms `𝓜̄ → Spec(ℤ)` and `𝓜̄_g → Spec(ℤ)` are smooth, for every `g`: `𝓜̄` is the
open substack of (the small model of) the algebraic stack `Curves` cut out by the stable
families, and `𝓜̄_g` the one cut out by the stable families of genus `g`. -/
theorem isSmoothOverIntegers_stable_and_stableOfGenus_unconditional :
    IsSmoothOverIntegers B hZ (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
        (AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) ∧
      ∀ g : ℕ, IsSmoothOverIntegers B hZ
        (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
        (isOpenCurvesLocus_isStableCurveFamilyOfGenus_unconditional B hZ g) :=
  isSmoothOverIntegers_stable_and_stableOfGenus_of_h2_h3 B hZ
    (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
    CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
    CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2

/-- Let `g ≥ 2`. The stack `𝓜̄_g` is separated: the morphism `𝓜̄_g → Spec(ℤ)` (the inclusion of
the open substack of stable families of genus `g` into the small model of the algebraic stack
`Curves`, followed by its structure morphism) is separated. -/
@[stacks 0E9A "g ≥ 2 (hg); 𝓜̄_g → Spec(ℤ) is separated, which is what the source says the \
statement means; nothing is assumed"]
theorem isSeparated_moduliStableCurvesOfGenus_unconditional (g : ℕ) (hg : 2 ≤ g) :
    Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ
          (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
          (isOpenCurvesLocus_isStableCurveFamilyOfGenus_unconditional B hZ g)).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ
          (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ))) :=
  isSeparated_moduliStableCurvesOfGenus_of_h2_h3 B hZ
    (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ) g hg
    CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
    CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2

end AlgebraicGeometry

end
