module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpenUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.UniqueStableModelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurvesPolarizationOfDualizing
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesRelativeDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableGenusDecomposition

/-!
# The stack `𝓜̄_g` is separated, from parts (2) and (3) of Stacks 0E1J (towards Stacks 0E9A)

`AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of_stableCurvesPolarization` proves the
statement of Stacks 0E9A from the openness of `𝓜̄_g` (Stacks 0E78) and of `𝓜_g` (Stacks 0E83), the
limit preservation of `Curves` (Stacks 0D55), a polarization of stable families, the density of
`|𝓜_g|` in `|𝓜̄_g|` (Stacks 0E87) and the uniqueness of stable models (Stacks 0E97). Each of these
is now proved, or reduced to parts (2) and (3) of Stacks 0E1J:

* the openness of `𝓜̄_g` and `𝓜_g`:
  `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3`,
  `AlgebraicGeometry.isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3`;
* Stacks 0D55: `AlgebraicGeometry.C1590Private.isLimitPreserving_curvesFiberedCategory`;
* the polarization by `ω_{X/S}`: `AlgebraicGeometry.stableCurvesPolarization`;
* Stacks 0E87:
  `AlgebraicGeometry.dense_preimage_pointSet_moduliSmoothOfGenus_of_isOpenCurvesLocus`, with
  condition (o) for `Curves^{prestable}_g` from Stacks 0E6V
  (`AlgebraicGeometry.isOpenCurvesLocus_isPrestableGenusCurveFamily`);
* Stacks 0E97: `AlgebraicGeometry.uniqueStableModels`.

What remains is the algebraicity of the stack of curves (`h`, Stacks 0D5A), on which the small
model `curvesAlgebraicStack B hZ h` is built, and parts (2) and (3) of Stacks 0E1J (`h2`, `h3`).

## Main results

* `AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of_h2_h3`: the statement of
  Stacks 0E9A from `h`, `h2` and `h3`.

## Implementation notes

Nothing here carries a `stacks` attribute.

## References

* [Stacks Project, Tag 0E9A](https://stacks.math.columbia.edu/tag/0E9A)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
-/

public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **The statement of Stacks 0E9A, from the algebraicity of `Curves` and parts (2) and (3) of
Stacks 0E1J.** Let `g ≥ 2` and let `𝓜̄_g` be the open substack of the small model of the stack of
curves cut out by being stable of genus `g`. Given the algebraicity of the stack of curves (`h`,
Stacks 0D5A) and parts (2) (`h2`) and (3) (`h3`) of Stacks 0E1J, the morphism `𝓜̄_g → Spec(ℤ)` is
separated. -/
theorem isSeparated_moduliStableCurvesOfGenus_of_h2_h3 (g : ℕ) (hg : 2 ≤ g)
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
    Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h
          (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g h2 h3)).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
  have hP := isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g h2 h3
  have hQ := isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 B hZ g h2 h3
  isSeparated_moduliStableCurvesOfGenus_of_stableCurvesPolarization B hZ h g hg hP hQ
    (AlgebraicGeometry.C1590Private.isLimitPreserving_curvesFiberedCategory B hZ)
    (stableCurvesPolarization B hZ)
    (dense_preimage_pointSet_moduliSmoothOfGenus_of_isOpenCurvesLocus B hZ h g hg
      ((isOpenCurvesLocus_isPrestableGenusCurveFamily g).of_iff (isPrestableGenusCurveFamily_iff g))
      hP hQ)
    (uniqueStableModels B hZ g)

end AlgebraicGeometry

end
