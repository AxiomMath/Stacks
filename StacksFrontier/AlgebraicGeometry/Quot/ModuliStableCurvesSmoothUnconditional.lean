module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpenUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothOfLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesRelativeDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpenUnconditional

/-!
# The stacks `𝓜̄` and `𝓜̄_g` are smooth over `Spec(ℤ)` (towards Stacks 0E79)

`AlgebraicGeometry.isSmoothOverIntegers_stable_of_isLimitPreserving` and
`AlgebraicGeometry.isSmoothOverIntegers_stableOfGenus_of_isLimitPreserving` prove Stacks 0E79 on
the small model `curvesAlgebraicStack B hZ h` of the stack of curves from the limit preservation of
`Curves` (Stacks 0D55, through Stacks 0E00) and the openness of `𝓜̄` (Stacks 0E76) and of `𝓜̄_g`
(Stacks 0E78). Stacks 0D55 and the openness of `𝓜̄` are proved
(`AlgebraicGeometry.C1590Private.isLimitPreserving_curvesFiberedCategory`,
`AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily`), and the openness of
`𝓜̄_g` is reduced to parts (2) and (3) of Stacks 0E1J
(`AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3`).

What remains is the algebraicity of the stack of curves (`h`, Stacks 0D5A), on which the small
model is built, and for `𝓜̄_g` parts (2) and (3) of Stacks 0E1J (`h2`, `h3`), on which the open
substack `𝓜̄_g` is built. The smoothness of `Curves^{nodal}` (Stacks 0E00) is
`AlgebraicGeometry.isSmoothOverIntegers_nodal_of_isLimitPreserving` and is not a hypothesis.

## Main results

* `AlgebraicGeometry.isSmoothOverIntegers_stable_of_isAlgebraicStack`: `𝓜̄ → Spec(ℤ)` is smooth.
* `AlgebraicGeometry.isSmoothOverIntegers_stableOfGenus_of_h2_h3`: `𝓜̄_g → Spec(ℤ)` is smooth.

## Implementation notes

Nothing here carries a `stacks` attribute.

## References

* [Stacks Project, Tag 0E79](https://stacks.math.columbia.edu/tag/0E79)
* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
-/

public section

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **Stacks 0E79 for `𝓜̄`, from the algebraicity of `Curves`**: with `h` the algebraicity of the
stack of curves (Stacks 0D5A), the open substack `𝓜̄ = Curves^{stable}` of its small model is
smooth over `Spec(ℤ)`. -/
theorem isSmoothOverIntegers_stable_of_isAlgebraicStack :
    IsSmoothOverIntegers B hZ h
      (AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) :=
  isSmoothOverIntegers_stable_of_isLimitPreserving B hZ h
    (AlgebraicGeometry.C1590Private.isLimitPreserving_curvesFiberedCategory B hZ)
    (AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ)

/-- **Stacks 0E79 for `𝓜̄_g`, from the algebraicity of `Curves` and parts (2) and (3) of Stacks
0E1J**: with `h` the algebraicity of the stack of curves (Stacks 0D5A), the open substack `𝓜̄_g`
of its small model, which exists by parts (2) (`h2`) and (3) (`h3`) of Stacks 0E1J, is smooth over
`Spec(ℤ)`. -/
theorem isSmoothOverIntegers_stableOfGenus_of_h2_h3 (g : ℕ)
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
    IsSmoothOverIntegers B hZ h
      (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g h2 h3) :=
  isSmoothOverIntegers_stableOfGenus_of_isLimitPreserving B hZ h
    (AlgebraicGeometry.C1590Private.isLimitPreserving_curvesFiberedCategory B hZ) g
    (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g h2 h3)

/-- **Stacks 0E79, both parts, from the algebraicity of `Curves` and parts (2) and (3) of Stacks
0E1J**: `𝓜̄ → Spec(ℤ)` is smooth, and for every `g` so is `𝓜̄_g → Spec(ℤ)`. -/
theorem isSmoothOverIntegers_stable_and_stableOfGenus_of_h2_h3
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
    IsSmoothOverIntegers B hZ h
        (AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ) ∧
      ∀ g : ℕ, IsSmoothOverIntegers B hZ h
        (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h2_h3 B hZ g h2 h3) :=
  ⟨isSmoothOverIntegers_stable_of_isAlgebraicStack B hZ h,
    fun g => isSmoothOverIntegers_stableOfGenus_of_h2_h3 B hZ h g h2 h3⟩

end AlgebraicGeometry

end
