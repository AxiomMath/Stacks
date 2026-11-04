module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStackHomUniverse

/-!
# The surjectivity half of Stacks 0DQ0 on the two algebraicity theorems it needs

Stacks 0DQ0 says that the projection `PolarizedCurves ⟶ 𝒞urves` is smooth and surjective. Its
surjectivity half is `AlgebraicGeometry.isSurjective_polarizedCurvesToCurvesAlgebraic_of` of
`StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesAlgebraic`, which carries three
inputs: the second assertion of Stacks 0D3Z (`h3Z`), the algebraicity of `PolarizedCurves`
(`hX`) and the algebraicity of `𝒞urves` (`hY`). Two of the three are not theorems of the Stacks
Project in that shape, and this file reduces them to the two that are.

* `h3Z` is a theorem of this library,
  `AlgebraicGeometry.polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids`, so it is
  discharged here rather than carried.
* `hX`, the algebraicity of `PolarizedCurves`, is the conjunction of two separate assertions in
  the source: **Stacks 0D4X**, that `𝒫olarized` is an algebraic stack, and **Stacks 0DPZ**, that
  the projection `PolarizedCurves ⟶ 𝒫olarized` is representable by algebraic spaces. Stacks 0DPZ
  is a theorem of this library
  (`AlgebraicGeometry.isRepresentableByAlgebraicSpaces_polarizedCurvesToPolarizedUnconditional`),
  so Stacks 05UM at the hom universe `u + 1` where both categories live, in the form
  `AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse`
  derives the algebraicity of `PolarizedCurves` from Stacks 0D4X alone. That is
  `AlgebraicGeometry.isAlgebraicStack_polarizedCurvesUnconditional_of_h0D4X`.
* `hY` is **Stacks 0D5A**, that `𝒞urves` is an algebraic stack, and it is carried unchanged.

So the surjectivity half of Stacks 0DQ0 rests on exactly Stacks 0D4X and Stacks 0D5A, both
proved in the source by Artin's axioms (Theorem 0D4X and Theorem 0D5A).

## The smoothness half

The smoothness half of Stacks 0DQ0 is not proved here. The source proves it by identifying
`PolarizedCurves ×_{𝒞urves} S` with the relatively ample locus of `Picardstack_{X/S}` (open by
Stacks 0D3D) and invoking the smoothness of `Picardstack_{X/S} ⟶ S`, **Stacks 0DPJ**. Stacks 0DPJ
is a statement about a 1-morphism of algebraic stacks only once `Picardstack_{X/S}` is known to be
an algebraic stack, **Stacks 0D04** (from **Stacks 09DS**). What the smoothness half of the
source's proof says about a single family of curves is
`AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized` of
`StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsSmoothLocallyPolarized`, on its own `hchart`
input standing for those same tags.

## Main definitions

* `AlgebraicGeometry.polarizedCurvesToCurvesAlgebraicOfPolarized`: given Stacks 0D4X and
  Stacks 0D5A, the projection `PolarizedCurves ⟶ 𝒞urves` as a 1-morphism of
  `AlgebraicGeometry.Stack.AlgebraicStacks`.

## Main results

* `AlgebraicGeometry.isAlgebraicStack_polarizedCurvesUnconditional_of_h0D4X`: `PolarizedCurves`
  is an algebraic stack as soon as `𝒫olarized` is (Stacks 0D4X), by Stacks 0DPZ and Stacks 05UM.
* `AlgebraicGeometry.isSurjective_polarizedCurvesToCurvesAlgebraicOfPolarized`: the surjectivity
  half of Stacks 0DQ0, on Stacks 0D4X and Stacks 0D5A and nothing else.

## References

* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0DPZ](https://stacks.math.columbia.edu/tag/0DPZ)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 0D3Z](https://stacks.math.columbia.edu/tag/0D3Z)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **`PolarizedCurves` is an algebraic stack as soon as `𝒫olarized` is** (Stacks 0D4X, the
hypothesis `h0D4X`). The projection `PolarizedCurves ⟶ 𝒫olarized` is representable by algebraic
spaces (Stacks 0DPZ,
`AlgebraicGeometry.isRepresentableByAlgebraicSpaces_polarizedCurvesToPolarizedUnconditional`), so
this is Stacks 05UM at the hom universe `u + 1` where both categories live. -/
theorem isAlgebraicStack_polarizedCurvesUnconditional_of_h0D4X
    (h0D4X : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val) :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedCurvesFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val :=
  Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse
    B integerBase hZ (polarizedCurvesToPolarizedUnconditional B hZ)
    (isRepresentableByAlgebraicSpaces_polarizedCurvesToPolarizedUnconditional B hZ) h0D4X

/-- **The projection `PolarizedCurves ⟶ 𝒞urves` as a 1-morphism of algebraic stacks**, on
Stacks 0D4X (`h0D4X`, `𝒫olarized` is algebraic) and Stacks 0D5A (`h0D5A`, `𝒞urves` is algebraic).
This is `AlgebraicGeometry.polarizedCurvesToCurvesAlgebraic` with the second assertion of
Stacks 0D3Z discharged and the algebraicity of `PolarizedCurves` obtained from Stacks 0D4X. -/
def polarizedCurvesToCurvesAlgebraicOfPolarized
    (h0D4X : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val)
    (h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (curvesFiberedCategory B hZ).val) :
    polarizedCurvesAlgebraicStack B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)
        (isAlgebraicStack_polarizedCurvesUnconditional_of_h0D4X B hZ h0D4X) ⟶
      curvesAlgebraicStack B hZ h0D5A :=
  polarizedCurvesToCurvesAlgebraic B hZ
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)
    (isAlgebraicStack_polarizedCurvesUnconditional_of_h0D4X B hZ h0D4X) h0D5A

/-- **The surjectivity half of Stacks 0DQ0, on Stacks 0D4X and Stacks 0D5A.** Given that
`𝒫olarized` is an algebraic stack (`h0D4X`) and that `𝒞urves` is an algebraic stack (`h0D5A`),
the projection `PolarizedCurves ⟶ 𝒞urves` is surjective in the sense of Stacks 04ZS: its map on
points is surjective.

This is `AlgebraicGeometry.isSurjective_polarizedCurvesToCurvesAlgebraic_of` with its `h3Z` input
discharged by `AlgebraicGeometry.polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids`
and its `hX` input obtained from Stacks 0D4X through Stacks 0DPZ. The two hypotheses stand for
Theorem 0D4X and Theorem 0D5A; the smoothness half of Stacks 0DQ0 is discussed in the module
documentation. -/
theorem isSurjective_polarizedCurvesToCurvesAlgebraicOfPolarized
    (h0D4X : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val)
    (h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (curvesFiberedCategory B hZ).val) :
    Stack.IsSurjective B integerBase hZ
      (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A) :=
  isSurjective_polarizedCurvesToCurvesAlgebraic_of B hZ
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)
    (isAlgebraicStack_polarizedCurvesUnconditional_of_h0D4X B hZ h0D4X) h0D5A

end AlgebraicGeometry

end
