module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesAlgebraicOfPolarized
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothSchemeChartDescent

/-!
# The smoothness half of Stacks 0DQ0 at the level of the 1-morphism

Stacks 0DQ0 says that the projection `PolarizedCurves ⟶ 𝒞urves` is smooth and surjective. Its
surjectivity half is `AlgebraicGeometry.isSurjective_polarizedCurvesToCurvesAlgebraicOfPolarized`
of `StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesAlgebraicOfPolarized`, carried on the two
algebraicity inputs **Stacks 0D4X** and **Stacks 0D5A** that are needed to write the 1-morphism
down at all. This file states the *smoothness* half about the same 1-morphism — the first time it
is stated at the level of the 1-morphism rather than of a single family of curves — and carries
out the step of the source's proof that reduces it to a statement over a scheme.

## The source's proof and where it is cut

The source argues: given an object `X ⟶ S` of `𝒞urves`, equivalently a morphism
`S ⟶ 𝒞urves`, the base change `PolarizedCurves ×_{𝒞urves} S` is the substack of
`Picardstack_{X/S}` of modules that are ample on `X_T/T`, which is open by **Stacks 0D3D**, and
`Picardstack_{X/S} ⟶ S` is smooth by **Stacks 0DPJ**.

That argument is a smoothness check on a single base change, and `AlgebraicGeometry.Stack`
`.AlgebraicStacks.isSmooth_of_forall_isSmooth_baseChange_schemeStack` of
`StacksFrontier.AlgebraicGeometry.Stacks.SmoothSchemeChartDescent` is exactly the reduction of
smoothness of the 1-morphism to such a check: **Stacks 0DN7** at a smooth surjective scheme chart
of `𝒞urves`, whose flatness and local finite presentation come from its smoothness. That step is
proved here with no input beyond the two algebraicity hypotheses, and is the content of
`AlgebraicGeometry.isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange`.

The identification of the base change with the ample locus of the Picard stack is **not** carried
out: the hypothesis `hbase` below is where it would enter. It is not a held tag but a gap in this
library, and the module documentation of
`StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsSmoothLocallyPolarized` says why: the Picard
stack of a family of curves is not an object of `AlgebraicGeometry.Stack.AlgebraicStacks` — it has
its morphisms one universe up, and membership in that 2-category *is*
`AlgebraicGeometry.Stack.IsAlgebraicStack`, i.e. **Stacks 0D04**. So neither
`Picardstack_{X/S} ⟶ S` nor its ample open substack exists as a 1-morphism of algebraic stacks in
this library, and `hbase` cannot yet be decomposed into the tags it rests on. The three it rests
on are **Stacks 0D04** (from **Stacks 09DS**), **Stacks 0DPJ** and **Stacks 0DMB**; the fourth
input of the source's argument, **Stacks 0D3D**, is a theorem of this library
(`StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding`).

What the source's smoothness argument says about a *single* family of curves is
`AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized`, which rests on the same chain through
its own `hchart` input.

## No tag is registered

Stacks 0DQ0 asserts two things, and `AlgebraicGeometry`
`.isSmooth_and_isSurjective_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange`
is the two-element covering set for it. Every one of its hypotheses is an unproved input:
Stacks 0D4X, Stacks 0D5A and the base-change clause. A registration of Stacks 0DQ0 goes on that
covering set once all three are discharged.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange`
  : the smoothness half of Stacks 0DQ0, reduced by Stacks 0DN7 to the base change along a smooth
  surjective scheme chart of `𝒞urves`.
* `AlgebraicGeometry`
  `.isSmooth_and_isSurjective_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange`
  : the two clauses of Stacks 0DQ0 together.

## References

* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0DMB](https://stacks.math.columbia.edu/tag/0DMB)
* [Stacks Project, Tag 0DN7](https://stacks.math.columbia.edu/tag/0DN7)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The smoothness half of Stacks 0DQ0, reduced to a single base change.** Given that
`𝒫olarized` is an algebraic stack (`h0D4X`, Stacks 0D4X) and that `𝒞urves` is an algebraic stack
(`h0D5A`, Stacks 0D5A), the projection `PolarizedCurves ⟶ 𝒞urves` is smooth in the sense of
Stacks 075U as soon as its base change along one smooth surjective 1-morphism from the stack of a
scheme of the site to `𝒞urves` is smooth.

The hypothesis `hbase` is the clause of the source's proof that reads
`PolarizedCurves ×_{𝒞urves} S` as the relatively ample locus of `Picardstack_{X/S}`, open by
Stacks 0D3D, and smooth over `S` by Stacks 0DPJ. It is quantified over all such charts because
`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_forall_isSmooth_baseChange_schemeStack`
produces the chart itself, from the presentation clause of Stacks 026O for `𝒞urves`; only one
chart is used, by Stacks 0DN7. -/
theorem isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange
    (h0D4X : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val)
    (h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (curvesFiberedCategory B hZ).val)
    (hbase : ∀ (U : BigFppfOver B integerBase hZ)
      (g : Stack.schemeStack.{u, w} B integerBase hZ U ⟶ curvesAlgebraicStack B hZ h0D5A),
      Stack.AlgebraicStacks.IsSmooth B integerBase hZ g →
      Stack.IsSurjective B integerBase hZ g →
        Stack.AlgebraicStacks.IsSmooth B integerBase hZ
          (Stack.twoFibreProductSquareAlgebraicStacks B integerBase hZ g
            (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A)).fst) :
    Stack.AlgebraicStacks.IsSmooth B integerBase hZ
      (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A) :=
  Stack.AlgebraicStacks.isSmooth_of_forall_isSmooth_baseChange_schemeStack.{u, w}
    B integerBase hZ (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A) hbase

/-- **The two-element covering set for Stacks 0DQ0.** Given that `𝒫olarized` is an algebraic
stack (`h0D4X`, Stacks 0D4X) and that `𝒞urves` is an algebraic stack (`h0D5A`, Stacks 0D5A), the
projection `PolarizedCurves ⟶ 𝒞urves` is smooth and surjective, the first clause on the
base-change hypothesis `hbase` and the second on nothing further.

No tag is registered: all three hypotheses are unproved inputs. See the module documentation. -/
theorem
    isSmooth_and_isSurjective_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange
    (h0D4X : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val)
    (h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (curvesFiberedCategory B hZ).val)
    (hbase : ∀ (U : BigFppfOver B integerBase hZ)
      (g : Stack.schemeStack.{u, w} B integerBase hZ U ⟶ curvesAlgebraicStack B hZ h0D5A),
      Stack.AlgebraicStacks.IsSmooth B integerBase hZ g →
      Stack.IsSurjective B integerBase hZ g →
        Stack.AlgebraicStacks.IsSmooth B integerBase hZ
          (Stack.twoFibreProductSquareAlgebraicStacks B integerBase hZ g
            (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A)).fst) :
    Stack.AlgebraicStacks.IsSmooth B integerBase hZ
        (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A) ∧
      Stack.IsSurjective B integerBase hZ
        (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A) :=
  ⟨isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange
      B hZ h0D4X h0D5A hbase,
    isSurjective_polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A⟩

end AlgebraicGeometry

end
