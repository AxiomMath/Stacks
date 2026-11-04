module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesSmoothReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothTwoFibreProductComparison

/-!
# The base-change clause of Stacks 0DQ0 at an arbitrary base-change square

The hypothesis `hbase` of
`AlgebraicGeometry.isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange`
asks for smoothness of the first leg of the *canonical* base-change square
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` of **Stacks 04T2**. A moduli
description of the base change never produces that square: it produces some other 2-commutative
square over the same cospan, with a universal property, whose apex is the moduli stack. For the
smoothness half of Stacks 0DQ0 the moduli stack is the relatively ample locus of a Picard stack,
which is a 2-fibre product of the cospan but is not the canonical one.

`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_fst_twoFibreProductSquare_of_isTwoFibreProduct`
closes that gap: smoothness of the first leg of a 2-fibre product square depends only on the
cospan. This file records the resulting restatement, in which the base-change clause asks only
that *some* 2-fibre product square of the cospan have smooth first leg. It is strictly easier to
discharge than `hbase` and implies it.

## Main definitions

There are no new definitions.

## Main results

* `isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_exists_baseChangeSquare`, in the
  namespace `AlgebraicGeometry`: the smoothness half of Stacks 0DQ0 from an arbitrary 2-fibre
  product square of the cospan.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 0DN7](https://stacks.math.columbia.edu/tag/0DN7)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The smoothness half of Stacks 0DQ0, reduced to one base change presented by any 2-fibre
product square.** Given that `𝒫olarized` is an algebraic stack (`h0D4X`, Stacks 0D4X) and that
`𝒞urves` is an algebraic stack (`h0D5A`, Stacks 0D5A), the projection
`PolarizedCurves ⟶ 𝒞urves` is smooth as soon as, for one smooth surjective 1-morphism `g` from
the stack of a scheme of the site to `𝒞urves`, *some* 2-fibre product square of the cospan
`(g, PolarizedCurves ⟶ 𝒞urves)` has smooth first leg.

This is
`AlgebraicGeometry.isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange`
with its `hbase` hypothesis weakened from the canonical base-change square of Stacks 04T2 to an
arbitrary 2-fibre product square of the same cospan, which is what a moduli description of the
base change supplies. The two are equivalent by
`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_fst_twoFibreProductSquare_of_isTwoFibreProduct`.

No tag is registered: `h0D4X`, `h0D5A` and the base-change clause are all unproved inputs. See
the module documentation of
`StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesSmoothReduction`. -/
theorem isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_exists_baseChangeSquare
    (h0D4X : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val)
    (h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (curvesFiberedCategory B hZ).val)
    (hbase : ∀ (U : BigFppfOver B integerBase hZ)
      (g : Stack.schemeStack.{u, w} B integerBase hZ U ⟶ curvesAlgebraicStack B hZ h0D5A),
      Stack.AlgebraicStacks.IsSmooth B integerBase hZ g →
      Stack.IsSurjective B integerBase hZ g →
        ∃ P : Bicategory.TwoCommSq g
            (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A),
          Nonempty (Bicategory.IsTwoFibreProduct P) ∧
            Stack.AlgebraicStacks.IsSmooth B integerBase hZ P.fst) :
    Stack.AlgebraicStacks.IsSmooth B integerBase hZ
      (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A) :=
  isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange.{u, w}
    B hZ h0D4X h0D5A fun U g hgsm hgs => by
      obtain ⟨P, ⟨hP⟩, hPsm⟩ := hbase U g hgsm hgs
      exact Stack.AlgebraicStacks.isSmooth_fst_twoFibreProductSquare_of_isTwoFibreProduct.{u, w}
        B integerBase hZ g (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A) hP hPsm

end AlgebraicGeometry

end
