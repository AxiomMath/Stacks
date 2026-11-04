module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableGenusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableSmooth
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreGlobalFunctionsOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableGenusLociOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SemistableLocusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.UniversallyBijectiveGlobalFunctions

/-!
# `Curves^{semistable}` and `Curves^{semistable}_g` are smooth over `Spec(ℤ)` (Stacks 0E72)

**Stacks 0E72.** The morphisms `Curves^{semistable} → Spec(ℤ)` and
`Curves^{semistable}_g → Spec(ℤ)` are smooth.

## Main results

* `AlgebraicGeometry.isSmoothOverIntegers_curvesSemistable_and_curvesSemistableOfGenus`:
  **Stacks 0E72**, for `Curves^{semistable}` and for `Curves^{semistable}_g`, every `g`.

## Implementation notes

The stack of curves is algebraic (Stacks 0D5A,
`AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory`), so it has the small
model `AlgebraicGeometry.curvesAlgebraicStack`. The two open substacks are the open substacks of
that model cut out by their conditions (o) of Stacks 0E0E, and smoothness over `Spec(ℤ)` is
`AlgebraicGeometry.IsSmoothOverIntegers`: smoothness of the inclusion followed by the structure
morphism of Stacks 050D.

`Curves^{semistable}` is the property `AlgebraicGeometry.IsSemistableCurveFamily` (Stacks 0E6Z)
and `Curves^{semistable}_g` is `AlgebraicGeometry.IsSemistableCurveFamilyOfFibreGenus`, the
substacks of Stacks 0E70 and 0E71, with the conditions (o) of
`AlgebraicGeometry.curvesSemistableOfGenus_isOpenSubstack_and_factors_iff`. The genus `g` ranges
over all natural numbers; for `g = 0` the substack is empty.

## References

* [Stacks Project, Tag 0E72](https://stacks.math.columbia.edu/tag/0E72)
* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
* [Stacks Project, Tag 0E71](https://stacks.math.columbia.edu/tag/0E71)
-/

@[expose] public section

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

open C1590Private

/-- The morphisms `Curves^{semistable} → Spec(ℤ)` and, for every `g`,
`Curves^{semistable}_g → Spec(ℤ)` are smooth. Here `Curves^{semistable}` and
`Curves^{semistable}_g` are the open substacks of the algebraic stack of curves (Stacks 0D5A) of
the semistable families and of the semistable families with all fibres of genus `g`. -/
@[stacks 0E72 "both morphisms Curves^{semistable} → Spec(ℤ) and Curves^{semistable}_g → Spec(ℤ), \
for every g"]
theorem isSmoothOverIntegers_curvesSemistable_and_curvesSemistableOfGenus :
    IsSmoothOverIntegers B hZ (isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
        (isOpenCurvesLocus_isSemistableCurveFamily_of
          (isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of
            (hasEtaleLocalSchemeCharts B hZ))
          (hasUniversallyBijectiveGlobalFunctions_of (hasEtaleLocalSchemeCharts B hZ))
          (prestableSemistableFibresOpen B hZ)) ∧
      ∀ g : ℕ, IsSmoothOverIntegers B hZ (isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
        (isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus
          (isOpenCurvesLocus_isSemistableCurveFamily_of
            (isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of
              (hasEtaleLocalSchemeCharts B hZ))
            (hasUniversallyBijectiveGlobalFunctions_of (hasEtaleLocalSchemeCharts B hZ))
            (prestableSemistableFibresOpen B hZ))
          (prestableGenusLociOpen_of (hasEtaleLocalSchemeCharts B hZ)) g) :=
  isSmoothOverIntegers_semistable_and_ofFibreGenus_of_isLimitPreserving B hZ
    (isAlgebraicStack_curvesFiberedCategory B hZ) (isLimitPreserving_curvesFiberedCategory B hZ)
    _ _

end AlgebraicGeometry

end
