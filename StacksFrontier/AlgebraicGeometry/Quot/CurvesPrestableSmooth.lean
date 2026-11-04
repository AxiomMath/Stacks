module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableGenusDecomposition
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothOfLimitPreserving

/-!
# `Curves^{prestable}` and `Curves^{prestable}_g` are smooth over `Spec(ℤ)` (Stacks 0E6W)

**Stacks 0E6W.** The morphisms `Curves^{prestable} → Spec(ℤ)` and
`Curves^{prestable}_g → Spec(ℤ)` are smooth.

## Main results

* `AlgebraicGeometry.isSmoothOverIntegers_of_imp_isPrestableCurveFamily`: every open substack of
  curves contained in `Curves^{prestable}` is smooth over `Spec(ℤ)`.
* `AlgebraicGeometry.isSmoothOverIntegers_curvesPrestable`: **Stacks 0E6W** for
  `Curves^{prestable}`.
* `AlgebraicGeometry.isSmoothOverIntegers_curvesPrestableOfGenus`: **Stacks 0E6W** for
  `Curves^{prestable}_g`, every `g`.

## Implementation notes

The stack of curves is algebraic (Stacks 0D5A,
`AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory`), so it has the small
model `AlgebraicGeometry.curvesAlgebraicStack`. An open substack is the open substack of that model
cut out by a property of families of curves satisfying condition (o) of Section 0E0E, and
smoothness over `Spec(ℤ)` is `AlgebraicGeometry.IsSmoothOverIntegers`: smoothness of the
inclusion followed by the structure morphism of Stacks 050D.

`Curves^{prestable}` is the property `AlgebraicGeometry.IsPrestableCurveFamily` with condition (o)
`AlgebraicGeometry.isOpenCurvesLocus_isPrestableCurveFamily` (Stacks 0E6U), and
`Curves^{prestable}_g` is the property `AlgebraicGeometry.IsPrestableGenusCurveFamily`
("prestable and `R¹f_*𝒪_X` locally free of rank `g`", part (1)(b) of Stacks 0E6V), with condition
(o) `AlgebraicGeometry.isOpenCurvesLocus_isPrestableGenusCurveFamily` (Stacks 0E6V).

## References

* [Stacks Project, Tag 0E6W](https://stacks.math.columbia.edu/tag/0E6W)
* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

open C1590Private

/-- **Open substacks of `Curves^{prestable}` are smooth over `Spec(ℤ)`.** Let `P` be a property
of families of curves satisfying condition (o) of Section 0E0E and implying prestability. Then the
open substack `Curves^P` of the algebraic stack of curves (Stacks 0D5A) is smooth over `Spec(ℤ)`.
-/
theorem isSmoothOverIntegers_of_imp_isPrestableCurveFamily
    {P : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    (hPQ : ∀ F, P F → IsPrestableCurveFamily B hZ F) :
    IsSmoothOverIntegers B hZ (isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ) hP :=
  isSmoothOverIntegers_of_imp B hZ _ hP _ (fun F hF => (hPQ F hF).1)
    (isSmoothOverIntegers_nodal_of_isLimitPreserving B hZ _
      (isLimitPreserving_curvesFiberedCategory_unconditional B hZ))

/-- The morphism `Curves^{prestable} → Spec(ℤ)` is smooth. Here `Curves^{prestable}` is the open
substack of the algebraic stack of curves (Stacks 0D5A) of the prestable families of curves
(Stacks 0E6U). -/
@[stacks 0E6W "the morphism Curves^{prestable} → Spec(ℤ) is smooth"]
theorem isSmoothOverIntegers_curvesPrestable :
    IsSmoothOverIntegers B hZ (isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
      (isOpenCurvesLocus_isPrestableCurveFamily B hZ) :=
  isSmoothOverIntegers_of_imp_isPrestableCurveFamily B hZ _ fun _ hF => hF

/-- For every `g`, the morphism `Curves^{prestable}_g → Spec(ℤ)` is smooth. Here
`Curves^{prestable}_g` is the open substack of the algebraic stack of curves (Stacks 0D5A) of the
prestable families `f : X → S` with `R¹f_*𝒪_X` locally free of rank `g` (Stacks 0E6V, part (1)).
-/
@[stacks 0E6W "the morphism Curves^{prestable}_g → Spec(ℤ) is smooth, for every g"]
theorem isSmoothOverIntegers_curvesPrestableOfGenus (g : ℕ) :
    IsSmoothOverIntegers B hZ (isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)
      (isOpenCurvesLocus_isPrestableGenusCurveFamily (B := B) (hZ := hZ) g) :=
  isSmoothOverIntegers_of_imp_isPrestableCurveFamily B hZ _ fun _ hF => hF.1

end AlgebraicGeometry

end
