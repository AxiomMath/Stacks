module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SmoothSliceSeparablePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportChartZariski

/-!
# A geometric point of an algebraic space over a prescribed point of an étale chart

The chart construction of **Stacks 06N3** slices the fibre `F = U ×_𝒳 Spec k` at the closed
point `v` of an étale chart `V` of `F` that **Stacks 056U** produces. Both slicing lemmas it then
uses — **Stacks 06MD** through
`AlgebraicGeometry.Stack.FibreIsRegularSequenceAt`, and the unramifiedness criterion of
**Stacks 02GF** — read their data at a *geometric* point `z̄` of `F` together with a small étale
neighbourhood of `z̄` whose chart is `V` and whose chart point is `v`. This file produces that
geometric point.

## Main results

* `AlgebraicGeometry.Space.exists_chartGeometricPoint_chartPoint_eq`: every
  point of an étale chart of an algebraic space is the chart point of a small étale
  neighbourhood, of a geometric point of the space, whose chart is that chart.
* `AlgebraicGeometry.Space.exists_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable`:
  the slicing point of **Stacks 06N3** read at a geometric point — an étale chart of the space
  which is nonempty and smooth over `Spec k` carries a geometric point of the space whose chart
  point is the closed point of **Stacks 056U**, with its regular local ring and its finite
  separable residue field extension.

## Implementation notes

The geometric point is produced on the chart and pushed forward:
`AlgebraicGeometry.Space.exists_geometricRepresentative` gives a geometric point of the presheaf
represented by the chart over the point of that presheaf corresponding to `v`
(**Stacks 03BX**, part (1), `AlgebraicGeometry.Space.pointsEquivScheme`), and
`AlgebraicGeometry.Space.SmallEtaleNeighborhood.ofChartGeometricPoint` turns it into a small
étale neighbourhood of its image geometric point whose chart is the given one. Its chart point is
the point of the chart scheme underlying the geometric point of the chart, by
`AlgebraicGeometry.Space.chartPoint_ofChartGeometricPoint`, hence `v`.

The closed point itself, with its regularity and its residue field datum, is
`Stacks.AlgebraicGeometry.exists_isClosed_isRegularLocalRing_finiteSeparable_of_smooth` —
**Stacks 056U** on the scheme chart, together with **Stacks 056S** and the reconciliation of the
two renderings of `κ(v)` as an extension. The space-level form of Stacks 056U,
`AlgebraicGeometry.Space.dense_setOf_class_finiteSeparable_of_isSmooth` (**Stacks 07W4**), is
stated over the base `Spec k` itself and is not the form this construction can use.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)

/-- **Every point of an étale chart of an algebraic space is the chart point of a small étale
neighbourhood of a geometric point of the space.** Given an étale chart `U` of `X` and a point
`v` of the scheme underlying it, some geometric point `y` of the presheaf represented by `U` has
`v` for the chart point of the small étale neighbourhood
`AlgebraicGeometry.Space.SmallEtaleNeighborhood.ofChartGeometricPoint` it determines — a small
étale neighbourhood of the geometric point `AlgebraicGeometry.Space.geometricPointMap` of `X`
below it, whose chart is `U` itself. -/
theorem exists_chartGeometricPoint_chartPoint_eq (v : chartScheme U) :
    ∃ y : GeometricPoint B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)),
      chartPoint B S hS X.1 (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X U y) = v := by
  obtain ⟨y, hy⟩ := exists_geometricRepresentative B S hS
    (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
    ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm v)
  refine ⟨y, ?_⟩
  rw [chartPoint_ofChartGeometricPoint B S hS X U y, hy]
  exact (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).apply_symm_apply v

/-- **The slicing point of Stacks 06N3, read at a geometric point of the algebraic space.** Let
`U` be an étale chart of an algebraic space `X` whose underlying scheme `V` is nonempty and
smooth over `Spec k`. Then there are a point `v` of `V` which is **closed**, has regular local
ring `𝒪_{V, v}` and has residue field finite separable over the residue field of `Spec k` at its
image, and a geometric point of `X` — presented as a geometric point `y` of the presheaf
represented by `U` — a small étale neighbourhood of which has chart `U` and chart point `v`. -/
theorem exists_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable
    {k : Type u} [Field k] (π : chartScheme U ⟶ Spec (.of k)) [Smooth π]
    [Nonempty (chartScheme U)] :
    ∃ (v : chartScheme U)
      (y : GeometricPoint B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))),
      chartPoint B S hS X.1 (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X U y) = v ∧
        IsClosed ({v} : Set (chartScheme U)) ∧
          IsRegularLocalRing ((chartScheme U).presheaf.stalk v) ∧
            (letI := (π.residueFieldMap v).hom.toAlgebra;
              Module.Finite ((Spec (.of k)).residueField (π v))
                  ((chartScheme U).residueField v) ∧
                Algebra.IsSeparable ((Spec (.of k)).residueField (π v))
                  ((chartScheme U).residueField v)) := by
  obtain ⟨v, hvclosed, hvreg, hvsep⟩ :=
    Stacks.AlgebraicGeometry.exists_isClosed_isRegularLocalRing_finiteSeparable_of_smooth π
  obtain ⟨y, hy⟩ := exists_chartGeometricPoint_chartPoint_eq B S hS X U v
  exact ⟨v, y, hy, hvclosed, hvreg, hvsep⟩

end AlgebraicGeometry.Space

end
