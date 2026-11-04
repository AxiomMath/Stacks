module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.FormalArcs.Basic.GenericKernel
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.FormalArcs.Basic.AffineCharts
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.FormalArcs.Basic.RegularCenter

/-!
# Resolution along a nonsingular formal arc

Let a two-dimensional Noetherian local domain map onto a complete discrete valuation ring. If
the local ring at the kernel is regular, the successive blowups at the centres of the induced
formal arc eventually have a regular centre.

## Main definitions

* `AlgebraicGeometry.ArcBlowupSequence` records the blowups and the compatible lifts of the
  arc, including their centres.

## Main results

* `AlgebraicGeometry.exists_regular_center` produces a stage of the sequence at which the
  centre of the next blowup is a regular point.

## References

* [Stacks Project, Tag 0BG3](https://stacks.math.columbia.edu/tag/0BG3)
-/
