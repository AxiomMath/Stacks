module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue

/-!
# Transport of inverse images along an equality of morphisms, on chart sections

For an equality `h : f = g` of morphisms `T ⟶ X` of algebraic spaces,
`AlgebraicGeometry.Space.pullbackTransport` identifies `f^*M` with `g^*M`.  On the canonical
section `AlgebraicGeometry.Space.modulePullbackChartSection` of a chart diagram over `f` it is
the chart section of the same diagram read over `g`.  This is the bookkeeping which the unit and
cocycle conditions of a quasi-coherent module on a groupoid (Stacks 0441) need, since both are
stated through such transports.

## Main results

* `AlgebraicGeometry.Space.ChartDiagram.transport`: a chart diagram over `f` read over `g`.
* `AlgebraicGeometry.Space.pullbackTransport_chartSection`: the transport on chart sections.

## References

* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T X : AlgebraicSpaces B S hS}

/-- A chart diagram over `f` read as a chart diagram over a morphism `g` equal to `f`: the same
charts and the same vertical morphism. -/
def ChartDiagram.transport {f g : T ⟶ X} (h : f = g) (d : ChartDiagram B S hS T.1 X.1 f.hom) :
    ChartDiagram B S hS T.1 X.1 g.hom where
  U := d.U
  V := d.V
  g := d.g
  comm := h ▸ d.comm

/-- **Transport along an equality of morphisms on chart sections.**  The transport
`f^*M ⟶ g^*M` carries the chart section of a diagram over `f` to the chart section of the same
diagram read over `g`. -/
theorem pullbackTransport_chartSection (M : Modules.{u, u} B S hS X.1 X.2) {f g : T ⟶ X}
    (h : f = g) (d : ChartDiagram B S hS T.1 X.1 f.hom) (s : M.val.obj (op d.V)) :
    (pullbackTransport M h).val.app (op d.U) (modulePullbackChartSection B S hS f M d s) =
      modulePullbackChartSection B S hS g M (d.transport B S hS h) s := by
  subst h
  rfl

end AlgebraicGeometry.Space

end
