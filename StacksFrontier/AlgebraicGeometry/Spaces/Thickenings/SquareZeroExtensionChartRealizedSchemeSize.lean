module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartThickeningMap

/-!
# The size of the chart thickenings of a square-zero extension

Let `E` be a square-zero extension of the small étale structure sheaf of an algebraic space `X`
by a quasi-coherent ideal (the data of Stacks 05ZT). If a big fppf site contains the chart
thickening `U'` of an étale chart `U` of `X`, it contains the chart thickening `W'` of every
étale chart `W` mapping to `U`: `W' ⟶ U'` is étale and `W'` has the underlying space of `W`, so
the size of `W'` is bounded by those of `W` and `U'` (Stacks 04T7 and 000Q, in the form
`AlgebraicGeometry.Scheme.size_le_max_of_locallyOfFiniteType_of_isHomeomorph`). In the proof of
Stacks 05ZT this is what lets a single site containing `U'` contain all the thickenings of the
charts over `U`, in particular that of the relation `R`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.contains_chartRealizedScheme_of_hom`

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- The chart thickening `W'` has the underlying space of `W`: the inclusion `W ⟶ W'` is a
homeomorphism. -/
theorem isHomeomorph_chartInclusion (W : SmallEtale B S hS X.1) :
    IsHomeomorph (E.chartInclusion W) := by
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion (E.chartInclusion W) :=
    (E.isFirstOrderThickening_chartInclusion W).1
  exact (isHomeomorph_iff_isEmbedding_surjective).2
    ⟨(E.chartInclusion W).isClosedEmbedding.isEmbedding,
      (E.isFirstOrderThickening_chartInclusion W).isThickening.2⟩

/-- **A site containing `U'` contains `W'` for every étale chart `W ⟶ U`.** -/
theorem contains_chartRealizedScheme_of_hom {U W : SmallEtale B S hS X.1} (g : W ⟶ U)
    (hU : B.Contains (E.chartRealizedScheme U)) : B.Contains (E.chartRealizedScheme W) := by
  have : Etale (E.chartRealizedSchemeMap g) := E.etale_chartRealizedSchemeMap g
  have hle := Scheme.size_le_max_of_locallyOfFiniteType_of_isHomeomorph
    (U := chartScheme W) (E.chartRealizedSchemeMap g)
    ((E.isHomeomorph_chartInclusion W).homeomorph _).symm
    ((E.isHomeomorph_chartInclusion W).homeomorph _).symm.isHomeomorph
  exact lt_of_le_of_lt hle (max_lt W.obj.left.left.2 hU)

end AlgebraicGeometry.Space.SquareZeroExtension

end
