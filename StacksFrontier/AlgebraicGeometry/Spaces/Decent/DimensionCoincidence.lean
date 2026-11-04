module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Dimension

/-!
# For a decent space the dimension at a point is the dimension of the point space there

The dimension of an algebraic space at a point, defined through étale scheme charts, need not
coincide with the local Krull dimension of its point space at that point, but the two coincide when
the space is decent. That assertion is the last one of Stacks 0DRF.

## Main results

* `AlgebraicGeometry.Space.topologicalKrullDimAt_points_eq_dimensionAtPoint_of_isDecentSpace`:
  at every point of a decent algebraic space the local Krull dimension of the point space equals
  the dimension of the space at that point (**Stacks 0DRF**, last assertion; also Stacks 0A4J).

## References

* [Stacks Project, Tag 0A4J](https://stacks.math.columbia.edu/tag/0A4J)
* [Stacks Project, Tag 0DRF](https://stacks.math.columbia.edu/tag/0DRF)
-/

@[expose] public section

add_to_stacks 0DRF
  "the remark's last assertion: for a decent space the two dimensions do coincide at every point"
  AlgebraicGeometry.Space.topologicalKrullDimAt_points_eq_dimensionAtPoint_of_isDecentSpace

end
