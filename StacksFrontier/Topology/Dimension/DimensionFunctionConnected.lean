module

public import StacksFrontier.Topology.Dimension.DimensionFunctionDifference

/-!
# Dimension functions on a connected space

On a locally Noetherian sober space the difference of two dimension functions is locally constant
([Stacks, Tag 02IB]). If the space is moreover preconnected, that difference is one single integer:
two dimension functions then differ by a constant, so they order the points of the space in the
same way and single out the same irreducible components as the components of maximal dimension.

## Main results

* `TopologicalSpace.DimensionFunction.sub_eq_sub` — the difference of two dimension functions takes
  the same value at any two points.
* `TopologicalSpace.DimensionFunction.le_iff_le` — two dimension functions order the points of the
  space in the same way.
* `TopologicalSpace.DimensionFunction.maximalComponents_eq` — the union of the irreducible
  components whose generic point maximizes a dimension function is the same set for any two
  dimension functions.

## Implementation notes

A component of `X` is named here by a point of `TopologicalSpace.genericPoints X`, whose closure is
by definition an irreducible component; the component itself is `closure {ξ}`. Local Noetherianity
is the predicate `TopologicalSpace.IsLocallyNoetherianSpace`, which is a `Prop`-valued definition
rather than a class, so it is an explicit argument, exactly as in [Stacks, Tag 02IB].

## References

* [Stacks Project, Tag 02IB](https://stacks.math.columbia.edu/tag/02IB)
* [Stacks Project, Tag 02I8](https://stacks.math.columbia.edu/tag/02I8)
-/

@[expose] public section

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X] [PreconnectedSpace X]

/-- On a preconnected locally Noetherian sober space the difference of two dimension functions is
constant: a locally constant function on a preconnected space takes a single value. -/
theorem DimensionFunction.sub_eq_sub (hX : IsLocallyNoetherianSpace X)
    (δ δ' : DimensionFunction X) (x y : X) : δ x - δ' x = δ y - δ' y :=
  (DimensionFunction.isLocallyConstant_sub hX δ δ').apply_eq_of_isPreconnected
    isPreconnected_univ trivial trivial

/-- On a preconnected locally Noetherian sober space two dimension functions order the points in
the same way, since they differ by a constant. -/
theorem DimensionFunction.le_iff_le (hX : IsLocallyNoetherianSpace X)
    (δ δ' : DimensionFunction X) (x y : X) : δ x ≤ δ y ↔ δ' x ≤ δ' y := by
  have h := DimensionFunction.sub_eq_sub hX δ δ' x y
  omega

/-- The union of the irreducible components whose generic point maximizes a dimension function does
not depend on which dimension function is used: on a preconnected space the notion of an
irreducible component of maximal dimension is independent of that choice. -/
theorem DimensionFunction.maximalComponents_eq (hX : IsLocallyNoetherianSpace X)
    (δ δ' : DimensionFunction X) :
    {x : X | ∃ ξ ∈ genericPoints X, x ∈ closure {ξ} ∧ ∀ η ∈ genericPoints X, δ η ≤ δ ξ} =
      {x : X | ∃ ξ ∈ genericPoints X, x ∈ closure {ξ} ∧ ∀ η ∈ genericPoints X, δ' η ≤ δ' ξ} := by
  simp only [DimensionFunction.le_iff_le hX δ δ']

end TopologicalSpace

end
