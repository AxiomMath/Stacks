module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SyntomicFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The dimension formula for a smooth morphism of schemes

For a smooth morphism of locally Noetherian schemes the dimension of the source at a point is
the dimension of the target at its image plus the dimension of the fibre at that point:
`dim_x(X) = dim_{f x}(Y) + dim_x(X_{f x})`.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_eq_add_topologicalKrullDimAt_fiber_of_smooth` is
  **Stacks Tag 0AFF**.

## Implementation notes

A smooth morphism is syntomic, hence Cohen–Macaulay, so the formula is the Cohen–Macaulay
dimension formula of Tag 0AFG. This replaces the source's route through a shrinking argument
producing constant relative dimension `d` and the formula of Tag 0AFE: the Cohen–Macaulay
formula already contains that shrinking argument, and smoothness supplies Cohen–Macaulayness
without it.

## References

* [Stacks Project, Tag 0AFF](https://stacks.math.columbia.edu/tag/0AFF)
* [Stacks Project, Tag 0AFG](https://stacks.math.columbia.edu/tag/0AFG)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0AFF.** For a smooth morphism of locally Noetherian schemes the
dimension of the source at a point is the dimension of the target at its image plus the
dimension of the fibre at that point. -/
@[stacks 0AFF]
public theorem topologicalKrullDimAt_eq_add_topologicalKrullDimAt_fiber_of_smooth
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Smooth f]
    (x : X) :
    topologicalKrullDimAt X x =
      topologicalKrullDimAt Y (f x) +
        topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  have hfib : ∀ y : Y, IsLocallyNoetherian (f.fiber y) := fun y ↦ isLocallyNoetherian_fiber f y
  have _ : LocallyOfFiniteType f := inferInstance
  exact topologicalKrullDimAt_eq_add_topologicalKrullDimAt_fiber f hfib
    (isCohenMacaulay_of_syntomic (syntomic_of_smooth f) hfib) x

end AlgebraicGeometry

end
