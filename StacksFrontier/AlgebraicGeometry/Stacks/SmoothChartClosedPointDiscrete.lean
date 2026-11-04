module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsLocallyClosedChart

/-!
# A smooth chart with a closed point over a point of a discrete point space

Let `𝒳` be an algebraic stack over `S` whose space of points is discrete, and let `x` be a point
of `|𝒳|`. Then there is a scheme `U` of the site, a smooth 1-morphism `schemeStack U ⟶ 𝒳` and a
point of `U` which is **closed in `U`** and lies over `x`.

The two inputs are proved and unconditional. A singleton of a discrete space is open, hence
locally closed, so **Stacks 06G2** — a nonempty locally closed subset of `|𝒳|` meets the finite
type points, `AlgebraicGeometry.Stack.exists_mem_finiteTypePoints_of_isLocallyClosed` — makes `x`
itself a finite type point. **Stacks 06FX**, the implication (1) ⟹ (2) in the form
`AlgebraicGeometry.Stack.exists_isClosed_smoothChart_of_isFiniteTypePoint`, then produces the
chart and the closed point.

## Main results

* `AlgebraicGeometry.Stack.isFiniteTypePoint_of_discreteTopology`: every point of an algebraic
  stack with discrete space of points is a finite type point.
* `AlgebraicGeometry.Stack.exists_isClosed_smoothChart_of_discreteTopology`: the chart and its
  closed point.

## Implementation notes

`AlgebraicGeometry.Stack.pointTopology` of **Stacks 04Y8** is not an instance, so the
discreteness hypothesis is written with `@DiscreteTopology`, as elsewhere in this corner of the
library.

The chart is *not* asserted to be surjective: `Stacks 06FX` builds it at the given point, and a
consumer which only needs the point in its image does not need more.

## References

* [Stacks Project, Tag 04Y8](https://stacks.math.columbia.edu/tag/04Y8)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06G2](https://stacks.math.columbia.edu/tag/06G2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A point of an algebraic stack with discrete space of points is a finite type point.** The
singleton of the point is open, hence locally closed and nonempty, so it meets the set of finite
type points by **Stacks 06G2**; the only point it contains is the given one. -/
theorem isFiniteTypePoint_of_discreteTopology (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hdisc : @DiscreteTopology (points B S hS 𝒳.val.val 𝒳.val.property)
      (pointTopology B S hS 𝒳.val))
    (x : points B S hS 𝒳.val.val 𝒳.val.property) :
    IsFiniteTypePoint.{u, w} B S hS 𝒳 x := by
  let := pointTopology B S hS 𝒳.val
  let := hdisc
  obtain ⟨z, hzmem, hzft⟩ :=
    exists_mem_finiteTypePoints_of_isLocallyClosed.{u, w} B S hS 𝒳 {x}
      (isOpen_discrete _).isLocallyClosed ⟨x, rfl⟩
  exact hzmem ▸ hzft

/-- **A smooth chart with a closed point over a point of a discrete point space.** For an
algebraic stack `𝒳` over `S` whose space of points is discrete and a point `x` of `|𝒳|`, there
are a scheme `U` of the site, a smooth 1-morphism `φ : schemeStack U ⟶ 𝒳` and a point `z` of
`|schemeStack U|` whose image in the scheme `U` is closed and whose image in `|𝒳|` is `x`.

This is **Stacks 06FX**, the implication (1) ⟹ (2), applied to the finite type point that
`AlgebraicGeometry.Stack.isFiniteTypePoint_of_discreteTopology` exhibits. -/
theorem exists_isClosed_smoothChart_of_discreteTopology (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hdisc : @DiscreteTopology (points B S hS 𝒳.val.val 𝒳.val.property)
      (pointTopology B S hS 𝒳.val))
    (x : points B S hS 𝒳.val.val 𝒳.val.property) :
    ∃ (U : BigFppfOver B S hS) (φ : schemeStack.{u, w} B S hS U ⟶ 𝒳)
      (z : points B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property),
      AlgebraicStacks.IsSmooth B S hS φ ∧
        IsClosed ({pointsHomeomorphScheme B S hS U z} :
          Set ((BigFppfOver.toScheme B S hS).obj U)) ∧
        pointsMap B S hS (schemeFibredCategory B S hS U).val
          (schemeFibredCategory B S hS U).property 𝒳.val.property φ.hom.hom z = x :=
  exists_isClosed_smoothChart_of_isFiniteTypePoint.{u, w} B S hS 𝒳 x
    (isFiniteTypePoint_of_discreteTopology.{u, w} B S hS 𝒳 hdisc x)

end AlgebraicGeometry.Stack

end
