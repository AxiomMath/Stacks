module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components

/-!
# The morphism of the relative duality situation is smooth of relative dimension `n`

In the situation of relative Poincaré duality ([Stacks, Tag 0G8G]) the morphism `f : X ⟶ S` is
smooth and every nonempty fibre is equidimensional of dimension `n`. A fibre of a morphism locally
of finite type is a scheme locally of finite type over a field, so an equidimensional fibre of
dimension `n` has local dimension `n` at each of its points; a smooth morphism whose fibres have
local dimension `n` everywhere is smooth of relative dimension `n` in the sense of Mathlib's
`AlgebraicGeometry.SmoothOfRelativeDimension` (standard smooth charts of relative dimension `n`).

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.smoothOfRelativeDimension`: `f` is smooth of
  relative dimension `n`.

## References

* [Stacks Project, Tag 0G8G](https://stacks.math.columbia.edu/tag/0G8G)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

/-- **In the relative duality situation, `f` is smooth of relative dimension `n`.** -/
instance smoothOfRelativeDimension (D : RelativeDualitySituation.{u}) :
    SmoothOfRelativeDimension D.n D.f := by
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq D.f D.n fun x => ?_
  have hFT : LocallyOfFiniteType (D.f.fiberToSpecResidueField (D.f x)) := by
    change LocallyOfFiniteType (pullback.snd D.f (D.S.fromSpecResidueField (D.f x)))
    infer_instance
  obtain ⟨heq, hdim⟩ := D.relativeDimension (D.f x) ⟨D.f.asFiber x⟩
  exact AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional (D.S.residueField (D.f x))
    (D.f.fiber (D.f x)) (D.f.fiberToSpecResidueField (D.f x)) heq hdim (D.f.asFiber x)

end AlgebraicGeometry.RelativeDualitySituation

end
