module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Curves.UniformizerDifferential
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension

/-!
# Smooth curves have relative dimension one

A curve over a field `k` which is smooth over `k` is smooth of relative dimension one: the fibre
of `X ⟶ Spec k` is `X` itself, and an irreducible scheme locally of finite type over a field has
the same dimension at every point (Tag 0A21).

## Main results

* `AlgebraicGeometry.smoothOfRelativeDimension_one_of_isCurve`.
* `AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension`: an irreducible scheme
  smooth of relative dimension `n` over a field has dimension `n`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **An irreducible scheme smooth of relative dimension `n` over a field has dimension `n`.** -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [IrreducibleSpace X] : topologicalKrullDim X = n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x,
    ← topologicalKrullDimAt_fiber_eq f x,
    fiberDimensionAt_eq_of_smoothOfRelativeDimension f n x]

/-- **A smooth curve is smooth of relative dimension one.** -/
theorem smoothOfRelativeDimension_one_of_isCurve (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] : SmoothOfRelativeDimension 1 f := by
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f 1 fun x ↦ ?_
  rw [topologicalKrullDimAt_fiber_eq,
    ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x,
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)]
  rfl

end AlgebraicGeometry
