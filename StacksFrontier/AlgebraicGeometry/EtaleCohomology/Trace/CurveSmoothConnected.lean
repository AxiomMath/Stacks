module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# A connected smooth scheme of relative dimension one over a field is a curve

Let `f : U ⟶ Spec k` be smooth of relative dimension one, quasi-compact and separated, with `U`
connected. Then `U` is integral (a connected smooth scheme over a field is integral,
`Stacks.Chow.isIntegral_of_connectedSpace_of_smooth`) of dimension one, so `f` is a curve.

## Main results

* `AlgebraicGeometry.isCurve_of_smoothOfRelativeDimension_one_of_connectedSpace`: a connected,
  quasi-compact, separated scheme smooth of relative dimension one over a field is a curve.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **A connected, quasi-compact, separated scheme smooth of relative dimension one over a field is
a curve.** -/
theorem isCurve_of_smoothOfRelativeDimension_one_of_connectedSpace {k : Type u} [Field k]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [QuasiCompact f]
    [IsSeparated f] [ConnectedSpace U] : IsCurve k f :=
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral U := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth f
  have : Nonempty U := ConnectedSpace.toNonempty
  { topologicalKrullDim_eq_one := by
      exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f }

end AlgebraicGeometry
