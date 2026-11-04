module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitsSupplement

/-!
# Affineness of the projections of the limit of a descent situation

In a descent situation whose systems of affine charts are bounded, every projection from the limit
to one of its stages is affine.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.isAffineHom_limitCone_π_of_chartsBounded`: the
  projections from the limit of a descent situation with bounded systems of affine charts are
  affine.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})}

/-! ### From a descent situation to a limit situation -/

namespace DescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- Every projection from the limit of a descent situation to one of its stages is affine,
provided the systems of affine charts of the system are bounded,
`AlgebraicGeometry.Space.ChartsBounded`. -/
theorem isAffineHom_limitCone_π_of_chartsBounded (hI : ChartsBounded B S hS D.system) (i : Iᵒᵖ) :
    IsAffineHom B S hS (D.limitCone.π.app i) :=
  D.toLimitSituation.isAffineHom_π_of_chartsBounded hI i

end DescentSituation

end AlgebraicGeometry.Space

end
