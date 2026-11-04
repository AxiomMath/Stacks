module

public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import all StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Limit situations with bounded charts

Results on `AlgebraicGeometry.Space.LimitSituation` under the bounded-charts hypothesis
`AlgebraicGeometry.Space.ChartsBounded`, kept in their own module so that the base file
`StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation` is unchanged.
-/

universe v u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace AlgebraicGeometry

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

namespace LimitSituation

variable (A : LimitSituation B S hS hZ X)

/-- **Stacks 07SF, part (1), in Situation 084R.** Every projection from the limit of a limit
situation to one of its stages is affine, provided the systems of affine charts of the
situation are bounded, `AlgebraicGeometry.Space.ChartsBounded`: that is what keeps the limits
of those charts inside the site, which is what the projection being affine is proved from.

Either of the two routes to `AlgebraicGeometry.Space.ChartsBounded` serves here, and
`AlgebraicGeometry.Space.chartsBounded_of_mk_lt_cof_ord_op` takes the one from
`#A.I < B.cutoff.ord.cof`, the companion bound on the morphism types being automatic because
the morphisms of a preorder are subsingletons.

This is `AlgebraicGeometry.Space.isAffineHom_limitπ_of_chartsBounded` transported to the cone
the situation carries. -/
theorem isAffineHom_π_of_chartsBounded (hI : ChartsBounded B S hS A.system) (i : A.Iᵒᵖ) :
    IsAffineHom B S hS (A.π.app i) := by
  have := A.hasLimit
  have hlim := isAffineHom_limitπ_of_chartsBounded B S hS A.system hI
    (fun {_ _} f => A.transition_affine f) i
  have he : (A.isLimitCone.conePointUniqueUpToIso (limit.isLimit A.system)).hom ≫
      limit.π A.system i = A.π.app i :=
    A.isLimitCone.conePointUniqueUpToIso_hom_comp (limit.isLimit A.system) i
  have hiso : IsAffineHom B S hS
      (A.isLimitCone.conePointUniqueUpToIso (limit.isLimit A.system)).hom :=
    isAffineHom_of_isIso _
  rw [← he]
  exact isAffineHom_comp B S hS _ _ hiso hlim

end LimitSituation

end Space

end AlgebraicGeometry

end

