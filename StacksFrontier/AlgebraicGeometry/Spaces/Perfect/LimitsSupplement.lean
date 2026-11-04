module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Supplement to `Limits`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `HasAffineStageDescent`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

/-- **Stacks 07SQ.** In the situation of Stacks 084R, if the limit of the inverse system is an
affine algebraic space then some stage beyond the distinguished one is an affine algebraic
space.

The system is required to have bounded charts, `AlgebraicGeometry.Space.ChartsBounded`, which
is what keeps the limit computed in the site equal to the limit the source speaks of: the
limits of the affine charts of the system then stay inside the site, as Stacks 07SF needs. See
the implementation notes of this module for the system that refutes the statement without any
such restriction, and for why this is the hypothesis a presentation of an integral morphism as
a directed limit of finite morphisms of finite presentation actually supplies.

Stacks 07SI, the identification `Γ(X, 𝒪_X) = colim_i Γ(X_i, 𝒪_{X_i})` that supplies the ring
an affine stage maps to, is `AlgebraicGeometry.Space.LimitSituation`
`.isStagesColimit_globalFunctions`, and the standard-étale presentation of the chart of the
affine limit is `AlgebraicGeometry.Space.exists_coordinateHom_bijective_of_isEtale`.

This property holds of every big fppf site: `AlgebraicGeometry.Space.hasAffineStageDescent` of
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/AffineStageDescent.lean` proves it,
and that declaration carries the tag. -/
def HasAffineStageDescent (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) : Prop :=
  ∀ {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] (E : DescentSituation B S hS hZ J),
    ChartsBounded B S hS E.system → IsAffineSpace B S hS E.limitCone.pt →
      ∃ j, E.base ≤ j ∧ IsAffineSpace B S hS (E.system.obj (Opposite.op j))

end AlgebraicGeometry.Space

end
