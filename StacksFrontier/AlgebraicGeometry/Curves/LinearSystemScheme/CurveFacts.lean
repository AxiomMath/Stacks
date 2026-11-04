module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeOfCurve
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# Standing facts about a smooth projective curve over an algebraically closed field

Let `X` be a smooth projective curve over an algebraically closed field `k`, with structure
morphism `f : X ⟶ Spec k`. This file records the properties of `f` that the scheme structure
on a complete linear system uses: `f` is geometrically integral. Smoothness of relative
dimension one is `Stacks.Hilbert.smoothOfRelativeDimension_one_of_isCurve`.

## Main results

* `Stacks.LinearSystemScheme.geometricallyIntegral`: `f` is geometrically integral.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.LinearSystemScheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A variety over an algebraically closed field is geometrically integral. -/
theorem geometricallyIntegral [IsAlgClosed k] [IsVariety k f] : GeometricallyIntegral f := by
  have : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X f
  have : GeometricallyReduced f := geometricallyReduced_of_isReduced f
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

end Stacks.LinearSystemScheme

end
