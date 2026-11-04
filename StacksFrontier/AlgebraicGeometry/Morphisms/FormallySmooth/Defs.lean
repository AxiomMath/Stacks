module

public import StacksFrontier.AlgebraicGeometry.Thickenings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formally smooth morphisms of schemes

A morphism of schemes is formally smooth when every map from an affine first-order thickening's
closed subscheme lifts over the base to the thickening.

## Main definitions

* `AlgebraicGeometry.FormallySmooth` is the infinitesimal lifting property for affine first-order
  thickenings over the target scheme.

## Implementation notes

Both schemes in the thickening are required to be affine. The equations express commutativity of
the original square and of the two triangles formed by a lift.

## References

* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes has lifts against every first-order thickening of affine schemes over
its target. -/
@[sga "3 XI 1.1"]
public abbrev FormallySmooth {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ {T T' : Scheme.{u}} (_ : IsAffine T) (_ : IsAffine T') (i : T ⟶ T'),
    IsFirstOrderThickening i →
      ∀ (g : T ⟶ X) (h : T' ⟶ S), g ≫ f = i ≫ h →
        ∃ g' : T' ⟶ X, (g' ≫ f = h) ∧ (i ≫ g' = g)

end AlgebraicGeometry
