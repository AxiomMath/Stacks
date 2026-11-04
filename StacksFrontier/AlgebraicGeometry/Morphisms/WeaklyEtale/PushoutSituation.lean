module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksCore.Tactic.StacksAttribute

/-!
# Pushouts along a closed immersion and an integral morphism

This file packages the standing situation of two morphisms of schemes over a base, one a
closed immersion and the other integral, subject to a condition ensuring that each fibre of
the latter maps into an affine open of the other scheme.

## Main definitions

* `AlgebraicGeometry.PushoutAlongClosedImmersionAndIntegralSituation` is the standing context
  for constructing the pushout.

## Implementation notes

The structure morphisms to the base and both commutative triangles are retained explicitly.
The condition on a fibre over `y` is expressed pointwise: every point mapping to `y` maps
under the closed immersion into one common affine open of `X`.

## References

* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0ECI.** The standing situation for a pushout along a
closed immersion and an integral morphism. -/
@[stacks 0ECI]
structure PushoutAlongClosedImmersionAndIntegralSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The scheme into which the closed immersion maps. -/
  X : Scheme.{u}
  /-- The target of the integral morphism. -/
  Y : Scheme.{u}
  /-- The common source of the two morphisms. -/
  Z : Scheme.{u}
  /-- The structure morphism of `X` over `S`. -/
  pX : X ⟶ S
  /-- The structure morphism of `Y` over `S`. -/
  pY : Y ⟶ S
  /-- The structure morphism of `Z` over `S`. -/
  pZ : Z ⟶ S
  /-- The closed immersion from `Z` to `X`. -/
  i : Z ⟶ X
  /-- The integral morphism from `Z` to `Y`. -/
  j : Z ⟶ Y
  /-- The morphism `i` is over `S`. -/
  i_over : i ≫ pX = pZ
  /-- The morphism `j` is over `S`. -/
  j_over : j ≫ pY = pZ
  /-- The morphism `i` is a closed immersion. -/
  [isClosedImmersion_i : IsClosedImmersion i]
  /-- The morphism `j` is integral. -/
  [isIntegralHom_j : IsIntegralHom j]
  /-- Each fibre of `j` maps under `i` into a common affine open of `X`. -/
  fiber_preimage_subset_affine :
    ∀ y : Y, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U

namespace PushoutAlongClosedImmersionAndIntegralSituation

attribute [instance] isClosedImmersion_i isIntegralHom_j

end PushoutAlongClosedImmersionAndIntegralSituation

end AlgebraicGeometry
