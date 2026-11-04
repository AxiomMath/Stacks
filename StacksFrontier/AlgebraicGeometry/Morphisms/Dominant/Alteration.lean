module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute

/-!
# Alterations

An alteration of an integral scheme is a proper dominant morphism from an integral scheme which
becomes finite over some nonempty open subscheme of the target, that is, a generically finite
proper dominant morphism.

## Main definitions

* `AlgebraicGeometry.IsAlteration` expresses that a morphism of integral schemes is an
  alteration.

## References

* [alterations, Definition 2.20]
* [Stacks Project, Tag 0AB0](https://stacks.math.columbia.edu/tag/0AB0)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A morphism to an integral scheme is an alteration if it is proper and dominant, its
source is integral, and its restriction over some nonempty open of the target is finite. -/
@[stacks 0AB0]
public abbrev IsAlteration {Y X : Scheme.{u}} [IsIntegral X] (f : Y ⟶ X) : Prop :=
  IsProper f ∧ IsDominant f ∧ IsIntegral Y ∧
    ∃ U : X.Opens, Nonempty U ∧ IsFinite (f ∣_ U)

end AlgebraicGeometry
