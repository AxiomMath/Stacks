module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute

/-!
# Closed immersions are separated

A closed immersion of schemes is separated. In Mathlib this holds by a chain of general
instances: a closed immersion is a preimmersion, a preimmersion is a monomorphism, and a
monomorphism of schemes is separated, since its diagonal is an isomorphism. This file states
the implication itself.

## Main results

* `AlgebraicGeometry.IsClosedImmersion.isSeparated`: a closed immersion is separated.

## References

* [Stacks Project, Tag 01QU](https://stacks.math.columbia.edu/tag/01QU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A closed immersion of schemes is separated. -/
@[stacks 01QU]
theorem IsClosedImmersion.isSeparated {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    IsSeparated f :=
  inferInstance

end AlgebraicGeometry
