module

public import Mathlib.Topology.Category.TopCat.Opens

/-!
# An open subset as a topological space

For a topological space `X` and an open subset `U ⊆ X`, the subspace `U` is the value at `U` of
Mathlib's functor `TopologicalSpace.Opens.toTopCat X : Opens X ⥤ TopCat`. Mathlib names the
functor and the inclusion `TopologicalSpace.Opens.inclusion'` out of its value, but not the value
itself, so a development working with an open immersion `j : U → X` has to spell
`(Opens.toTopCat X).obj U` out. This module names it once.

## Main definitions

* `Stacks.Topology.openSubspace`: the open subset `U` of `X`, as an object of `TopCat`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.Topology

variable {X : TopCat.{u}} (U : Opens X)

/-- The open subset `U ⊆ X`, viewed as a topological space (an object of `TopCat`) via the
subspace topology. The inclusion `j : U → X` is `TopologicalSpace.Opens.inclusion' U`. -/
abbrev openSubspace : TopCat.{u} := (Opens.toTopCat X).obj U

end Stacks.Topology

end
