module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Finality of the inverse-image functor on opens

For a continuous map `f : X ⟶ Y` of topological spaces the inverse-image functor
`TopologicalSpace.Opens.map f` between the lattices of opens is final: the opens of `Y` whose
preimage contains a fixed open of `X` are closed under intersection, so each comma category is
cofiltered and in particular connected.

Mathlib has both halves of this — the instance `RepresentablyFlat (Opens.map f)` and the lemma
`CategoryTheory.final_of_representablyFlat` — but states finality as a lemma rather than an
instance, so a development that needs `(Opens.map f).Final` has to name it. This module names it
once.

## Main results

* `Stacks.Topology.final_opensMap`: `(TopologicalSpace.Opens.map f).Final`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.Topology

/-- The inverse-image functor on opens of a continuous map is final: it is representably flat,
the opens of the target whose preimage contains a fixed open of the source being closed under
intersection. -/
theorem final_opensMap {X Y : TopCat.{u}} (f : X ⟶ Y) : (Opens.map f).Final :=
  final_of_representablyFlat _

end Stacks.Topology
