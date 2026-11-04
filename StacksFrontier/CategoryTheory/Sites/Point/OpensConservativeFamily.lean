module

public import Mathlib.Topology.Sheaves.Points
public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamily
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The site of opens of a topological space has enough points

Let `X` be a topological space. The site `Opens X` with its canonical topology has a
conservative family of points, namely the points of `X` themselves: a map of sheaves of sets
on `X` which is bijective on every stalk is an isomorphism.

This file records that fact in the shape of Stacks 00YK (2), that is as
`CategoryTheory.GrothendieckTopology.HasConservativeFamily`, which asks for a conservative family
of points and imposes no smallness condition on it. Mathlib proves the conservativity
itself, as `Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology`,
in the shape of `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints`; what is supplied
here is only the translation between the two shapes.

Every statement about a general ringed topos whose hypothesis is "the site has enough points" —
for instance Stacks 0DEP, the stability of K-flatness under pullback — is instantiated at a
ringed space through the site `Opens X`, and so has to discharge exactly this hypothesis. The
result also witnesses that such a hypothesis is satisfiable at all.

## Main results

* `Opens.hasConservativeFamily_grothendieckTopology`: the site of opens of a topological space
  has a conservative family of points, in the sense of Stacks 00YK (2).

## Implementation notes

The universe is the one of the space: for `X : TopCat.{u}` the points of `X` are a conservative
family of `Point.{u}`s, so the conclusion is `HasConservativeFamily.{u}`. Mathlib's family is
additionally `u`-small, so `HasEnoughPoints.{u}` holds too and the result could be obtained from
`CategoryTheory.GrothendieckTopology.HasConservativeFamily.of_hasEnoughPoints`; it is proved
from the conservative family directly instead, so that it does not depend on the smallness that
Stacks 00YK (2) deliberately does not ask for.

## References

* [Stacks Project, Tag 00YK](https://stacks.math.columbia.edu/tag/00YK)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Opens

/-- **The site of opens of a topological space has enough points.** The points of `X` form a
conservative family of points of `(Opens X, grothendieckTopology X)`: a map of sheaves of sets
on `X` which is an isomorphism on every stalk is an isomorphism.

This is Mathlib's `Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology` transported
into the shape of Stacks 00YK (2), which asks only for the existence of a conservative family
and imposes no smallness condition on it. -/
@[sga "4 IV 7.8" "(c)", sga "4 IV 9.8.2" "f), special case"]
theorem hasConservativeFamily_grothendieckTopology (X : TopCat.{u}) :
    (grothendieckTopology X).HasConservativeFamily.{u} :=
  (GrothendieckTopology.hasConservativeFamily_iff_exists _).2
    ⟨_, isConservativeFamilyOfPoints_pointsGrothendieckTopology X⟩

end Opens

end
