module

public import Mathlib.Topology.NoetherianSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Noetherian and Artinian topological spaces

A topological space is *Noetherian* when every descending chain of closed subsets stabilizes.
Dually, it is *Artinian* when every ascending chain of closed subsets stabilizes.

Mathlib already has the Noetherian condition, in the equivalent form of the ascending chain
condition on open subsets, as `TopologicalSpace.NoetherianSpace`; that declaration is the one
recorded here for the Noetherian half of the exercise. The Artinian condition is introduced
below as well-foundedness of strict reverse inclusion on closed subsets, which is the same as
stabilization of ascending chains of closed subsets. Stating it as a transparent abbreviation
lets well-founded induction on closed subsets be used directly, with no conversion lemma.

## Main definitions

* `TopologicalSpace.ArtinianSpace`: ascending chains of closed subsets stabilize.

## References

* [Stacks Project, Tag 027F](https://stacks.math.columbia.edu/tag/027F)
-/

@[expose] public section

add_to_stacks 027F "Noetherian spaces" TopologicalSpace.NoetherianSpace
add_to_sga "4 VI 2.15" TopologicalSpace.NoetherianSpace
add_to_ega "0 2.2.1" TopologicalSpace.NoetherianSpace

namespace TopologicalSpace

/-- A topological space is Artinian if its ascending chains of closed subsets stabilize. -/
@[stacks 027F "Artinian spaces"]
abbrev ArtinianSpace (X : Type*) [TopologicalSpace X] : Prop :=
  WellFoundedGT (TopologicalSpace.Closeds X)

end TopologicalSpace

end
