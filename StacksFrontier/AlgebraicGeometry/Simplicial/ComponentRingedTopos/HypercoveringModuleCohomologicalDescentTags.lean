module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescentUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomological descent of modules along hypercoverings, as a Stacks tag

For a hypercovering `K` of a site `C` with a sheaf of rings `O_C`, the canonical map
`E ⟶ Ra_*La^*E` along the ringed augmentation `a` is an isomorphism for every `E` in `D(O_C)`
(Stacks 0DA0). This file attaches the tag to the theorem
`SimplicialSemiRepresentable.isIso_derivedPullbackPushforwardUnit_of_hypercoveringOfTerminal`.

## References

* [Stacks Project, Tag 0DA0](https://stacks.math.columbia.edu/tag/0DA0)
-/

@[expose] public section

open CategoryTheory

add_to_stacks 0DA0
  SimplicialSemiRepresentable.isIso_derivedPullbackPushforwardUnit_of_hypercoveringOfTerminal

end
