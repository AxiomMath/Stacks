module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescentUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomological descent of modules along hypercoverings, as a Stacks tag

For a hypercovering `K` of a site `C` with a sheaf of rings `O_C`, the canonical map
`E ⟶ Ra_*La^*E` along the ringed augmentation `a` is an isomorphism for every `E` in `D(O_C)`
(Stacks 0DA0). The tag is carried by the attribute on the theorem
`SimplicialSemiRepresentable.isIso_derivedPullbackPushforwardUnit_of_hypercoveringOfTerminal`;
this module re-exports it.

## References

* [Stacks Project, Tag 0DA0](https://stacks.math.columbia.edu/tag/0DA0)
-/

@[expose] public section

open CategoryTheory

end
