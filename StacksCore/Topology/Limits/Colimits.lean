module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Colimits of topological spaces

Stacks 0B1X: the category of topological spaces has colimits and the forgetful functor to sets
commutes with them.

Both halves are Mathlib instances.

## References

* [Stacks Project, Tag 0B1X](https://stacks.math.columbia.edu/tag/0B1X)
-/

@[expose] public section

add_to_stacks 0B1X "the category of topological spaces has colimits" TopCat.topCat_hasColimits
add_to_stacks 0B1X "the forgetful functor to sets commutes with colimits"
  TopCat.forget_preservesColimits
