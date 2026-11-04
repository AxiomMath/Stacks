module

public import Mathlib.Topology.Inseparable
import StacksCore.Tactic.StacksAttribute

/-!
# Images of stable sets under maps lifting specializations

Stacks 0065: for a map `f : X → Y` of topological spaces along which specializations lift, the
image of a set stable under specialization is again stable under specialization; likewise for
generalizations.

Both halves, and all four notions they are stated in terms of, are Mathlib's. "Specializations
lift along `f`" is `SpecializingMap f` and "generalizations lift along `f`" is
`GeneralizingMap f`, both phrased there as `Relation.Fibration` for the specialization relation
`x ⤳ y`, which is `y ∈ closure {x}`.

## References

* [Stacks Project, Tag 0065](https://stacks.math.columbia.edu/tag/0065)
-/

@[expose] public section

add_to_stacks 0065 "(1) the image is stable under specialization"
  SpecializingMap.stableUnderSpecialization_image
add_to_stacks 0065 "(2) the image is stable under generalization"
  GeneralizingMap.stableUnderGeneralization_image
