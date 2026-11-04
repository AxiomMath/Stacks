module

public import Mathlib.Topology.Inseparable
import StacksCore.Tactic.StacksAttribute

/-!
# Lifting specializations and generalizations is stable under composition

Stacks 0064: if specializations lift along `f : X → Y` and along `g : Y → Z` then they lift along
`g ∘ f`, and likewise for generalizations. The two conditions are Mathlib's `SpecializingMap` and
`GeneralizingMap`, expressed as fibrations of the specialization relation and its reverse.
Both composition statements are Mathlib's.

## References

* [Stacks Project, Tag 0064](https://stacks.math.columbia.edu/tag/0064)
-/

@[expose] public section

add_to_stacks 0064 "specializations lift along a composition" SpecializingMap.comp
add_to_stacks 0064 "generalizations lift along a composition" GeneralizingMap.comp
