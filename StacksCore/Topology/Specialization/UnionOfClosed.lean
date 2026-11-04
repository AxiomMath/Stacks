module

public import Mathlib.Topology.Inseparable
import StacksCore.Tactic.StacksAttribute

/-!
# Sets stable under specialization are unions of closed sets

Stacks 0EES: a subset of a topological space is stable under specialization if and only if it is
a union of closed subsets.

This is Mathlib's theorem, verbatim.

## References

* [Stacks Project, Tag 0EES](https://stacks.math.columbia.edu/tag/0EES)
-/

@[expose] public section

add_to_stacks 0EES "stable under specialization iff a union of closed sets"
  stableUnderSpecialization_iff_exists_sUnion_eq
add_to_ega "IV 5.9.1" "Z = union of closeds" stableUnderSpecialization_iff_exists_sUnion_eq
