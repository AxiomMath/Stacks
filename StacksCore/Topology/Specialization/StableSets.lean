module

public import Mathlib.Topology.Inseparable
import StacksCore.Tactic.StacksAttribute

/-!
# Stability of open and closed subsets under specialization

Closed subsets are stable under specialization, open subsets are stable under generalization,
and a subset is stable under specialization if and only if its complement is stable under
generalization.

All three parts are registered directly from Mathlib. In the third registration,
`stableUnderGeneralization_compl_iff` states the equivalence in the reverse order.

## References

* [Stacks Project, Tag 0062](https://stacks.math.columbia.edu/tag/0062)
-/

@[expose] public section

add_to_stacks 0062 "(1)" IsClosed.stableUnderSpecialization
add_to_stacks 0062 "(2)" IsOpen.stableUnderGeneralization
add_to_stacks 0062 "(3)" stableUnderGeneralization_compl_iff
