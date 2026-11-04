module

public import Mathlib.Topology.Separation.Hausdorff
import StacksCore.Tactic.StacksAttribute

/-!
# Hausdorff spaces and the diagonal

A topological space `X` is Hausdorff if and only if its diagonal is closed in `X × X`.
This equivalence is registered directly as Mathlib's `t2_iff_isClosed_diagonal`.

## References

* [Stacks Project, Tag 08ZE](https://stacks.math.columbia.edu/tag/08ZE)
-/

@[expose] public section

add_to_stacks 08ZE t2_iff_isClosed_diagonal
