module

public import Mathlib.Topology.Category.TopCat.Limits.Konig
import StacksCore.Tactic.StacksAttribute

/-!
# A cofiltered limit of nonempty quasi-compact Hausdorff spaces is nonempty

Stacks 0A2R: for a cofiltered diagram `F : J ⥤ TopCat` with every `F.obj j` nonempty,
quasi-compact and Hausdorff, the limit is nonempty. Mathlib states this for an index category
that is cofiltered or empty, so slightly more generally.

## References

* [Stacks Project, Tag 0A2R](https://stacks.math.columbia.edu/tag/0A2R)
-/

@[expose] public section

add_to_stacks 0A2R TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system
