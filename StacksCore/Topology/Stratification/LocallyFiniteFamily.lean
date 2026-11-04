module

public import Mathlib.Topology.LocallyFinite
import StacksCore.Tactic.StacksAttribute

/-!
# Locally finite families of subsets

Mathlib's `LocallyFinite` expresses the definition of Stacks 0BDS: every point has a
neighbourhood meeting only finitely many members of the family. Mathlib allows an arbitrary
neighbourhood `t ∈ 𝓝 x`; choosing an open neighbourhood inside `t` gives the source's
open-neighbourhood formulation, since the indices meeting the smaller set form a subset
of those meeting `t`.

## References

* [Stacks Project, Tag 0BDS](https://stacks.math.columbia.edu/tag/0BDS)
-/

@[expose] public section

add_to_stacks 0BDS "a locally finite collection of subsets" LocallyFinite
