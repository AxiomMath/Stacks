module

public import Mathlib.Topology.Separation.DisjointCover
import StacksCore.Tactic.StacksAttribute

/-!
# Refining an open covering of a profinite space by clopens

Stacks 08ZZ: every open covering of a profinite space, i.e. of a compact Hausdorff totally
disconnected space, admits a refinement by a finite covering `X = ⨆ⱼ Wⱼ` with each `Wⱼ` clopen and
the `Wⱼ` pairwise disjoint. Mathlib states the stronger form in which the refining clopens are
moreover nonempty.

## References

* [Stacks Project, Tag 08ZZ](https://stacks.math.columbia.edu/tag/08ZZ)
-/

@[expose] public section

add_to_stacks 08ZZ TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover
