module

public import Mathlib.Topology.Separation.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Closed points of a quasi-compact Kolmogorov space

Stacks 005E: a nonempty quasi-compact Kolmogorov (`T₀`) space has a closed point. Mathlib states
the more general fact that in such a space every nonempty closed subset contains a point whose
singleton is closed; the tag is the case of the whole space.

## References

* [Stacks Project, Tag 005E](https://stacks.math.columbia.edu/tag/005E)
-/

@[expose] public section

add_to_stacks 005E "the case of the whole space, which is closed and assumed nonempty"
  IsClosed.exists_closed_singleton
