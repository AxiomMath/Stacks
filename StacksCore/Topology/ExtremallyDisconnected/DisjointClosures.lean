module

public import Mathlib.Topology.ExtremallyDisconnected
import StacksCore.Tactic.StacksAttribute

/-!
# Closures of disjoint opens in an extremally disconnected space

Stacks 08YK — in an extremally disconnected space, disjoint open subsets have disjoint closures —
is Mathlib's `ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen`.

## References

* [Stacks Project, Tag 08YK](https://stacks.math.columbia.edu/tag/08YK)
-/

@[expose] public section

add_to_stacks 08YK "disjoint open subsets of an extremally disconnected space have disjoint
  closures" ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen
