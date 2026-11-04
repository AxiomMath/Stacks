module

public import Mathlib.Topology.Baire.LocallyCompactRegular
import StacksCore.Tactic.StacksAttribute

/-!
# Baire's theorem for locally quasi-compact Hausdorff spaces

A countable intersection of dense open subsets of a locally quasi-compact Hausdorff space
is dense.

Mathlib's `LocallyCompactSpace` expresses the Stacks Project's local quasi-compactness.
The Baire-space instance and the countable-intersection theorem are registered directly:
the instance establishes the hypotheses under which the theorem applies.

## References

* [Stacks Project, Tag 0CQN](https://stacks.math.columbia.edu/tag/0CQN)
-/

@[expose] public section

add_to_stacks 0CQN "a locally quasi-compact Hausdorff space is a Baire space"
  BaireSpace.of_t2Space_locallyCompactSpace
add_to_stacks 0CQN "a countable intersection of dense opens is dense"
  dense_iInter_of_isOpen_nat
