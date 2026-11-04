module

public import Mathlib.Topology.ExtremallyDisconnected
import StacksCore.Tactic.StacksAttribute

/-!
# Images of open subsets under irreducible surjections

For a continuous surjection carrying no proper closed subset onto its target, the image of
an open subset lies in the closure of the complement of the image of its complement.
This is registered directly as Mathlib's
`image_subset_closure_compl_image_compl_of_isOpen`.

## References

* [Stacks Project, Tag 08YJ](https://stacks.math.columbia.edu/tag/08YJ)
-/

@[expose] public section

add_to_stacks 08YJ "images of opens under a map that is onto no proper closed subset"
  image_subset_closure_compl_image_compl_of_isOpen
