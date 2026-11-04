module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of the chapter on sites covered by Mathlib

Registrations of Mathlib declarations that state results and definitions of the Stacks chapter
"Sites and Sheaves" (Chapter 7). Where a tag is covered by several declarations, each line names
the part it covers.

## References

* [Stacks Project, Tag 00VJ](https://stacks.math.columbia.edu/tag/00VJ)
* [Stacks Project, Tag 00WG](https://stacks.math.columbia.edu/tag/00WG)
-/

add_to_stacks 00VJ "the site X_Zar: coverings of U are the families of opens with union U"
  Opens.pretopology
add_to_stacks 00VJ "the Grothendieck topology on the opens of X" Opens.grothendieckTopology
add_to_stacks 00VJ "the covering families generate the Grothendieck topology of X_Zar"
  Opens.pretopology_toGrothendieck
add_to_stacks 00VJ "sheaves on a space are by definition sheaves on the site X_Zar"
  TopCat.Presheaf.IsSheaf
add_to_stacks 00VJ "sheaves of sets on X_Zar agree with the usual unique-gluing sheaves on X"
  TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types

add_to_stacks 00WG "the sheaf F^# := F^{++}" CategoryTheory.GrothendieckTopology.sheafify
add_to_stacks 00WG "the canonical map F → F^#" CategoryTheory.GrothendieckTopology.toSheafify

add_to_stacks 00X7 "If the category has a final object and fibre products, a functor preserving the
  final object and fibre products is left exact (preserves finite limits)."
  CategoryTheory.Limits.preservesFiniteLimits_of_preservesTerminal_and_pullbacks
add_to_stacks 00X7 "Conversely, a left exact functor preserves limits of every finite shape, in
  particular final objects and fibre products."
  CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits
