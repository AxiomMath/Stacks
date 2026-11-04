module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksCore.Tactic.StacksAttribute

/-!
# The reduced induced scheme structure on a locally closed subset

A locally closed subset of a scheme is closed in the open complement of its boundary. Its
reduced induced scheme structure is the closed subscheme of that open subscheme defined by the
vanishing ideal.

This module declares nothing. The construction is in
`StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedLocallyClosed`:

* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedOpen`: the complement of
  the boundary of the locally closed set.
* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedClosed`: the set,
  regarded as closed in that open subscheme.
* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedIdealSheaf`: its
  vanishing ideal, defining the reduced induced scheme structure.
* `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedScheme` and
  `Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedInclusion`: the
  resulting scheme and its canonical immersion into the ambient scheme.

The reduced induced structure on a *closed* subset is the special case in which the boundary
complement is the whole scheme; it is treated separately under tag 01J3.

## References

* [Stacks Project, Tag 0F2L](https://stacks.math.columbia.edu/tag/0F2L)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u


end AlgebraicGeometry

end
