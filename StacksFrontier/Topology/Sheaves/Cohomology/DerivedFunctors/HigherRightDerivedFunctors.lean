module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksCore.Tactic.StacksAttribute

/-!
# Higher right derived functors

Let `F : C ⥤ D` be an additive functor between abelian categories and suppose that `C` has
enough injectives. The higher right derived functors of `F` are obtained by viewing an object
of `C` as a complex concentrated in degree zero, applying the right derived functor on the
bounded below derived categories, and taking `i`-th homology. This is the definition the
Stacks project makes in Tag 05U4, and it is already available on this branch as
`CategoryTheory.Functor.rightDerivedPlus`; this file only records the tag for it.

## Main definitions

No new definitions are introduced.

## Main results

No new results are introduced.

## Implementation notes

`CategoryTheory.Functor.rightDerivedPlus` is stated for an arbitrary abelian source category
rather than only for modules on a ringed space, and the inclusion of an object into the
bounded below derived category is made explicit by composing with the degree-zero single
object functor. The index runs over `ℤ`, as in the source.

## References

* [Stacks Project, Tag 05U4](https://stacks.math.columbia.edu/tag/05U4)
-/

@[expose] public section

add_to_stacks 05U4 CategoryTheory.Functor.rightDerivedPlus
