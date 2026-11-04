module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.DGCategory

/-!
# The category of complexes and the homotopy category of a differential graded category

A differential graded category `A` over a commutative ring has two ordinary categories
canonically attached to it: its *category of complexes* `Comp(A)`, with the objects of `A` and
the closed degree-zero morphisms, and its *homotopy category* `K(A)`, with the same objects and
the degree-zero cohomology of the Hom complexes as morphisms. Both are constructed in
`StacksDraft.Ch22.Sec26.Tag09L8`; this file records which declarations there realize the two
constructions and the square-zero property of the Hom differential, so that the chapter's
statements about them can cite those declarations rather than duplicate them.

## Main results

The declarations tagged here are `DGCategory.Cocycle`, `DGCategory.Comp` and
`DGCategory.instCategoryComp` for the category of complexes; `DGCategory.K`,
`DGCategory.HomotopyClass` and `DGCategory.instCategoryK` for the homotopy category; and
`DGCategory.d_d` for the vanishing of the square of the Hom differential.

## Implementation notes

`DGCategory.Cocycle` is the kernel of the differential on degree-zero morphisms, expressed as a
subtype, and `DGCategory.Comp` and `DGCategory.K` keep precisely the objects of the differential
graded category; the homotopy category's morphisms are the quotient of the degree-zero cocycles
by the coboundaries, which is `H⁰` of the differential graded Hom module. Having square-zero Hom
differentials is a field of `DGCategory`, so the projection `DGCategory.d_d` is already exactly
the assertion of the source and is tagged directly rather than wrapped in a theorem.

## References

* [Stacks Project, Tag 09L7](https://stacks.math.columbia.edu/tag/09L7)
* [Stacks Project, Tag 09L9](https://stacks.math.columbia.edu/tag/09L9)
-/

add_to_stacks 09L7 "category_of_complexes" DGCategory.Cocycle
add_to_stacks 09L7 "category_of_complexes" DGCategory.Comp
add_to_stacks 09L7 "category_of_complexes" DGCategory.instCategoryComp

add_to_stacks 09L7 "homotopy_category" DGCategory.K
add_to_stacks 09L7 "homotopy_category" DGCategory.HomotopyClass
add_to_stacks 09L7 "homotopy_category" DGCategory.instCategoryK

add_to_stacks 09L9 "hom_differential" DGCategory.d_d
