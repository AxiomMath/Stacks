module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import StacksCore.Tactic.StacksAttribute

/-! # Common refinements of coverings

Stacks tag 00W6: two coverings `{U i ⟶ U}` and `{V j ⟶ U}` of an object of a site admit a
common refinement. In sieve form the refinement is the intersection of the two covering sieves,
and that it is again covering is Mathlib's
`CategoryTheory.GrothendieckTopology.intersection_covering`, so nothing is reproved here. The
sharper equivalence, that an intersection is covering exactly when both sieves are, is
`CategoryTheory.GrothendieckTopology.intersection_covering_iff`.

## References

* [Stacks Project, Tag 00W6](https://stacks.math.columbia.edu/tag/00W6)
-/

@[expose] public section

add_to_stacks 00W6 "common refinement" CategoryTheory.GrothendieckTopology.intersection_covering
add_to_sga "3 IV 4.2.1" "T′5 with F representable"
  CategoryTheory.GrothendieckTopology.intersection_covering
add_to_sga "4 II 1.1.1" "finite intersections"
  CategoryTheory.GrothendieckTopology.intersection_covering
