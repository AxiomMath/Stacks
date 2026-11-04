module

public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CoverLifting

/-!
# Lower shriek for sheaves of sets on the lisse-étale site

For an algebraic stack, the inverse image of the morphism from its lisse-étale topos to its
étale topos has a left adjoint on sheaves of sets.

That inverse image is restriction along the continuous inclusion of the lisse-étale site into
the étale site. The general lower-shriek construction
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`, which sheafifies the left Kan
extension along the inclusion of sites, and its adjunction with restriction,
`CategoryTheory.Functor.sheafAdjunctionLowerShriek`, apply to that inclusion with set-valued
sheaves. They are recorded in their general form rather than wrapped for this particular site.

## References

* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
-/

add_to_stacks 0788 "lisse_sets_shriek"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback
add_to_stacks 0788 "lisse_sets_shriek" CategoryTheory.Functor.sheafAdjunctionLowerShriek
