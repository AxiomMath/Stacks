module

public import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Separated presheaves

Stacks 00WA defines a presheaf of sets `F` on a site to be *separated* when for every covering
`{U i ⟶ U}` the map `F U ⟶ ∏ F (U i)` is injective; in sieve-theoretic form, two sections over `U`
whose restrictions along every arrow of a covering sieve agree are equal.

That predicate is Mathlib's `CategoryTheory.Presheaf.IsSeparated`, which quantifies over covering
sieves in exactly this way.

## References

* [Stacks Project, Tag 00WA](https://stacks.math.columbia.edu/tag/00WA)
-/

@[expose] public section

add_to_stacks 00WA "a presheaf is separated when two sections over `U` whose restrictions along
  every arrow of a covering sieve agree are equal" CategoryTheory.Presheaf.IsSeparated
add_to_sga "4 II 2.1" "separated presheaf" CategoryTheory.Presheaf.IsSeparated
