module

public import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCore.Tactic.StacksAttribute

/-!
# The category of sheaves of sets

Stacks 00VQ says that the category `Sh(C)` of sheaves of sets on a site is the full subcategory of
`PSh(C)` whose objects are the sheaves of sets. In Mathlib `Sheaf J A` is a separate category, so
being a full subcategory is the statement that the inclusion `sheafToPresheaf J A` is full and
faithful, which is `CategoryTheory.fullyFaithfulSheafToPresheaf`.

## References

* [Stacks Project, Tag 00VQ](https://stacks.math.columbia.edu/tag/00VQ)
-/

@[expose] public section

add_to_stacks 00VQ "the inclusion of sheaves into presheaves is fully faithful, which is what it
  means for `Sh(C)` to be a full subcategory of `PSh(C)`"
  CategoryTheory.fullyFaithfulSheafToPresheaf
