module

public import Mathlib.CategoryTheory.Sites.Limits
import StacksCore.Tactic.StacksAttribute

/-!
# Colimits of sheaves

Stacks 00WI says that for a diagram `F : I ⥤ Sheaf J A` the colimit `colim_I F` exists and is the
sheafification of the colimit taken in presheaves.

That is Mathlib's pair `CategoryTheory.Sheaf.sheafifyCocone`, which sheafifies a cocone of the
underlying diagram of presheaves, and `CategoryTheory.Sheaf.isColimitSheafifyCocone`, which says
that it is a colimit cocone as soon as the presheaf cocone is.

## References

* [Stacks Project, Tag 00WI](https://stacks.math.columbia.edu/tag/00WI)
-/

@[expose] public section

add_to_stacks 00WI "the colimit of a diagram of sheaves, obtained by sheafifying a cocone of the
  underlying diagram of presheaves" CategoryTheory.Sheaf.sheafifyCocone
add_to_stacks 00WI "the sheafification of a presheaf colimit cocone is a colimit cocone of
  sheaves, so the colimit of a diagram of sheaves exists and is the sheafification of the colimit
  taken in presheaves" CategoryTheory.Sheaf.isColimitSheafifyCocone
