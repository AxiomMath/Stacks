module

public import Mathlib.CategoryTheory.Sites.Point.Category
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms between points of a site

Stacks 00YI defines a *morphism* `f : p ⟶ p'` between two points of a site `(C, J)`, given by
functors `u, u' : C ⥤ Sets`, to be a transformation of functors `f_u : u' ⟶ u`.

Mathlib bundles that data as `CategoryTheory.GrothendieckTopology.Point.Hom`.

## References

* [Stacks Project, Tag 00YI](https://stacks.math.columbia.edu/tag/00YI)
-/

@[expose] public section

add_to_stacks 00YI "a morphism of points of a site is a transformation of the fibre functors in
  the opposite direction" CategoryTheory.GrothendieckTopology.Point.Hom
