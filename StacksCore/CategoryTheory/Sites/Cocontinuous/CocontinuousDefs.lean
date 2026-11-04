module

public import Mathlib.CategoryTheory.Sites.CoverLifting
import StacksCore.Tactic.StacksAttribute

/-!
# Cocontinuous functors

Stacks 00XJ defines a functor `u : C ⥤ D` between sites to be *cocontinuous* if for every object
`U` of `C` and every covering `{V j ⟶ u U}` in `D` there is a covering `{U i ⟶ U}` in `C` whose
image `{u (U i) ⟶ u U}` refines it.

Mathlib records that property as `CategoryTheory.Functor.IsCocontinuous`, phrased by lifting
covering sieves.

## References

* [Stacks Project, Tag 00XJ](https://stacks.math.columbia.edu/tag/00XJ)
-/

@[expose] public section

add_to_stacks 00XJ "a functor between sites is cocontinuous when every covering of `u U` in `D` is
  refined by the image of a covering of `U` in `C`"
  CategoryTheory.Functor.IsCocontinuous
add_to_sga "4 III 2.1" CategoryTheory.Functor.IsCocontinuous
