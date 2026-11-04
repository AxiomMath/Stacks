module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
import StacksCore.Tactic.StacksAttribute

/-!
# The plus construction is locally surjective

Stacks 00W9 says that the canonical map `θ : F ⟶ F⁺` is locally surjective: for every object `U`
and every section `s` of `F⁺` over `U` there is a covering of `U` along which `s` restricts to
sections in the image of `θ`. That is Mathlib's instance
`CategoryTheory.Presheaf.isLocallySurjective_toPlus`, whose single field `imageSieve_mem` is
exactly this condition.

## References

* [Stacks Project, Tag 00W9](https://stacks.math.columbia.edu/tag/00W9)
-/

@[expose] public section

add_to_stacks 00W9 "the canonical map `F ⟶ F⁺` is locally surjective"
  CategoryTheory.Presheaf.isLocallySurjective_toPlus
