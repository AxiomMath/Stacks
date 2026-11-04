module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib declarations carrying Stacks tags of Chapter 65 (Algebraic Spaces)

Stacks 025V, a representable transformation of presheaves having a property `P` of morphisms
of schemes, is Mathlib's `CategoryTheory.MorphismProperty.presheaf`, the relative property
`CategoryTheory.MorphismProperty.relative` along the Yoneda embedding. Mathlib proves the two
basic facts about it that the source states right after the definition, for an arbitrary fully
faithful functor preserving fibre products, the Yoneda embedding of the big fppf site of `S`
being one such: `h_f` has `P` exactly when `f` does, and the property is stable under
composition when `P` is.

## References

* [Stacks Project, Tag 02WJ](https://stacks.math.columbia.edu/tag/02WJ)
* [Stacks Project, Tag 02WK](https://stacks.math.columbia.edu/tag/02WK)
-/

@[expose] public section

-- Stacks 02WL: the morphisms satisfying `P.relative F` are stable under base change along any
-- morphism, for every morphism property `P`.
add_to_stacks 02WL CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange
-- Stacks 02YO: if `P ≤ P'` then `P.relative F ≤ P'.relative F`.
add_to_stacks 02YO CategoryTheory.MorphismProperty.relative_monotone

add_to_stacks 02WJ "`h_f` has the relative property `P` if and only if `f` has `P`, for `P`
  stable under base change; stated for any fully faithful functor preserving fibre products"
  CategoryTheory.MorphismProperty.relative_map_iff

add_to_stacks 02WK "the relative property attached to `P` is stable under composition when `P`
  is; stated for any fully faithful functor"
  CategoryTheory.MorphismProperty.relative_isStableUnderComposition

end
