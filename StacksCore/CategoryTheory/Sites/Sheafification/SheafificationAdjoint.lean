module

public import Mathlib.CategoryTheory.Sites.Sheafification
import StacksCore.Tactic.StacksAttribute

/-!
# The universal property of sheafification

Stacks 00WH says that the canonical map `F ⟶ F^#` from a presheaf to its sheafification is
universal among maps from `F` to a sheaf: for any presheaf morphism `η : F ⟶ Q` whose codomain
underlies a sheaf there is a unique `γ : F^# ⟶ Q` with `F ⟶ F^# ⟶ Q` equal to `η`.

Mathlib states this at the level of a site, which subsumes the formulation over a topological
space in the Stacks tag: `CategoryTheory.sheafifyLift` is `γ`,
`CategoryTheory.toSheafify_sheafifyLift` is the factorization, and
`CategoryTheory.sheafifyLift_unique` is its uniqueness.

## References

* [Stacks Project, Tag 00WH](https://stacks.math.columbia.edu/tag/00WH)
-/

@[expose] public section

add_to_stacks 00WH "the lift `γ : F^# ⟶ Q` of a map `η : F ⟶ Q` into a sheaf"
  CategoryTheory.sheafifyLift
add_to_stacks 00WH "the lift factors `η` through the canonical map `F ⟶ F^#`"
  CategoryTheory.toSheafify_sheafifyLift
add_to_stacks 00WH "the lift is the unique such factorization"
  CategoryTheory.sheafifyLift_unique
