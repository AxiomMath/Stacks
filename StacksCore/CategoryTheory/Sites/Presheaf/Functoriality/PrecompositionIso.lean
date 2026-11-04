module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The right adjoint of restriction of presheaves

Stacks 00XH says that for a functor `u : C ⥤ D` the functor `{}_pu : PSh(C) ⥤ PSh(D)` is right
adjoint to the restriction functor `u^p : PSh(D) ⥤ PSh(C)`; equivalently, the formula
`Mor_{PSh(C)}(u^p G, F) = Mor_{PSh(D)}(G, {}_pu F)` holds bifunctorially.

All of this is Mathlib's. `u^p` is precomposition with `u.op`, i.e.
`(CategoryTheory.Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op`; `{}_pu` is the right Kan extension
`CategoryTheory.Functor.ran` along `u.op`; and the adjunction between them is
`CategoryTheory.Functor.ranAdjunction`.

## References

* [Stacks Project, Tag 00XH](https://stacks.math.columbia.edu/tag/00XH)
-/

@[expose] public section

add_to_stacks 00XH "the restriction functor `u^p : PSh(D) ⥤ PSh(C)` is precomposition with `u.op`"
  CategoryTheory.Functor.whiskeringLeft
add_to_stacks 00XH "the functor `{}_pu : PSh(C) ⥤ PSh(D)` is right Kan extension along `u.op`"
  CategoryTheory.Functor.ran
add_to_stacks 00XH "`{}_pu` is right adjoint to `u^p`"
  CategoryTheory.Functor.ranAdjunction
