module

public import Mathlib.CategoryTheory.Yoneda
import StacksCore.Tactic.StacksAttribute

/-!
# Maps out of a representable presheaf

Stacks 090F asserts that morphisms from the representable presheaf `h_U = yoneda.obj U` into a
presheaf `F` are in natural bijection with the elements of `F(U)`. That bijection is Mathlib's
`CategoryTheory.yonedaEquiv`.

## References

* [Stacks Project, Tag 090F](https://stacks.math.columbia.edu/tag/090F)
-/

@[expose] public section

add_to_stacks 090F "the Yoneda bijection `Mor_{PSh(C)}(h_U, F) = F(U)`"
  CategoryTheory.yonedaEquiv
