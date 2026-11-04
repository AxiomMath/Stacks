module

public import Mathlib.CategoryTheory.Sites.Sheafification
import StacksCore.Tactic.StacksAttribute

/-!
# Maps out of the sheafification of a representable presheaf

Stacks 090I is the chain of bijections
`Mor_{Sh(C)}(h_U^#, F) = Mor_{PSh(C)}(h_U, F) = F(U)`
for a sheaf `F` and the sheafification `h_U^#` of a representable presheaf.

Both bijections are Mathlib's. The first is the sheafification adjunction
`CategoryTheory.sheafificationAdjunction`, whose hom-equivalence at `h_U` and `F` identifies
morphisms of sheaves `h_U^# ⟶ F` with morphisms of presheaves `h_U ⟶ F`; the second is the Yoneda
lemma `CategoryTheory.yonedaEquiv`.

## References

* [Stacks Project, Tag 090I](https://stacks.math.columbia.edu/tag/090I)
-/

@[expose] public section

add_to_stacks 090I "(1) morphisms from the sheafification of a representable presheaf to a sheaf
  `F` correspond to morphisms of presheaves `h_U ⟶ F`, by the hom-equivalence of the
  sheafification adjunction" CategoryTheory.sheafificationAdjunction
add_to_stacks 090I "(2) morphisms of presheaves `h_U ⟶ F` correspond to elements of `F(U)`, by the
  Yoneda lemma" CategoryTheory.yonedaEquiv
