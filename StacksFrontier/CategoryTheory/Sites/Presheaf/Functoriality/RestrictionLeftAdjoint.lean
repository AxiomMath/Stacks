module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# The left adjoint of restriction of presheaves

Stacks 00VE says that for a functor `u : C ⥤ D` the functor `u_p : PSh(C) ⥤ PSh(D)` is left
adjoint to the restriction functor `u^p : PSh(D) ⥤ PSh(C)`; equivalently, the formula
`Mor_{PSh(C)}(F, u^p G) = Mor_{PSh(D)}(u_p F, G)` holds bifunctorially.

All of this is Mathlib's, dually to the promoted Stacks 00XH. `u^p` is precomposition with
`u.op`, i.e. `(CategoryTheory.Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op`; `u_p` is the left
Kan extension `CategoryTheory.Functor.lan` along `u.op`, whose value at `V` is the colimit of
`F` over Stacks' index category `I^u_V = CostructuredArrow u.op V`; and the adjunction between
them is `CategoryTheory.Functor.lanAdjunction`.

## References

* [Stacks Project, Tag 00VE](https://stacks.math.columbia.edu/tag/00VE)
-/

@[expose] public section

add_to_stacks 00VE "the restriction functor `u^p : PSh(D) ⥤ PSh(C)` is precomposition with `u.op`"
  CategoryTheory.Functor.whiskeringLeft
add_to_stacks 00VE "the functor `u_p : PSh(C) ⥤ PSh(D)` is left Kan extension along `u.op`"
  CategoryTheory.Functor.lan
add_to_stacks 00VE "`u_p` is left adjoint to `u^p`"
  CategoryTheory.Functor.lanAdjunction
add_to_sga "4 IV 4.6.1" "partial" CategoryTheory.Functor.lanAdjunction
