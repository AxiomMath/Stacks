module

public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward of (pre)sheaves of algebraic structures

Stacks 00YS defines, for a morphism of sites `f : D ⟶ C` given by a functor `u : C ⥤ D`, the
pushforward of a presheaf of algebraic structures by the rule `u^p F (U) = F(u U)`, and the
pushforward of a sheaf of algebraic structures by the same rule, `f_* F (U) = F(u U)`.

Both are Mathlib's, for an arbitrary category `A` of algebraic structures. On presheaves the
rule is precomposition with `u.op`, `(CategoryTheory.Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj
u.op`; on sheaves it is `CategoryTheory.Functor.sheafPushforwardContinuous`, which is that same
precomposition, landing in sheaves by `CategoryTheory.Functor.op_comp_isSheaf`.

## References

* [Stacks Project, Tag 00YS](https://stacks.math.columbia.edu/tag/00YS)
-/

@[expose] public section

add_to_stacks 00YS "`u^p F (U) = F(u U)` on presheaves, i.e. precomposition with `u.op`"
  CategoryTheory.Functor.whiskeringLeft
add_to_stacks 00YS "`f_* F (U) = F(u U)` on sheaves, by the same rule"
  CategoryTheory.Functor.sheafPushforwardContinuous
