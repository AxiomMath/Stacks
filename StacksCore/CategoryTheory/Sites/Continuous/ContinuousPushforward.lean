module

public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCore.Tactic.StacksAttribute

/-!
# The sheafified pushforward is left adjoint to the sheaf pushforward

Stacks 00WX says that along a continuous functor `u : C ⥤ D` the sheafified pushforward
`u_s : G ↦ (u_p G)^#` is left adjoint to the sheaf pushforward `u^s`.

All three are Mathlib's. `CategoryTheory.Functor.sheafPushforwardContinuous` is `u^s`;
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` is `u_s`, defined exactly as
`sheafToPresheaf ⋙ lan u.op ⋙ presheafToSheaf`, i.e. the sheafification of the left Kan extension
along `u.op`; and `CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` is
the adjunction, obtained by composing the left Kan extension adjunction with the sheafification
adjunction and restricting along the fully faithful inclusion of sheaves into presheaves.

## References

* [Stacks Project, Tag 00WX](https://stacks.math.columbia.edu/tag/00WX)
-/

@[expose] public section

add_to_stacks 00WX "the sheaf pushforward `u^s : Sh(D) ⥤ Sh(C)` along a continuous functor"
  CategoryTheory.Functor.sheafPushforwardContinuous
add_to_stacks 00WX "the sheafified pushforward `u_s : G ↦ (u_p G)^#`"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback
add_to_stacks 00WX "the sheafified pushforward is left adjoint to the sheaf pushforward"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
