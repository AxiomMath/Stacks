module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map out of a right Kan extension of presheaves

Stacks 00XG says that for a functor `u : C ⥤ D` and a presheaf `F` on `C` there is a canonical
map `{}_p u F (u U) ⟶ F(U)`, compatible with the restriction maps of `F` and of `{}_p u F`.

All of this is Mathlib's. `{}_p u` is the right Kan extension `CategoryTheory.Functor.ran`
along `u.op` (Stacks 00XH), and the canonical map is the component at `U` of
`CategoryTheory.Functor.ranCounit`, the counit of `u^p ⊣ {}_p u`; because that counit is a
morphism of presheaves `{}_p u F ∘ u ⟶ F`, the asserted compatibility with the restriction maps
is exactly its naturality, `CategoryTheory.NatTrans.naturality`.

## References

* [Stacks Project, Tag 00XG](https://stacks.math.columbia.edu/tag/00XG)
-/

@[expose] public section

add_to_stacks 00XG "the canonical map `{}_p u F (u U) ⟶ F(U)` is the counit of `u^p ⊣ {}_p u`"
  CategoryTheory.Functor.ranCounit
add_to_stacks 00XG "compatibility with the restriction maps is naturality of that counit"
  CategoryTheory.NatTrans.naturality
add_to_ega "0 8.2.1" "more general" CategoryTheory.NatTrans.naturality
