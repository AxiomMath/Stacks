module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map into a left Kan extension of presheaves

Stacks 00VD says that for a functor `u : C ⥤ D` and a presheaf `F` on `C` there is a canonical
map `F(U) ⟶ u_p F (u U)`, compatible with the restriction maps of `F` and of `u_p F`.

All of this is Mathlib's. `u_p` is the left Kan extension `CategoryTheory.Functor.lan` along
`u.op` (Stacks 00VE), whose value at `V` is the colimit of `F` over the index category
`I^u_V = CostructuredArrow u.op V`, and the canonical map is the component at `U` of
`CategoryTheory.Functor.lanUnit`, the unit of `u_p ⊣ u^p`, which is the colimit injection at the
object `(U, 𝟙 (u U))` of `I^u_{u U}`; because that unit is a morphism of presheaves
`F ⟶ u^p u_p F`, the asserted compatibility with the restriction maps is exactly its
naturality, `CategoryTheory.NatTrans.naturality`. The refinement of the colimit formula to
presheaves of modules is `StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SiteUpColimit`.

## References

* [Stacks Project, Tag 00VD](https://stacks.math.columbia.edu/tag/00VD)
-/

@[expose] public section

add_to_stacks 00VD "the canonical map `F(U) ⟶ u_p F (u U)` is the unit of `u_p ⊣ u^p`"
  CategoryTheory.Functor.lanUnit
add_to_stacks 00VD "compatibility with the restriction maps is naturality of that unit"
  CategoryTheory.NatTrans.naturality
