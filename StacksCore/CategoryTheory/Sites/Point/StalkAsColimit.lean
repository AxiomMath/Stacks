module

public import Mathlib.CategoryTheory.Sites.Point.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a presheaf at a point of a site

Let `(C, J)` be a site and `p` a point of it, given by a fibre functor `u : C ⥤ Type w`. A
*neighbourhood* of `p` is a pair `(U, x)` with `x ∈ u(U)`, and a morphism of neighbourhoods
`(V, y) ⟶ (U, x)` is a morphism `α : V ⟶ U` with `u(α)(y) = x`; these form the category of
elements `u.Elements`. Stacks 04EH defines the stalk of a presheaf `F` at `p` as
`F_p = colim_{{(U, x)}ᵒᵖ} F(U)`.

That is Mathlib's `CategoryTheory.GrothendieckTopology.Point.presheafFiber`, which is by
definition the colimit of `(CategoryOfElements.π Φ.fiber).op ⋙ F` over `Φ.fiber.Elementsᵒᵖ`. The
canonical map `F(U) ⟶ F_p` attached to a neighbourhood — the colimit injection — is
`Point.toPresheafFiber`, and its compatibility with morphisms of neighbourhoods is
`Point.toPresheafFiber_w`.

## References

* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
-/

@[expose] public section

add_to_stacks 04EH "the stalk `F_p = colim_{{(U, x)}ᵒᵖ} F(U)` of a presheaf at a point of a site"
  CategoryTheory.GrothendieckTopology.Point.presheafFiber
add_to_stacks 04EH "the canonical map `F(U) ⟶ F_p` attached to a neighbourhood `(U, x)` of the
  point" CategoryTheory.GrothendieckTopology.Point.toPresheafFiber
add_to_stacks 04EH "the canonical maps are compatible with morphisms of neighbourhoods"
  CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_w
