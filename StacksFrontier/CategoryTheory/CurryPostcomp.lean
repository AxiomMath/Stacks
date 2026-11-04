module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering

/-!
# Currying a functor on a product postcomposed with a functor

Let `G : C₁ ⥤ C₂ ⥤ D` be a bifunctor and `H : D ⥤ E`.  There are two ways to write
`(X₁, X₂) ↦ H((G X₁) X₂)` as a bifunctor: postcompose `G` with `H` in its value, which is
`G ⋙ (CategoryTheory.Functor.whiskeringRight C₂ D E).obj H`, or uncurry `G`, compose with `H` on
the product category, and curry again.  The two are the identity on every object but not
syntactically equal — currying a composite inserts a `CategoryTheory.Functor.map_id` in the first
variable and a `CategoryTheory.Functor.map_comp` in the second — so an isomorphism is needed.

This is the postcomposition counterpart of Mathlib's `CategoryTheory.Functor.curryObjProdComp`,
which does the same for *pre*composition by a product of functors, and the two-variable
counterpart of `CategoryTheory.Functor.curry_obj_uncurry_obj`.

It is what lets a closure property of a shift datum — which is stated for the whiskered spelling,
since that is the one a `CategoryTheory.Functor.whiskeringRight` makes visible — be transported to
the curried spelling, which is the one a transformation of functors on a product category is
curried into.

## Main results

* `CategoryTheory.Functor.curryObjUncurryObjCompIso`: the isomorphism.  Mathlib's own
  `CategoryTheory.Functor.curryObjCompIso` is the unrelated statement that currying commutes with
  postcomposition; the step this one adds is `curry_obj_uncurry_obj`, which is an equality of
  functors and so unusable for transporting a shift datum.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ v v' u₁ u₂ u u'

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u} {E : Type u'}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v} D] [Category.{v'} E]

/-- **Postcomposing a bifunctor with a functor is the currying of the postcomposite on the
product category.**  Both are `(X₁, X₂) ↦ H((G X₁) X₂)` on objects, by `Iso.refl`; the content is
the two naturality squares, where the `CategoryTheory.Functor.map_id` in the first variable and
the `CategoryTheory.Functor.map_comp` in the second that `CategoryTheory.Functor.curry.obj` of a
composite inserts are discharged. -/
@[simps!]
def curryObjUncurryObjCompIso (G : C₁ ⥤ C₂ ⥤ D) (H : D ⥤ E) :
    G ⋙ (whiskeringRight C₂ D E).obj H ≅ curry.obj (uncurry.obj G ⋙ H) :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))

end CategoryTheory.Functor

end
