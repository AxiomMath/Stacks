module

public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The iso-comma category of two functors

The *iso-comma category* of two functors `F : A ⥤ C` and `G : B ⥤ C` is the full subcategory of
the comma category `Comma F G` on the objects whose comparison morphism is invertible. It is a
model for the `2`-fibre product `A ×_C B` of categories: an object is an object of `A`, an object
of `B`, and an isomorphism between their images in `C`, and a morphism is a pair of morphisms
making the evident square commute.

A functor into it is given by a pair of functors together with a natural isomorphism between
their composites with `F` and with `G`; this is `CategoryTheory.IsoComma.lift`, and the
isomorphism it is built from is recovered on each object as the comparison morphism.

## Main definitions

* `CategoryTheory.IsoComma`: the iso-comma category.
* `CategoryTheory.IsoComma.fst` and `CategoryTheory.IsoComma.snd`: its two projections.
* `CategoryTheory.IsoComma.lift`: the functor into it determined by two functors and a natural
  isomorphism.

## Implementation notes

An object carries its comparison isomorphism as data — the full-subcategory predicate is
`IsIso X.hom` on an object of the comma category — and a morphism is literally a morphism of the
comma category, so it satisfies the compatibility square automatically. That is why
`CategoryTheory.ObjectProperty.lift` is the whole of `CategoryTheory.IsoComma.lift`: the object
and morphism assignments land in the comma category, and the side condition holds because the
comparison morphism is a component of a natural *isomorphism*.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} [Category.{v₁} A] [Category.{v₂} B]
  [Category.{v₃} C]

/-- The iso-comma model for the `2`-fibre product of `F : A ⥤ C` and `G : B ⥤ C`: the full
subcategory of the comma category on the objects whose comparison morphism is an isomorphism. -/
@[sga "7 VI 2.6(b)"]
abbrev IsoComma (F : A ⥤ C) (G : B ⥤ C) :=
  (show ObjectProperty (Comma F G) from fun X ↦ IsIso X.hom).FullSubcategory

namespace IsoComma

variable (F : A ⥤ C) (G : B ⥤ C)

/-- The projection of the iso-comma category of `F` and `G` to the source of `F`. -/
abbrev fst : IsoComma F G ⥤ A :=
  ObjectProperty.ι (show ObjectProperty (Comma F G) from fun X ↦ IsIso X.hom) ⋙ Comma.fst F G

/-- The projection of the iso-comma category of `F` and `G` to the source of `G`. -/
abbrev snd : IsoComma F G ⥤ B :=
  ObjectProperty.ι (show ObjectProperty (Comma F G) from fun X ↦ IsIso X.hom) ⋙ Comma.snd F G

variable {D : Type u₄} [Category.{v₄} D]

/-- The functor into the iso-comma category of `F` and `G` determined by a functor `L : D ⥤ A`,
a functor `R : D ⥤ B` and a natural isomorphism `L ⋙ F ≅ R ⋙ G`. -/
def lift (L : D ⥤ A) (R : D ⥤ B) (e : L ⋙ F ≅ R ⋙ G) : D ⥤ IsoComma F G :=
  ObjectProperty.lift _
    { obj X := ⟨L.obj X, R.obj X, e.hom.app X⟩
      map f := ⟨L.map f, R.map f, e.hom.naturality f⟩
      map_id := by intro X; ext <;> simp
      map_comp := by intro X Y Z f g; ext <;> simp }
    fun _ ↦ inferInstance

/-- The first projection of `CategoryTheory.IsoComma.lift` is its first factor. -/
theorem lift_comp_fst (L : D ⥤ A) (R : D ⥤ B) (e : L ⋙ F ≅ R ⋙ G) :
    lift F G L R e ⋙ fst F G = L :=
  rfl

/-- The second projection of `CategoryTheory.IsoComma.lift` is its second factor. -/
theorem lift_comp_snd (L : D ⥤ A) (R : D ⥤ B) (e : L ⋙ F ≅ R ⋙ G) :
    lift F G L R e ⋙ snd F G = R :=
  rfl

/-- The comparison morphism of an object in the image of `CategoryTheory.IsoComma.lift` is the
component of the given natural isomorphism. -/
@[simp]
theorem lift_obj_hom (L : D ⥤ A) (R : D ⥤ B) (e : L ⋙ F ≅ R ⋙ G) (X : D) :
    ((lift F G L R e).obj X).obj.hom = e.hom.app X :=
  rfl

end IsoComma

end CategoryTheory

end
