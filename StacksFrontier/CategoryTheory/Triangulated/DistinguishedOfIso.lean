module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Transporting a distinguished triangle along isomorphisms of its objects

`CategoryTheory.Pretriangulated.isomorphic_distinguished` transports distinguishedness along an
isomorphism of triangles, which presupposes a candidate third morphism. In practice one has two
composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, a distinguished triangle `T`, isomorphisms of
`X`, `Y` and `Z` onto the three objects of `T`, and the two squares saying that the isomorphisms
intertwine `f` and `g` with the first two morphisms of `T`. The third morphism is then not given
but produced: it is the connecting morphism of `T` conjugated by the isomorphisms, and the third
square commutes automatically.

Sometimes only the *second* object has to move, and the three morphisms are then all given:
`CategoryTheory.Pretriangulated.distTriang_of_iso_obj₂` transports a distinguished triangle
along an isomorphism of its second object, with the two morphisms through that object and the
connecting morphism supplied rather than produced, each by an equation.

## Main results

* `CategoryTheory.Pretriangulated.exists_distinguished_of_iso`: a pair of composable morphisms
  isomorphic to the first two morphisms of a distinguished triangle is itself the start of a
  distinguished triangle.
* `CategoryTheory.Pretriangulated.distTriang_of_iso_obj₂`: a distinguished triangle stays
  distinguished after its second object is transported along an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Pretriangulated

/-- A pair of composable maps isomorphic to the first two maps of a distinguished triangle is
itself the start of a distinguished triangle. -/
public lemma exists_distinguished_of_iso
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (e₁ : X ≅ T.obj₁) (e₂ : Y ≅ T.obj₂) (e₃ : Z ≅ T.obj₃)
    (h₁ : f ≫ e₂.hom = e₁.hom ≫ T.mor₁)
    (h₂ : g ≫ e₃.hom = e₂.hom ≫ T.mor₂) :
    ∃ δ : Z ⟶ X⟦(1 : ℤ)⟧, Triangle.mk f g δ ∈ distTriang C := by
  refine ⟨e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧',
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e₁ e₂ e₃ h₁ h₂ ?_)⟩
  dsimp
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, e₁.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- A distinguished triangle stays distinguished after its second object is transported along an
isomorphism `e : T.obj₂ ≅ A`: the triangle on morphisms `a : T.obj₁ ⟶ A`, `b : A ⟶ T.obj₃` and
`c : T.obj₃ ⟶ T.obj₁⟦1⟧` is distinguished as soon as `a` and `b` are the first two morphisms of
`T` read through `e` and `c` is its connecting morphism. -/
public lemma distTriang_of_iso_obj₂
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) {A : C} (e : T.obj₂ ≅ A)
    (a : T.obj₁ ⟶ A) (b : A ⟶ T.obj₃)
    (c : T.obj₃ ⟶ (CategoryTheory.shiftFunctor C (1 : ℤ)).obj T.obj₁)
    (ha : a ≫ e.inv = T.mor₁) (hb : b = e.inv ≫ T.mor₂) (hc : c = T.mor₃) :
    Triangle.mk a b c ∈ distTriang C :=
  isomorphic_distinguished T hT _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
      (ha.trans (Category.id_comp _).symm) ((Category.comp_id _).trans hb)
      (by simpa using hc))

end CategoryTheory.Pretriangulated
