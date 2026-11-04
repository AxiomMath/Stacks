module

public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functor of categories of elements induced by a morphism of presheaves

A morphism `m : F ⟶ G` of presheaves of sets on a category `C` induces a functor
`El F ⥤ El G` of their categories of elements (Stacks 02XV) over `C`: it keeps the base and
applies `m` to the element named.

Naming a section (`CategoryTheory.PresheafOfCategories.sectionOfObj`) through an equivalence
`e : p ≃ El F` over `C` only depends on the image of the object under the forward 1-morphism of
`e`, and `m` applied to that section is the section named by the image under `El m`. So if the
square of 1-morphisms
```text
   𝒮 --e_F--> El F
   |            |
   Φ          El m
   v            v
   𝒯 --e_G--> El G
```
commutes on the nose, then `m` carries the section named by `z` to the section named by `Φ z`.

## Main definitions

* `CategoryTheory.PresheafOfCategories.elementsMap`: the functor `El F ⥤ El G`.

## Main results

* `CategoryTheory.PresheafOfCategories.sectionOfObj_eq_of_obj_eq`: the section named by an object
  depends only on its image under the forward 1-morphism of the equivalence.
* `CategoryTheory.PresheafOfCategories.sectionOfObj_of_hom_functor_eq`: the same statement read
  against a given forward 1-morphism.
* `CategoryTheory.PresheafOfCategories.natTrans_app_sectionOfObj_of_comp_eq`: if the square above
  commutes, then `m` carries the section named by `z` to the section named by `Φ z`.
* `CategoryTheory.PresheafOfCategories.sectionOfObj_eq_map_eqToHom`: naming a section over `W`
  for a non-canonical identification of `W` is the restriction along that identification.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.PresheafOfCategories

universe v u a u₁ u₂ v₁ v₂

variable {C : Type u} [Category.{v} C]

section ElementsMap

variable {F G : Cᵒᵖ ⥤ Type a}

/-- The functor of categories of elements induced by a morphism `m : F ⟶ G` of presheaves of
sets: it keeps the base of an object and applies `m` to the element named. -/
@[sga "4 I 5.10"]
def elementsMap (m : F ⟶ G) :
    (presheafOfCategories (F ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (G ⋙ typeToCat)).obj where
  obj Z := ⟨Z.base, Discrete.mk (m.app (op Z.base) Z.fiber.as)⟩
  map {Z W} u := ⟨u.base, Discrete.eqToHom (by
    have h : Z.fiber.as = F.map u.base.op W.fiber.as := Discrete.eq_of_hom u.fiber
    change m.app (op Z.base) Z.fiber.as = G.map u.base.op (m.app (op W.base) W.fiber.as)
    rw [h, ← NatTrans.naturality_apply])⟩
  map_id _ := elements_hom_ext _ _ rfl
  map_comp _ _ := elements_hom_ext _ _ rfl

/-- `CategoryTheory.PresheafOfCategories.elementsMap` is strictly over `C`. -/
lemma elementsMap_comp_eq (m : F ⟶ G) :
    elementsMap m ⋙ (presheafOfCategories (G ⋙ typeToCat)).p =
      (presheafOfCategories (F ⋙ typeToCat)).p :=
  rfl

/-- The element named by the image of an object of a fibre under
`CategoryTheory.PresheafOfCategories.elementsMap` is the image under `m` of the element named by
that object. -/
lemma elementsFiberEquiv_elementsMap (m : F ⟶ G) {W : C}
    (x : (presheafOfCategories (F ⋙ typeToCat)).p.Fiber W) :
    m.app (op W) (elementsFiberEquiv F W x) =
      elementsFiberEquiv G W
        (⟨(elementsMap m).obj x.1, x.2⟩ :
          (presheafOfCategories (G ⋙ typeToCat)).p.Fiber W) := by
  obtain ⟨x, hx⟩ := x
  change (presheafOfCategories (F ⋙ typeToCat)).p.obj x = W at hx
  subst hx
  rfl

/-- The functor of categories of elements induced by a morphism of presheaves is faithful. -/
lemma faithful_elementsMap (m : F ⟶ G) : (elementsMap m).Faithful where
  map_injective {_ _} u w h := elements_hom_ext u w (congrArg (fun k => k.base) h)

/-- The functor of categories of elements induced by a morphism of presheaves with injective
components is full. -/
lemma full_elementsMap_of_injective (m : F ⟶ G)
    (hm : ∀ X : Cᵒᵖ, Function.Injective (m.app X)) : (elementsMap m).Full where
  map_surjective {Z W} f := by
    have hf : m.app (op Z.base) Z.fiber.as =
        G.map f.base.op (m.app (op W.base) W.fiber.as) := Discrete.eq_of_hom f.fiber
    have h : Z.fiber.as = F.map f.base.op W.fiber.as :=
      hm (op Z.base) (hf.trans (NatTrans.naturality_apply m f.base.op W.fiber.as).symm)
    exact ⟨⟨f.base, Discrete.eqToHom h⟩, elements_hom_ext _ _ rfl⟩

end ElementsMap

section Section

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒯 : Type u₂} [Category.{v₂} 𝒯]
  {p : 𝒮 ⥤ C} {q : 𝒯 ⥤ C} {F G : Cᵒᵖ ⥤ Type a}

/-- Naming a section only depends on the image of the object under the forward 1-morphism of the
equivalence. -/
lemma sectionOfObj_eq_of_obj_eq
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)
    (d : StacksRepresentableCFG.EquivalenceOver q (presheafOfCategories (F ⋙ typeToCat)).p)
    (z : 𝒮) (w : 𝒯) {W : C} (h : p.obj z = W) (h' : q.obj w = W)
    (hobj : e.hom.functor.obj z = d.hom.functor.obj w) :
    sectionOfObj e z h = sectionOfObj d w h' :=
  congrArg (elementsFiberEquiv F W) (Subtype.ext hobj)

/-- An equivalence whose forward 1-morphism is a given functor `K` names the section that the
image of the object under `K` carries. -/
lemma sectionOfObj_of_hom_functor_eq
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)
    (K : 𝒮 ⥤ (presheafOfCategories (F ⋙ typeToCat)).obj) (hK : e.hom.functor = K) (z : 𝒮)
    {W : C} (h : p.obj z = W) (hb : (presheafOfCategories (F ⋙ typeToCat)).p.obj (K.obj z) = W) :
    sectionOfObj e z h = elementsFiberEquiv F W ⟨K.obj z, hb⟩ :=
  congrArg (elementsFiberEquiv F W) (Subtype.ext (Functor.congr_obj hK z))

/-- Naming a section over `W` through an identification `h` of `W` with the image of the object is
the restriction along `h` of the section named over that image. -/
lemma sectionOfObj_eq_map_eqToHom
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)
    (z : 𝒮) {W : C} (h : p.obj z = W) :
    sectionOfObj e z h = F.map (eqToHom h.symm).op (sectionOfObj e z rfl) := by
  subst h
  simp

/-- If the forward 1-morphism of `e` followed by `El m` is a 1-morphism `Φ` followed by the
forward 1-morphism of `d`, then `m` carries the section named by `z` to the section named by
`Φ z`. -/
theorem natTrans_app_sectionOfObj_of_comp_eq (m : F ⟶ G)
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)
    (d : StacksRepresentableCFG.EquivalenceOver q (presheafOfCategories (G ⋙ typeToCat)).p)
    (Φ : 𝒮 ⥤ 𝒯) (hΦ : e.hom.functor ⋙ elementsMap m = Φ ⋙ d.hom.functor)
    (z : 𝒮) {W : C} (h : p.obj z = W) (h' : q.obj (Φ.obj z) = W) :
    m.app (op W) (sectionOfObj e z h) = sectionOfObj d (Φ.obj z) h' := by
  have h1 : m.app (op W) (sectionOfObj e z h) =
      elementsFiberEquiv G W (⟨(elementsMap m).obj (e.hom.functor.obj z),
        (Functor.congr_obj e.hom.w z).trans h⟩ :
          (presheafOfCategories (G ⋙ typeToCat)).p.Fiber W) :=
    elementsFiberEquiv_elementsMap m
      (⟨e.hom.functor.obj z, (Functor.congr_obj e.hom.w z).trans h⟩ :
        (presheafOfCategories (F ⋙ typeToCat)).p.Fiber W)
  rw [h1]
  exact congrArg (elementsFiberEquiv G W) (Subtype.ext (Functor.congr_obj hΦ z))

end Section

end CategoryTheory.PresheafOfCategories

end
