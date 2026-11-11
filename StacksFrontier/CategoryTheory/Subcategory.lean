module

public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute

/-!
# Subcategories

A subcategory of a category `C` (Stacks 001D (a)) is a set of objects of `C` together with a
set of arrows of `C`, every arrow having its source and target among the objects, which contains
the identity of each of its objects and is closed under composition. It is a category with the
source, target, composition and identities of `C`. The subcategory is full (Stacks 001D (b)) if
it contains every arrow of `C` between two of its objects, and strictly full (Stacks 001D (c)) if
moreover every object of `C` isomorphic to one of its objects is one of its objects.

Mathlib has no single structure for this notion: it has full subcategories
(`CategoryTheory.ObjectProperty.FullSubcategory`) and wide subcategories
(`CategoryTheory.WideSubcategory`). A subcategory is the same as a property of objects together
with a multiplicative morphism property on the corresponding full subcategory, that is a wide
subcategory of a full subcategory; this file proves that correspondence.

## Main definitions

* `CategoryTheory.Subcategory`: a subcategory of `C`, Stacks 001D (a).
* `CategoryTheory.Subcategory.Obj`: the category it defines, with inclusion functor
  `CategoryTheory.Subcategory.ι`.
* `CategoryTheory.Subcategory.IsFull`: full subcategories, Stacks 001D (b).
* `CategoryTheory.Subcategory.IsStrictlyFull`: strictly full subcategories, Stacks 001D (c).

## Main results

* `CategoryTheory.Subcategory.isFull_iff_full_ι`: a subcategory is full if and only if its
  inclusion functor, which is always faithful, is full.
* `CategoryTheory.Subcategory.isFull_iff_eq_ofObjectProperty`: a full subcategory is determined
  by its objects.
* `CategoryTheory.Subcategory.equivFullSubcategory`: the category of a full subcategory is
  equivalent to Mathlib's `ObjectProperty.FullSubcategory` of its objects.
* `CategoryTheory.Subcategory.equivWideSubcategory`: the category of a subcategory is equivalent
  to the wide subcategory, given by its arrows, of the full subcategory on its objects.
* `CategoryTheory.Subcategory.ofWide_fullHom` and `CategoryTheory.Subcategory.fullHom_ofWide`:
  subcategories correspond bijectively to pairs of a property of objects and a multiplicative
  morphism property on its full subcategory.

## References

* [Stacks Project, Tag 001D](https://stacks.math.columbia.edu/tag/001D)
-/

@[expose] public section

universe v u

namespace CategoryTheory

/-- A subcategory of a category `C`: a set `obj` of objects of `C` and a set `hom` of arrows of
`C` such that the source and target of every arrow in `hom` lie in `obj`, the identity of every
object in `obj` lies in `hom`, and `hom` is closed under composition. -/
@[ext, stacks 001D "(a) subcategory: subsets of the objects and of the arrows, arrows having
source and target among the objects, containing the identities of its objects and closed under
composition; its category structure is `CategoryTheory.Subcategory.category`"]
structure Subcategory (C : Type u) [Category.{v} C] where
  /-- The objects of the subcategory. -/
  obj : ObjectProperty C
  /-- The arrows of the subcategory. -/
  hom : MorphismProperty C
  /-- The source of an arrow of the subcategory is an object of the subcategory. -/
  obj_of_hom_left : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), hom f → obj X
  /-- The target of an arrow of the subcategory is an object of the subcategory. -/
  obj_of_hom_right : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), hom f → obj Y
  /-- The identity of an object of the subcategory is an arrow of the subcategory. -/
  id_mem : ∀ ⦃X : C⦄, obj X → hom (𝟙 X)
  /-- The arrows of the subcategory are closed under composition. -/
  comp_mem : ∀ ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z), hom f → hom g → hom (f ≫ g)

namespace Subcategory

variable {C : Type u} [Category.{v} C] (S : Subcategory C)

/-- The objects of the category defined by a subcategory `S`: the objects of `C` in `S`. -/
@[ext]
structure Obj where
  /-- The underlying object of `C`. -/
  obj : C
  /-- The object lies in the subcategory. -/
  property : S.obj obj

variable {S}

/-- The morphisms of the category defined by a subcategory `S`: the arrows of `C` in `S`. -/
@[ext]
structure Hom (X Y : S.Obj) where
  /-- The underlying arrow of `C`. -/
  hom : X.obj ⟶ Y.obj
  /-- The arrow lies in the subcategory. -/
  property : S.hom hom

/-- The category defined by a subcategory, with the source, target, composition and identities
of the ambient category. -/
instance category : Category.{v} S.Obj where
  Hom := Hom
  id X := ⟨𝟙 X.obj, S.id_mem X.property⟩
  comp f g := ⟨f.hom ≫ g.hom, S.comp_mem _ _ f.property g.property⟩
  id_comp f := Hom.ext (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _)

@[ext]
lemma hom_ext {X Y : S.Obj} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
lemma id_hom (X : S.Obj) : Hom.hom (𝟙 X) = 𝟙 X.obj := rfl

@[simp]
lemma comp_hom {X Y Z : S.Obj} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

variable (S)

/-- The inclusion functor of a subcategory into the ambient category. -/
@[simps]
def ι : S.Obj ⥤ C where
  obj X := X.obj
  map f := f.hom

instance faithful_ι : S.ι.Faithful where
  map_injective h := hom_ext h

/-- A subcategory is full if it contains every arrow of the ambient category between two of its
objects, so that its morphisms between two of its objects are all those of the ambient
category. -/
@[stacks 001D "(b) full subcategory: every arrow of the ambient category between two objects of
the subcategory is in the subcategory"]
def IsFull : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), S.obj X → S.obj Y → S.hom f

/-- A subcategory is strictly full if it is full and every object of the ambient category
isomorphic to an object of the subcategory is an object of the subcategory. -/
@[stacks 001D "(c) strictly full subcategory: full, and every object of the ambient category
isomorphic to an object of the subcategory is in the subcategory"]
def IsStrictlyFull : Prop :=
  S.IsFull ∧ S.obj.IsClosedUnderIsomorphisms

/-- A subcategory is full if and only if its inclusion functor is full. The inclusion is always
faithful, by `CategoryTheory.Subcategory.faithful_ι`. -/
theorem isFull_iff_full_ι : S.IsFull ↔ S.ι.Full := by
  constructor
  · intro h
    exact ⟨fun {X Y} f ↦ ⟨⟨f, h f X.property Y.property⟩, rfl⟩⟩
  · intro h X Y f hX hY
    obtain ⟨g, hg⟩ := h.map_surjective (X := (⟨X, hX⟩ : S.Obj)) (Y := ⟨Y, hY⟩) f
    rw [← hg]
    exact g.property

/-- The full subcategory of `C` on the objects satisfying `P`: its arrows are all the arrows of
`C` between two objects satisfying `P`. -/
@[simps]
def ofObjectProperty (P : ObjectProperty C) : Subcategory C where
  obj := P
  hom := fun X Y _ ↦ P X ∧ P Y
  obj_of_hom_left _ _ _ h := h.1
  obj_of_hom_right _ _ _ h := h.2
  id_mem _ h := ⟨h, h⟩
  comp_mem _ _ _ _ _ hf hg := ⟨hf.1, hg.2⟩

lemma isFull_ofObjectProperty (P : ObjectProperty C) : (ofObjectProperty P).IsFull :=
  fun _ _ _ hX hY ↦ ⟨hX, hY⟩

/-- A subcategory is full if and only if it is the full subcategory on its objects. In
particular full subcategories correspond to properties of objects. -/
theorem isFull_iff_eq_ofObjectProperty : S.IsFull ↔ S = ofObjectProperty S.obj := by
  constructor
  · intro h
    ext1
    · rfl
    · exact MorphismProperty.ext _ _ fun X Y f ↦
        ⟨fun hf ↦ ⟨S.obj_of_hom_left f hf, S.obj_of_hom_right f hf⟩,
          fun hf ↦ h f hf.1 hf.2⟩
  · intro h
    rw [h]
    exact isFull_ofObjectProperty _

/-- The category of a full subcategory is equivalent to Mathlib's full subcategory on its
objects, by functors that are the identity on underlying objects and arrows. -/
@[simps! functor_obj_obj inverse_obj_obj]
def equivFullSubcategory (h : S.IsFull) : S.Obj ≌ S.obj.FullSubcategory where
  functor :=
    { obj X := ⟨X.obj, X.property⟩
      map f := ObjectProperty.homMk f.hom }
  inverse :=
    { obj X := ⟨X.obj, X.property⟩
      map {X Y} f := ⟨f.hom, h f.hom X.property Y.property⟩ }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The arrows of a subcategory, as a morphism property of the full subcategory on its
objects. -/
def fullHom : MorphismProperty S.obj.FullSubcategory :=
  fun _ _ f ↦ S.hom f.hom

instance : S.fullHom.IsMultiplicative where
  id_mem X := S.id_mem X.property
  comp_mem f g hf hg := S.comp_mem f.hom g.hom hf hg

/-- The category of a subcategory is equivalent to the wide subcategory, given by its arrows,
of the full subcategory on its objects, by functors that are the identity on underlying objects
and arrows. -/
@[simps! functor_obj_obj_obj inverse_obj_obj]
def equivWideSubcategory : S.Obj ≌ WideSubcategory S.fullHom where
  functor :=
    { obj X := ⟨⟨X.obj, X.property⟩⟩
      map f := ⟨ObjectProperty.homMk f.hom, f.property⟩ }
  inverse :=
    { obj X := ⟨X.obj.obj, X.obj.property⟩
      map f := ⟨f.hom.hom, f.property⟩ }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The subcategory of `C` given by a property `P` of objects and a multiplicative morphism
property `Q` of the full subcategory on `P`: its arrows are the arrows of `C` between objects
satisfying `P` which satisfy `Q`. -/
def ofWide (P : ObjectProperty C) (Q : MorphismProperty P.FullSubcategory)
    [Q.IsMultiplicative] : Subcategory C where
  obj := P
  hom X Y f := ∃ (hX : P X) (hY : P Y),
    Q (ObjectProperty.homMk f : (⟨X, hX⟩ : P.FullSubcategory) ⟶ ⟨Y, hY⟩)
  obj_of_hom_left _ _ _ h := h.1
  obj_of_hom_right _ _ _ h := h.2.1
  id_mem X hX := ⟨hX, hX, Q.id_mem (⟨X, hX⟩ : P.FullSubcategory)⟩
  comp_mem _ _ _ _ _ hf hg := by
    obtain ⟨hX, hY, hf⟩ := hf
    obtain ⟨_, hZ, hg⟩ := hg
    exact ⟨hX, hZ, Q.comp_mem _ _ hf hg⟩

@[simp]
lemma ofWide_obj (P : ObjectProperty C) (Q : MorphismProperty P.FullSubcategory)
    [Q.IsMultiplicative] : (ofWide P Q).obj = P := rfl

/-- A subcategory is recovered from its objects and the multiplicative morphism property of its
arrows on the full subcategory of its objects. -/
theorem ofWide_fullHom : ofWide S.obj S.fullHom = S := by
  ext1
  · rfl
  · exact MorphismProperty.ext _ _ fun X Y f ↦
      ⟨fun ⟨_, _, hf⟩ ↦ hf, fun hf ↦ ⟨S.obj_of_hom_left f hf, S.obj_of_hom_right f hf, hf⟩⟩

/-- A property of objects and a multiplicative morphism property on its full subcategory are
recovered from the subcategory they define. -/
theorem fullHom_ofWide (P : ObjectProperty C) (Q : MorphismProperty P.FullSubcategory)
    [Q.IsMultiplicative] : (ofWide P Q).fullHom = Q :=
  MorphismProperty.ext _ _ fun X Y f ↦
    ⟨fun ⟨_, _, hf⟩ ↦ hf, fun hf ↦ ⟨X.property, Y.property, hf⟩⟩

end Subcategory

end CategoryTheory
