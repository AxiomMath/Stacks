module

public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# The category of isomorphism classes of 1-morphisms of a bicategory

In a bicategory `C` composition of 1-morphisms is associative and unital only up to the
associator and the unitors, so the objects and 1-morphisms of `C` do not form a category.
Replacing each 1-morphism by its isomorphism class in the hom-category repairs this: the
associator and the unitors become equalities of classes, and the result is an honest category
with the same objects.

This is the passage from a 2-category to a category that Stacks 04ZQ performs for the
2-category `Spaces/𝒴` of 1-morphisms to an algebraic stack representable by algebraic spaces,
and in which Stacks 050R then states the group-object condition. It is carried out here for an
arbitrary bicategory, since nothing beyond the bicategory axioms is used.

## Main definitions

* `CategoryTheory.Bicategory.homIsoSetoid`: isomorphism of 1-morphisms, as a setoid on a
  hom-type.
* `CategoryTheory.Bicategory.IsoClassCategory`: the objects of `C`, carrying the category
  structure whose morphisms are the isomorphism classes of 1-morphisms of `C`.
* `CategoryTheory.Bicategory.IsoClassCategory.homMk`: the class of a 1-morphism.

## Main results

* `CategoryTheory.Bicategory.IsoClassCategory.homMk_eq_iff`: two 1-morphisms have the same
  class exactly when they are isomorphic.
* `CategoryTheory.Bicategory.IsoClassCategory.homMk_id` and
  `CategoryTheory.Bicategory.IsoClassCategory.homMk_comp`: taking classes is compatible with
  identities and composition.
* `CategoryTheory.Bicategory.IsoClassCategory.homMk_surjective`: every morphism is the class of
  a 1-morphism.

## Implementation notes

`CategoryTheory.Bicategory.IsoClassCategory C` is a type synonym for `C`, so that the category
structure defined here does not compete with the `CategoryTheory.CategoryStruct` the bicategory
structure of `C` already provides. The setoid is passed explicitly rather than registered as an
instance, so that no `Setoid` instance on a hom-type of a bicategory is introduced.
-/

@[expose] public section

namespace CategoryTheory.Bicategory

universe w v u

variable {C : Type u} [Bicategory.{w, v} C]

/-- Isomorphism of 1-morphisms, as a setoid on a hom-type of a bicategory: two 1-morphisms are
equivalent when the hom-category contains an isomorphism between them. -/
def homIsoSetoid (a b : C) : Setoid (a ⟶ b) where
  r f g := Nonempty (f ≅ g)
  iseqv :=
    { refl := fun f => ⟨Iso.refl f⟩
      symm := fun h => ⟨(Classical.choice h).symm⟩
      trans := fun h k => ⟨Classical.choice h ≪≫ Classical.choice k⟩ }

/-- Composition of 1-morphisms respects isomorphism in both arguments: the comparison
isomorphism is built by whiskering. -/
def homIso_comp {a b c : C} {f f' : a ⟶ b} {g g' : b ⟶ c} (e : f ≅ f') (d : g ≅ g') :
    f ≫ g ≅ f' ≫ g' :=
  whiskerRightIso e g ≪≫ whiskerLeftIso f' d

/-- The objects of a bicategory `C`, with the 1-morphisms of `C` taken up to isomorphism. This
is a category: the associator and the unitors of `C` become equalities of isomorphism
classes. -/
def IsoClassCategory (C : Type u) [Bicategory.{w, v} C] : Type u := C

namespace IsoClassCategory

/-- An object of a bicategory, read as an object of the category of isomorphism classes of its
1-morphisms. -/
def mk (a : C) : IsoClassCategory C := a

/-- The object of the bicategory underlying an object of the category of isomorphism classes of
its 1-morphisms. -/
def obj (a : IsoClassCategory C) : C := a

/-- The underlying object of `mk a` is `a`. -/
@[simp]
theorem obj_mk (a : C) : obj (mk a) = a := rfl

/-- An object of `IsoClassCategory C` is `mk` of its underlying object. -/
@[simp]
theorem mk_obj (a : IsoClassCategory C) : mk (obj a) = a := rfl

/-- The category with the objects of `C` and with the isomorphism classes of 1-morphisms of `C`
as morphisms. -/
instance category : Category.{v} (IsoClassCategory C) where
  Hom a b := Quotient (homIsoSetoid (obj a) (obj b))
  id a := Quotient.mk _ (𝟙 (obj a))
  comp {a _ c} u v :=
    Quotient.liftOn₂ u v (fun f g => Quotient.mk (homIsoSetoid (obj a) (obj c)) (f ≫ g))
      (fun _ _ _ _ hf hg =>
        Quotient.sound ⟨homIso_comp (Classical.choice hf) (Classical.choice hg)⟩)
  id_comp u := Quotient.inductionOn u fun f => Quotient.sound ⟨λ_ f⟩
  comp_id u := Quotient.inductionOn u fun f => Quotient.sound ⟨ρ_ f⟩
  assoc u v w := Quotient.inductionOn₃ u v w fun f g k => Quotient.sound ⟨α_ f g k⟩

/-- The isomorphism class of a 1-morphism of `C`, as a morphism of the category of isomorphism
classes. -/
def homMk {a b : C} (f : a ⟶ b) : mk a ⟶ mk b := Quotient.mk _ f

/-- Every morphism of the category of isomorphism classes is the class of a 1-morphism. -/
theorem homMk_surjective {a b : C} (u : mk a ⟶ mk b) : ∃ f : a ⟶ b, homMk f = u :=
  Quotient.inductionOn u fun f => ⟨f, rfl⟩

/-- **Two 1-morphisms have the same isomorphism class exactly when they are isomorphic.** -/
theorem homMk_eq_iff {a b : C} (f g : a ⟶ b) : homMk f = homMk g ↔ Nonempty (f ≅ g) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Isomorphic 1-morphisms have the same class. -/
theorem homMk_eq_of_iso {a b : C} {f g : a ⟶ b} (e : f ≅ g) : homMk f = homMk g :=
  (homMk_eq_iff f g).2 ⟨e⟩

/-- The class of the identity 1-morphism of `a` is the identity morphism of `mk a`. -/
@[simp]
theorem homMk_id (a : C) : homMk (𝟙 a) = 𝟙 (mk a) := rfl

/-- The class of a composite of 1-morphisms is the composite of their classes. -/
@[simp]
theorem homMk_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    homMk (f ≫ g) = homMk f ≫ homMk g := rfl

end IsoClassCategory

end CategoryTheory.Bicategory

end
