module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Basic definitions and constructions
This file contains the stacks tags from section 4.2: definitions. A lot of these should
probably be moved to their own file eventually.
-/

@[expose] public section

open CategoryTheory

add_to_stacks 0014 "the type / category of all categories" Cat

add_to_stacks 0016 "the identity morphism on an object" CategoryStruct.id
add_to_stacks 0016 "uniqueness of left identities" id_of_comp_left_id
add_to_stacks 0016 "uniqueness of right identities" id_of_comp_right_id

add_to_stacks 0017 "Prop-valued typeclass stating that a morphism is an isomorphism" IsIso

add_to_stacks 0018 "Prop-valued typeclass stating that a category is a groupoid" IsGroupoid
add_to_stacks 0018 "typeclass for groupoids, carrying an inverse to each morphism as data" Groupoid
add_to_stacks 0018 "the type / category of all groupoids" Grpd

@[stacks 0019 "with `f` the identity it follows that every one-object category is equivalent
to its endomorphism monoid, which for groupoids is a group by `CategoryTheory.End.group`"]
instance CategoryTheory.SingleObj.isEquivalence_functor {C : Type*} [Category* C]
    [Subsingleton C] {X : C} {M : Type*} [Monoid M] (f : M ≃* End X) :
    (functor f.toMonoidHom).IsEquivalence where
  full := ⟨f.surjective⟩
  faithful := ⟨fun h ↦ f.injective h⟩
  essSurj := ⟨fun _ ↦ ⟨star M, ⟨eqToIso <| Subsingleton.elim _ _⟩⟩⟩

add_to_stacks 001A CategoryTheory.instGroupoidDiscrete
add_to_stacks 001C "structure for fully faithful functors, carrying the preimage of each morphism
  as data" CategoryTheory.Functor.FullyFaithful
add_to_stacks 001D "predicate for strictly full subcategories"
  ObjectProperty.IsClosedUnderIsomorphisms

set_option backward.isDefEq.respectTransparency false in
@[stacks 001F]
lemma CategoryTheory.SingleObj.faithful_mapHom_iff {M N : Type*} [Monoid M] [Monoid N]
    {f : M →* N} : f.toFunctor.Faithful ↔ Function.Injective f :=
  ⟨fun h ↦ h.map_injective (X := star M) (Y := star M),
  fun h ↦ ⟨by simpa [MonoidHom.toFunctor, mapHom] using fun _ ↦ h⟩⟩

@[stacks 001F]
lemma CategoryTheory.SingleObj.full_mapHom_iff {M N : Type*} [Monoid M] [Monoid N]
    {f : M →* N} : f.toFunctor.Full ↔ Function.Surjective f :=
  ⟨fun h ↦ h.map_surjective (X := star M) (Y := star M),
  fun h ↦ ⟨by simpa [MonoidHom.toFunctor, mapHom] using fun _ ↦ h⟩⟩

add_to_stacks 001G Over.mapForget

add_to_stacks 001H Under
add_to_stacks 001H Under.forget
add_to_stacks 001H Under.map
add_to_stacks 001H Under.mapForget

add_to_stacks 001I NatTrans
add_to_stacks 001I NatTrans.id
add_to_stacks 001I NatTrans.vcomp
add_to_stacks 001I Functor.category

add_to_stacks 001J "Prop-valued typeclass stating that a functor is an equivalence"
  Functor.IsEquivalence
add_to_stacks 001J "constructor upgrading an equivalence to a half-adjoint equivalence with the
  the same functors" CategoryTheory.Equivalence.mk

/-- Constructs an equivalence of categories from a fully faithful functor `F`, a family of objects
`j : D → C` and a family of isomorphisms `i : ∀ X, X ≅ F.obj (j X)`. The constructed equivalence
has an inverse that agrees with `j` on objects and a counit with components given by `i`.
This is similar to `F.asEquivalence`, but gives more control over the resulting equivalence. -/
@[simps!, stacks 05SG, ega "0 8.1.5" "equivalence C₁ ≃ F(C₁)"]
def CategoryTheory.Equivalence.mkOfIsos {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    (hF : F.FullyFaithful) (j : D → C) (i : ∀ X, X ≅ F.obj (j X)) : C ≌ D :=
  .mk F {
    obj X := j X,
    map f := hF.preimage ((i _).inv ≫ f ≫ (i _).hom)
    map_comp f g := by simp [← hF.preimage_comp] }
  (NatIso.ofComponents (fun X ↦ hF.preimageIso (i (F.obj X))) (by
    simp [← Category.assoc, ← hF.preimage_comp]))
  (NatIso.ofComponents (fun X ↦ (i X).symm))

add_to_stacks 003E NatTrans.hcomp
