module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal endomorphism monoid of an object of a closed monoidal category

Let `C` be a closed monoidal category and let `X` be an object of `C`. The internal hom
`X ⟶[C] X` carries a canonical monoid structure: the unit is the internal identity
`MonoidalClosed.id X` and the multiplication is the internal composition
`MonoidalClosed.comp X X X`. The three monoid axioms are exactly the three axioms witnessing
that a closed monoidal category is enriched in itself.

When `C` is moreover symmetric there is a canonical comparison
`End X ⊗ End Y ⟶ End (X ⊗ Y)`, the external tensor product of endomorphisms, obtained by
currying

`(X ⊗ Y) ⊗ (End X ⊗ End Y) ⟶ (X ⊗ End X) ⊗ (Y ⊗ End Y) ⟶ X ⊗ Y`,

where the first map interleaves the four factors by `MonoidalCategory.tensorμ` and the second
evaluates in each variable. It is a morphism of monoid objects.

For `C` the category of sheaves of `𝒪_S`-modules on a scheme this is the endomorphism algebra
sheaf `End(E)` of a sheaf of modules `E`, together with the algebra map
`End(E) ⊗ End(F) ⟶ End(E ⊗ F)`; these are the source of the trivial classes in the Brauer group
of a scheme and of the transitivity of Brauer equivalence.

## Main definitions

* `CategoryTheory.MonoidalClosed.internalEndMonObj`: the monoid-object structure on
  `X ⟶[C] X`.
* `CategoryTheory.MonoidalClosed.internalEnd`: that monoid object, as an object of `Mon C`.
* `CategoryTheory.MonoidalClosed.tensorInternalEnd`: the comparison morphism
  `End X ⊗ End Y ⟶ End (X ⊗ Y)` in `C`, and
  `CategoryTheory.MonoidalClosed.tensorInternalEndHom` the same morphism in `Mon C`.
* `CategoryTheory.MonoidalClosed.tensorInternalEndIso`: the comparison as an isomorphism of
  monoid objects, when the underlying morphism is invertible.

## Main results

* `CategoryTheory.MonoidalClosed.internalEnd_X`,
  `CategoryTheory.MonoidalClosed.internalEnd_one` and
  `CategoryTheory.MonoidalClosed.internalEnd_mul` identify the underlying object, the unit and
  the multiplication of `internalEnd X` with the internal hom, the internal identity and the
  internal composition.
* `CategoryTheory.MonoidalClosed.isMonHom_tensorInternalEnd`: **the comparison morphism is a
  morphism of monoid objects**, i.e. it carries the internal identity of `X ⊗ Y` to the tensor
  product of the internal identities and is compatible with internal composition.
* `CategoryTheory.MonoidalClosed.uncurry_tensorInternalEnd`: the uncurried form of the
  comparison morphism.
* `CategoryTheory.MonoidalClosed.whiskerLeft_tensorHom_compTranspose`: uncurrying a tensor product
  of two morphisms into an internal endomorphism object evaluates the two factors in turn.

## Implementation notes

The monoid axioms of `internalEndMonObj` are not reproved. `MonoidalClosed.id_comp`,
`MonoidalClosed.comp_id` and `MonoidalClosed.assoc` state the unit and associativity laws of the
self-enrichment with a unitor or associator moved to the left-hand side, and
`CategoryTheory.Iso.inv_comp_eq` moves it back to the shape `MonObj` asks for.

The two `IsMonHom` fields are stated by instance search in terms of `MonObj.one` and `MonObj.mul`
of `MonoidalCategory.tensorObj`; those are definitionally the expressions of
`Mon.tensorObj_one` and `Mon.tensorObj_mul`, but not syntactically, so each proof opens with a
`show` that names the expression it is about. The unit law is then
`MonoidalCategory.tensor_right_unitality` and the multiplication law is
`MonoidalCategory.tensor_associativity` together with the naturality of
`MonoidalCategory.tensorμ` in its two left and its two right arguments.

Invertibility of the comparison is proved separately, in
`StacksFrontier.CategoryTheory.Monoidal.InternalEndTensorIso`: it holds when `X` and `Y` admit
duals, and that file reduces it to one identity between braidings, associators and the two
evaluations of the pairings. `tensorInternalEndIso` here takes `IsIso (tensorInternalEnd X Y)` as
a hypothesis, which `CategoryTheory.MonoidalClosed.isIso_tensorInternalEnd` supplies.

## References

* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
* [Stacks Project, Tag 0A2K](https://stacks.math.columbia.edu/tag/0A2K)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

/-- The internal hom `X ⟶[C] X` of an object of a closed monoidal category is a monoid object,
with the internal identity as unit and the internal composition as multiplication. -/
instance internalEndMonObj (X : C) : MonObj ((ihom X).obj X) where
  one := MonoidalClosed.id X
  mul := MonoidalClosed.comp X X X
  one_mul := by
    have h := MonoidalClosed.id_comp (C := C) X X
    rw [Iso.inv_comp_eq] at h
    simpa using h
  mul_one := by
    have h := MonoidalClosed.comp_id (C := C) X X
    rw [Iso.inv_comp_eq] at h
    simpa using h
  mul_assoc := by
    have h := MonoidalClosed.assoc (C := C) X X X X
    rw [Iso.inv_comp_eq] at h
    exact h

/-- The internal endomorphism monoid of an object of a closed monoidal category. -/
@[sga "3 I 1.7.2" "more general"]
abbrev internalEnd (X : C) : Mon C := Mon.mk ((ihom X).obj X)

/-- The underlying object of `internalEnd X` is the internal hom `X ⟶[C] X`. -/
@[simp]
lemma internalEnd_X (X : C) : (internalEnd X).X = (ihom X).obj X := rfl

/-- The unit of `internalEnd X` is the internal identity `MonoidalClosed.id X`. -/
@[simp]
lemma internalEnd_one (X : C) :
    MonObj.one (X := (internalEnd X).X) = MonoidalClosed.id X := rfl

/-- The multiplication of `internalEnd X` is the internal composition
`MonoidalClosed.comp X X X`. -/
@[simp]
lemma internalEnd_mul (X : C) :
    MonObj.mul (X := (internalEnd X).X) = MonoidalClosed.comp X X X := rfl

/-- Uncurrying a tensor product of two morphisms into the internal endomorphism object of `W`
evaluates the two factors in turn. -/
lemma whiskerLeft_tensorHom_compTranspose {W A B : C} (f : A ⟶ (ihom W).obj W)
    (g : B ⟶ (ihom W).obj W) :
    W ◁ (f ⊗ₘ g) ≫ compTranspose W W W
      = (α_ W A B).inv ≫ (uncurry f ▷ B) ≫ uncurry g := by
  simp only [compTranspose_eq, uncurry_eq, tensorHom_def, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_inv_naturality_middle_assoc, Functor.id_obj, comp_whiskerRight]

/-- An isomorphism `e : X ≅ Y` conjugates internal endomorphisms. -/
def internalEndCongrHom {X Y : C} (e : X ≅ Y) : (ihom X).obj X ⟶ (ihom Y).obj Y :=
  curry (e.inv ▷ (ihom X).obj X ≫ (ihom.ev X).app X ≫ e.hom)

/-- The uncurried form of `internalEndCongrHom e` is `e.inv`, followed by evaluation, followed by
`e.hom`. -/
@[simp]
lemma uncurry_internalEndCongrHom {X Y : C} (e : X ≅ Y) :
    uncurry (internalEndCongrHom e)
      = e.inv ▷ (ihom X).obj X ≫ (ihom.ev X).app X ≫ e.hom :=
  uncurry_curry _

/-- Conjugation by an isomorphism is a morphism of monoid objects. -/
instance isMonHom_internalEndCongrHom {X Y : C} (e : X ≅ Y) :
    IsMonHom (internalEndCongrHom e) where
  one_hom := by
    change MonoidalClosed.id X ≫ internalEndCongrHom e = MonoidalClosed.id Y
    apply uncurry_injective
    simp only [MonoidalClosed.id_eq, uncurry_natural_left, uncurry_internalEndCongrHom,
      uncurry_curry]
    rw [whisker_exchange_assoc, whiskerLeft_curry_ihom_ev_app_assoc]
    simp
  mul_hom := by
    change MonoidalClosed.comp X X X ≫ internalEndCongrHom e
      = (internalEndCongrHom e ⊗ₘ internalEndCongrHom e) ≫ MonoidalClosed.comp Y Y Y
    apply uncurry_injective
    simp only [MonoidalClosed.comp_eq, uncurry_natural_left, uncurry_internalEndCongrHom,
      uncurry_curry]
    rw [whisker_exchange_assoc, whiskerLeft_curry_ihom_ev_app_assoc,
      whiskerLeft_tensorHom_compTranspose, uncurry_internalEndCongrHom,
      MonoidalClosed.compTranspose_eq]
    simp only [comp_whiskerRight, Category.assoc, ← associator_inv_naturality_left_assoc]
    simp

/-- Conjugation is compatible with composition of isomorphisms. -/
lemma internalEndCongrHom_trans {X Y Z : C} (e : X ≅ Y) (e' : Y ≅ Z) :
    internalEndCongrHom e ≫ internalEndCongrHom e' = internalEndCongrHom (e ≪≫ e') := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_internalEndCongrHom, whisker_exchange_assoc,
    internalEndCongrHom, whiskerLeft_curry_ihom_ev_app_assoc, uncurry_internalEndCongrHom]
  simp

/-- Conjugation by the identity isomorphism is the identity. -/
@[simp]
lemma internalEndCongrHom_refl (X : C) :
    internalEndCongrHom (Iso.refl X) = 𝟙 ((ihom X).obj X) := by
  apply uncurry_injective
  rw [uncurry_internalEndCongrHom, MonoidalClosed.uncurry_id_eq_ev]
  simp

/-- **An isomorphism of objects induces an isomorphism of their internal endomorphism
monoids.** -/
def internalEndCongr {X Y : C} (e : X ≅ Y) : internalEnd X ≅ internalEnd Y where
  hom := Mon.Hom.mk' (internalEndCongrHom e) (IsMonHom.one_hom _) (IsMonHom.mul_hom _)
  inv := Mon.Hom.mk' (internalEndCongrHom e.symm) (IsMonHom.one_hom _) (IsMonHom.mul_hom _)
  hom_inv_id := by
    apply Mon.Hom.ext
    simpa using internalEndCongrHom_trans e e.symm
  inv_hom_id := by
    apply Mon.Hom.ext
    simpa using internalEndCongrHom_trans e.symm e

section Symmetric

variable [SymmetricCategory C]

/-- The external tensor product of endomorphisms `End X ⊗ End Y ⟶ End (X ⊗ Y)`: the curried
form of the map which interleaves the four factors of `(X ⊗ Y) ⊗ (End X ⊗ End Y)` and then
evaluates in each variable. -/
def tensorInternalEnd (X Y : C) :
    (ihom X).obj X ⊗ (ihom Y).obj Y ⟶ (ihom (X ⊗ Y)).obj (X ⊗ Y) :=
  curry (tensorμ X Y ((ihom X).obj X) ((ihom Y).obj Y) ≫
    ((ihom.ev X).app X ⊗ₘ (ihom.ev Y).app Y))

/-- The uncurried form of `tensorInternalEnd X Y` interleaves the four factors by `tensorμ` and
then evaluates in each variable. -/
@[simp]
lemma uncurry_tensorInternalEnd (X Y : C) :
    uncurry (tensorInternalEnd X Y) = tensorμ X Y ((ihom X).obj X) ((ihom Y).obj Y) ≫
      ((ihom.ev X).app X ⊗ₘ (ihom.ev Y).app Y) :=
  uncurry_curry _

/-- **The external tensor product of endomorphisms is a morphism of monoid objects.** It
carries the internal identity to the internal identity and internal composition to internal
composition. -/
instance isMonHom_tensorInternalEnd (X Y : C) : IsMonHom (tensorInternalEnd X Y) where
  one_hom := by
    change ((λ_ (𝟙_ C)).inv ≫ (MonoidalClosed.id X ⊗ₘ MonoidalClosed.id Y)) ≫
      tensorInternalEnd X Y = MonoidalClosed.id (X ⊗ Y)
    rw [Category.assoc]
    apply uncurry_injective
    simp only [uncurry_natural_left, uncurry_tensorInternalEnd, MonoidalClosed.id_eq,
      uncurry_curry, tensorμ_natural_right_assoc, tensorHom_comp_tensorHom,
      whiskerLeft_curry_ihom_ev_app]
    exact (tensor_right_unitality X Y).symm
  mul_hom := by
    change (tensorμ ((ihom X).obj X) ((ihom Y).obj Y) ((ihom X).obj X) ((ihom Y).obj Y) ≫
        (MonoidalClosed.comp X X X ⊗ₘ MonoidalClosed.comp Y Y Y)) ≫ tensorInternalEnd X Y
      = (tensorInternalEnd X Y ⊗ₘ tensorInternalEnd X Y) ≫
        MonoidalClosed.comp (X ⊗ Y) (X ⊗ Y) (X ⊗ Y)
    apply uncurry_injective
    simp only [uncurry_natural_left, uncurry_tensorInternalEnd, MonoidalClosed.comp_eq,
      uncurry_curry, Category.assoc, tensorμ_natural_right_assoc, tensorHom_comp_tensorHom,
      whiskerLeft_curry_ihom_ev_app]
    rw [whiskerLeft_tensorHom_compTranspose, uncurry_tensorInternalEnd, Iso.eq_inv_comp,
      ← tensor_associativity_assoc]
    simp only [tensorHom_comp_tensorHom, compTranspose_eq, Iso.hom_inv_id_assoc,
      comp_whiskerRight, Category.assoc]
    have h := tensorμ_natural_left ((ihom.ev X).app X) ((ihom.ev Y).app Y)
      ((ihom X).obj X) ((ihom Y).obj Y)
    rw [reassoc_of% h, tensorHom_comp_tensorHom]
    rfl

/-- The external tensor product of endomorphisms, as a morphism of monoid objects
`End X ⊗ End Y ⟶ End (X ⊗ Y)`. -/
def tensorInternalEndHom (X Y : C) : internalEnd X ⊗ internalEnd Y ⟶ internalEnd (X ⊗ Y) :=
  Mon.Hom.mk' (tensorInternalEnd X Y) (IsMonHom.one_hom _) (IsMonHom.mul_hom _)

/-- The underlying morphism of `tensorInternalEndHom X Y` is `tensorInternalEnd X Y`. -/
@[simp]
lemma tensorInternalEndHom_hom (X Y : C) :
    (tensorInternalEndHom X Y).hom = tensorInternalEnd X Y := rfl

/-- If `tensorInternalEnd X Y` is an isomorphism in `C`, then `tensorInternalEndHom X Y` is an
isomorphism of monoid objects. -/
instance isIso_tensorInternalEndHom (X Y : C) [h : IsIso (tensorInternalEnd X Y)] :
    IsIso (tensorInternalEndHom X Y) := by
  have : IsIso ((Mon.forget C).map (tensorInternalEndHom X Y)) := h
  exact isIso_of_reflects_iso _ (Mon.forget C)

/-- When the comparison morphism is invertible, `End X ⊗ End Y` and `End (X ⊗ Y)` are isomorphic
as monoid objects. -/
noncomputable def tensorInternalEndIso (X Y : C) [IsIso (tensorInternalEnd X Y)] :
    internalEnd X ⊗ internalEnd Y ≅ internalEnd (X ⊗ Y) :=
  asIso (tensorInternalEndHom X Y)

end Symmetric

end CategoryTheory.MonoidalClosed
