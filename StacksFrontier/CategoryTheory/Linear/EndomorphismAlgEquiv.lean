module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Endomorphism algebras under a fully faithful linear functor, and under an isomorphism

In an `R`-linear category the endomorphisms of an object form an `R`-algebra: they are an
`R`-module because the category is `R`-linear, and composition is `R`-bilinear, so Mathlib's
`CategoryTheory.Linear` supplies `Algebra R (End X)`. A functor acts on endomorphisms by a monoid
homomorphism (`CategoryTheory.Functor.mapEnd`), which is a bijection when the functor is fully
faithful (`CategoryTheory.Functor.FullyFaithful.mulEquivEnd`). If moreover the functor is additive
and `R`-linear, that bijection is additive and carries `r • 𝟙 X` to `r • 𝟙 (F X)`, hence is an
isomorphism of `R`-algebras.

## Main definitions

* `CategoryTheory.Functor.FullyFaithful.algEquivEndOfFullyFaithful`: the isomorphism of
  `R`-algebras `End X ≃ₐ[R] End (F X)` attached to a fully faithful additive `R`-linear
  functor `F`.
* `CategoryTheory.Iso.endAlgEquiv`: the isomorphism of `R`-algebras `End X ≃ₐ[R] End Y` attached
  to an isomorphism `X ≅ Y`, namely conjugation by it.

## Implementation notes

The `R`-algebra structure on `End X` is Mathlib's `Algebra.ofModule` instance for an `R`-linear
category, for which `algebraMap R (End X) r` is `r • 𝟙 X`; this is what makes `commutes'` the
statement that `F` preserves the scalar multiples of identities, which is `Functor.map_smul`
together with `Functor.map_id`.

Mathlib's `CategoryTheory.Functor.FullyFaithful.mulEquivEnd` gives the multiplicative half; only
the underlying bijection is reused here, since its `map_mul'` field is `fun x y => F.map_comp y x`
either way.

Conjugation by an isomorphism exchanges the order of the two factors, because the product of
`End X` is composition written backwards: `f * g = g ≫ f`. That is why the multiplicativity of
`CategoryTheory.Iso.endAlgEquiv` is the cancellation `e.hom ≫ e.inv = 𝟙` inserted between the two
conjugates.
-/

@[expose] public section

open CategoryTheory

universe v v' u u' w

variable {R : Type w} [CommRing R] {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  {F : C ⥤ D} [F.Additive] [F.Linear R]

namespace CategoryTheory.Functor.FullyFaithful

/-- **A fully faithful additive `R`-linear functor identifies endomorphism `R`-algebras.** For
such a functor `F` and an object `X`, the map `f ↦ F f` is an isomorphism of `R`-algebras from
`End X` onto `End (F X)`: it is bijective because `F` is fully faithful, multiplicative because
`F` preserves composition and identities, additive because `F` is additive, and compatible with
the structure map `r ↦ r • 𝟙` because `F` is `R`-linear. -/
noncomputable def algEquivEndOfFullyFaithful (hF : F.FullyFaithful) (X : C) :
    End X ≃ₐ[R] End (F.obj X) where
  toFun f := .of (F.map f.asHom)
  invFun g := .of (hF.preimage g.asHom)
  left_inv f := by ext; simp
  right_inv g := by ext; simp
  map_add' f g := by ext; simp [End.add_asHom]
  map_mul' f g := by ext; simp
  commutes' r := by
    ext
    change F.map (r • 𝟙 X) = r • 𝟙 (F.obj X)
    simp

/-- The isomorphism of endomorphism algebras is the action of the functor on morphisms. -/
@[simp] theorem algEquivEndOfFullyFaithful_apply (hF : F.FullyFaithful) (X : C) (f : End X) :
    algEquivEndOfFullyFaithful (R := R) hF X f = .of (F.map f.asHom) :=
  rfl

end CategoryTheory.Functor.FullyFaithful

namespace CategoryTheory.Iso

variable {X Y : C}

/-- **An isomorphism identifies endomorphism `R`-algebras.** For an isomorphism `e : X ≅ Y` of
objects of an `R`-linear category, conjugation `f ↦ e⁻¹ ∘ f ∘ e` is an isomorphism of `R`-algebras
`End X ≃ₐ[R] End Y`: it is bijective with conjugation by `e⁻¹` as its inverse, multiplicative
because the two inner isomorphisms cancel, additive because composition is bilinear, and it
carries `r • 𝟙 X` to `r • 𝟙 Y`.

This is what transports an identification of `A` with the endomorphism algebra of an object along
a chosen isomorphism of that object, as in the proofs of [Stacks, Tag 09S8] and
[Stacks, Tag 09SA], where a compact generator is replaced by a quasi-isomorphic model. -/
noncomputable def endAlgEquiv (e : X ≅ Y) : End X ≃ₐ[R] End Y where
  toFun f := .of (e.inv ≫ f.asHom ≫ e.hom)
  invFun g := .of (e.hom ≫ g.asHom ≫ e.inv)
  left_inv f := by ext; simp
  right_inv g := by ext; simp
  map_mul' f g := by ext; simp
  map_add' f g := by
    ext
    simp [End.add_asHom, Preadditive.add_comp, Preadditive.comp_add]
  commutes' r := by
    ext
    change e.inv ≫ (r • 𝟙 X) ≫ e.hom = r • 𝟙 Y
    simp

/-- The isomorphism of endomorphism algebras attached to an isomorphism is conjugation by it. -/
@[simp] theorem endAlgEquiv_apply (e : X ≅ Y) (f : End X) :
    endAlgEquiv (R := R) e f = .of (e.inv ≫ f.asHom ≫ e.hom) :=
  rfl

end CategoryTheory.Iso

end
