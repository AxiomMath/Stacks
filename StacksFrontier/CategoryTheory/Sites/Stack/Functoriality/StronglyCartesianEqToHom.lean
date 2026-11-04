module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-! # `IsStronglyCartesian` and `eqToHom` on the base

The pushforward of a fibred category along `u : 𝒞 ⥤ 𝒟` is built from the strict pullback
`u^p𝒮`, whose objects carry an *equality* `p y = u U` rather than an isomorphism. Every
base morphism read off from that data therefore comes decorated with `eqToHom`s, and the
cartesianness of a morphism has to be moved across them in both directions.

Since an `eqToHom` decoration is erased by `subst`, all four statements are immediate; they
are collected here rather than restated wherever they are needed.

## Main results

* `CategoryTheory.Functor.IsStronglyCartesian.eqToHom_comp`,
  `CategoryTheory.Functor.IsStronglyCartesian.eqToHom_comp_eqToHom`, decorating the base
  morphism;
* `CategoryTheory.Functor.IsStronglyCartesian.of_eqToHom_comp`,
  `CategoryTheory.Functor.IsStronglyCartesian.of_comp_eqToHom`, undecorating it.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮] {p : 𝒮 ⥤ 𝒞}

namespace Functor.IsStronglyCartesian

/-- Prepending an `eqToHom` to the base morphism preserves `IsStronglyCartesian`. -/
lemma eqToHom_comp {R R' S : 𝒞} {a b : 𝒮} (hR : R' = R) (f : R ⟶ S)
    (φ : a ⟶ b) (hf : p.IsStronglyCartesian f φ) :
    p.IsStronglyCartesian (eqToHom hR ≫ f) φ := by
  subst hR; simpa using hf

/-- Prepending an `eqToHom` to the base morphism reflects `IsStronglyCartesian`. -/
lemma of_eqToHom_comp {R R' S : 𝒞} {a b : 𝒮} (hR : R' = R) (f : R ⟶ S)
    (φ : a ⟶ b) (hf : p.IsStronglyCartesian (eqToHom hR ≫ f) φ) :
    p.IsStronglyCartesian f φ := by
  subst hR; simpa using hf

/-- Composing the base morphism with `eqToHom`s on both sides preserves `IsStronglyCartesian`. -/
lemma eqToHom_comp_eqToHom {R S R' S' : 𝒞} {a b : 𝒮} (hR : R' = R) (hS : S = S') (f : R ⟶ S)
    (φ : a ⟶ b) (hf : p.IsStronglyCartesian f φ) :
    p.IsStronglyCartesian (eqToHom hR ≫ f ≫ eqToHom hS) φ := by
  subst hR; subst hS; simpa using hf

/-- Appending an `eqToHom` to the base morphism reflects `IsStronglyCartesian`. -/
lemma of_comp_eqToHom {R S S' : 𝒞} {a b : 𝒮} (hS : S = S') (f : R ⟶ S) (φ : a ⟶ b)
    (hf : p.IsStronglyCartesian (f ≫ eqToHom hS) φ) : p.IsStronglyCartesian f φ := by
  subst hS; simpa using hf

end Functor.IsStronglyCartesian

end CategoryTheory
