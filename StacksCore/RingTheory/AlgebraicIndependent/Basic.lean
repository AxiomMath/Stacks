module

import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-! # Algebraic independence -/

@[expose] public section

/-- The image of an algebraically independent set under an injective `R`-algebra
homomorphism is algebraically independent. -/
theorem AlgebraicIndepOn.image
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {s : Set A}
    (hs : AlgebraicIndepOn R id s) {f : A →ₐ[R] B} (hf : Function.Injective f) :
    AlgebraicIndepOn R id (f '' s) :=
  AlgebraicIndependent.image <| hs.map' hf

@[simp] theorem algebraicIndependent_subtypeVal_iff
    (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] (s : Set A) :
    AlgebraicIndependent R (Subtype.val : s → A) ↔ AlgebraicIndepOn R id s := Iff.rfl
