module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Basic constructions about subalgebras -/

@[expose] public section

/-- Users need to provide their own simp lemmas for `algebraMap` and `SMul`. -/
@[reducible] def Algebra.ofMapLE
    {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {R' : Subsemiring R} {S' : Subsemiring S} (h : R'.map (algebraMap R S) ≤ S') :
    Algebra R' S' := Subalgebra.algebra (R := R') <|
  { __ := S'
    algebraMap_mem' r := h ⟨r, r.2, rfl⟩ }

theorem IsScalarTower.ofMapLE {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {R' : Subsemiring R} {S' : Subsemiring S} (h : R'.map (algebraMap R S) ≤ S') :
    letI := Algebra.ofMapLE h
    IsScalarTower R' S' S :=
  letI := Algebra.ofMapLE h
  ⟨fun x y z ↦ smul_assoc x.1 y.1 z⟩

variable {R₀ R S A B : Type*} [CommSemiring R₀] [CommSemiring R] [CommSemiring S] [Semiring A]
  [Semiring B] [Algebra R₀ R] [Algebra R₀ S] [Algebra R A] [Algebra S B] [Algebra R₀ A]
  [Algebra R₀ B] [IsScalarTower R₀ R A] [IsScalarTower R₀ S B]

set_option backward.isDefEq.respectTransparency false in
/-- The center of an algebra is preserved under algebra isomorphisms. -/
@[simps!]
def Subalgebra.centerCongr (e : A ≃ₐ[R₀] B) : Subalgebra.center R A ≃ₐ[R₀]
    Subalgebra.center S B where
  __ := Subsemiring.centerCongr e.toRingEquiv
  commutes' r := by ext; simp

add_to_stacks 074A Subalgebra.algebra
add_to_stacks 074A Subalgebra.isScalarTower_mid
