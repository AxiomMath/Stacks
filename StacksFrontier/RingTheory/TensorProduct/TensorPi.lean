module

public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksFrontier.RingTheory.Module.FinitePresentation.TensorProductPi

/-!
# Tensoring with a finitely presented module commutes with arbitrary products

Mathlib's `TensorProduct.piRight` and `Algebra.TensorProduct.piRight` invert the canonical
comparison `N ⊗[R] (∀ i, M i) ⟶ ∀ i, N ⊗[R] M i` for a *finite* index type, with no hypothesis on
`N`. Dually, for a finitely presented `N` the same comparison is bijective for *every* family `M`,
with no hypothesis on the index type. That bijectivity is packaged here as a linear equivalence and
as an algebra equivalence.

## Main definitions

* `TensorProduct.piRightOfFinitePresentation`: the comparison as a linear equivalence
  `N ⊗[R] (∀ i, M i) ≃ₗ[S] ∀ i, N ⊗[R] M i`, for an arbitrary index type and a finitely
  presented `N`.
* `Algebra.TensorProduct.piRightOfFinitePresentation`: the same as an algebra equivalence.

## Main results

* `TensorProduct.bijective_piRightHom_of_finitePresentation`: the comparison map
  `TensorProduct.piRightHom` is bijective when the left tensor factor is finitely presented.

## Implementation notes

`Module.FinitePresentation.tfae_piRightHom_bijective` is stated for the comparison map with
scalars `R` on both sides, `TensorProduct.piRightHom R R N M`, and quantifies its test data over
the universe of `N`. The scalar extension to `TensorProduct.piRightHom R S N M` costs nothing:
the two maps have the same underlying function, which is checked here on pure tensors by
`piRightHom_apply_eq_of_tower`, so bijectivity transfers. The `Small.{u} R` side condition of the
source is discharged by `small_self`, every type here living in a single universe.

Both equivalences are built with `LinearEquiv.ofBijective` and `AlgEquiv.ofBijective`, so their
forward direction is the canonical comparison map itself, definitionally — not an unspecified
isomorphism.

## References

* [Stacks Project, Tag 059K](https://stacks.math.columbia.edu/tag/059K)
-/

@[expose] public noncomputable section

universe u

open scoped TensorProduct

namespace TensorProduct

variable (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  (N : Type u) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  {ι : Type u} (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The comparison map `N ⊗[R] (∀ i, M i) ⟶ ∀ i, N ⊗[R] M i` does not depend on the intermediate
ring of scalars: `TensorProduct.piRightHom R S N M` and `TensorProduct.piRightHom R R N M` have
the same underlying function. -/
theorem piRightHom_apply_eq_of_tower (x : N ⊗[R] (∀ i, M i)) :
    piRightHom R S N M x = piRightHom R R N M x := by
  induction x with
  | zero => simp
  | tmul n m => rfl
  | add x y hx hy => simp [hx, hy]

/-- **Tensoring with a finitely presented module commutes with arbitrary products.** The
comparison map `N ⊗[R] (∀ i, M i) ⟶ ∀ i, N ⊗[R] M i` is bijective for every family `M` when `N`
is a finitely presented `R`-module, with no finiteness hypothesis on the index type. This is
[Stacks, Tag 059K] (1) implies (2), with the scalars extended from `R` to `S`. -/
theorem bijective_piRightHom_of_finitePresentation [Module.FinitePresentation R N] :
    Function.Bijective (piRightHom R S N M) := by
  have key := ((Module.FinitePresentation.tfae_piRightHom_bijective R N).out 1 2).mp
    ‹Module.FinitePresentation R N›
  have h : Function.Bijective (piRightHom R R N M) := key ι M
  simpa [funext (piRightHom_apply_eq_of_tower R S N M)] using h

/-- **Tensoring with a finitely presented module commutes with arbitrary products**, as a linear
equivalence `N ⊗[R] (∀ i, M i) ≃ₗ[S] ∀ i, N ⊗[R] M i` whose forward direction is the canonical
comparison map `TensorProduct.piRightHom`. -/
def piRightOfFinitePresentation [Module.FinitePresentation R N] :
    N ⊗[R] (∀ i, M i) ≃ₗ[S] ∀ i, N ⊗[R] M i :=
  LinearEquiv.ofBijective (piRightHom R S N M)
    (bijective_piRightHom_of_finitePresentation R S N M)

/-- `TensorProduct.piRightOfFinitePresentation` acts as the comparison map
`TensorProduct.piRightHom`. -/
@[simp]
theorem piRightOfFinitePresentation_apply [Module.FinitePresentation R N]
    (x : N ⊗[R] (∀ i, M i)) :
    piRightOfFinitePresentation R S N M x = piRightHom R S N M x :=
  rfl

/-- `TensorProduct.piRightOfFinitePresentation` sends the pure tensor `x ⊗ₜ m` to the family
`fun j ↦ x ⊗ₜ m j`. -/
@[simp]
theorem piRightOfFinitePresentation_tmul [Module.FinitePresentation R N] (x : N)
    (m : ∀ i, M i) :
    piRightOfFinitePresentation R S N M (x ⊗ₜ m) = fun j ↦ x ⊗ₜ m j :=
  rfl

end TensorProduct

namespace Algebra.TensorProduct

variable (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  (A : Type u) [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {ι : Type u} (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

/-- **Tensoring with a finitely presented algebra commutes with arbitrary products**, as an
algebra equivalence `A ⊗[R] (∀ i, B i) ≃ₐ[S] ∀ i, A ⊗[R] B i` whose forward direction is the
canonical comparison map `Algebra.TensorProduct.piRightHom`. -/
def piRightOfFinitePresentation [Module.FinitePresentation R A] :
    A ⊗[R] (∀ i, B i) ≃ₐ[S] ∀ i, A ⊗[R] B i :=
  AlgEquiv.ofBijective (piRightHom R S A B)
    (_root_.TensorProduct.bijective_piRightHom_of_finitePresentation R S A B)

/-- `Algebra.TensorProduct.piRightOfFinitePresentation` sends the pure tensor `x ⊗ₜ f` to the
family `fun j ↦ x ⊗ₜ f j`. -/
@[simp]
theorem piRightOfFinitePresentation_tmul [Module.FinitePresentation R A] (x : A)
    (f : ∀ i, B i) :
    piRightOfFinitePresentation R S A B (x ⊗ₜ f) = fun j ↦ x ⊗ₜ f j :=
  rfl

end Algebra.TensorProduct

end
