module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.SetTheory.Cardinal.NatCard
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndomorphismAlgebra

/-!
# Skolem--Noether for a matrix algebra over a local ring

Over a field, every algebra automorphism of a matrix algebra is conjugation by an invertible
matrix; Mathlib has this in the form `AlgEquiv.eq_linearEquivConjAlgEquiv`, for the endomorphism
algebra of a projective module over a semifield. The same statement holds over a *commutative
local ring*: the only thing the field was used for is that a nonzero element of the base ring is
invertible, and over a local ring a rank-one operator still has a matrix coefficient outside the
maximal ideal, because the rank-one projections of a basis sum to the identity and are conjugate
to one another, so they cannot all die in the residue field.

## Main results

* `Stacks.exists_conjAlgEquiv_eq_of_basis`: if `R` is a commutative local ring and `P` is a free
  `R`-module with a basis indexed by a nonempty finite type, every algebra automorphism of
  `Module.End R P` is `T.conjAlgEquiv R` for some `T : P ≃ₗ[R] P`.
* `Stacks.Matrix.exists_units_conj_eq_of_algEquiv`: consequently every algebra automorphism of
  `Matrix I I R`, for `I` a nonempty finite type and `R` a commutative local ring, is conjugation
  by a unit of `Matrix I I R`.

## Implementation notes

The module-theoretic core is already proved in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BrauerGroupScheme/EndomorphismAlgebra.lean`, where
it is used to show that a vector bundle is determined up to invertible twist by its endomorphism
algebra sheaf: `Stacks.EtaleCohomology.exists_isUnit_coord_smulRight_coord` produces the unimodular
matrix coefficient and
`Stacks.EtaleCohomology.exists_linearEquiv_conjAlgEquiv_of_isUnit_coord` turns it
into the conjugating linear equivalence. This file only has to instantiate those at
`φ = RingHom.id R` — the local ring receiving the base ring being the base ring itself — and then
move the result across the two changes of presentation a consumer wants: from a basis indexed by
an arbitrary finite type to matrices, and from the single universe those lemmas are stated in to
arbitrary universes for the ring, the module and the index type.

The universe reduction, inside `Stacks.exists_conjAlgEquiv_eq_of_basis`, is that a free module of
rank `n` over `R : Type u` is linearly equivalent to `ULift.{u} (Fin n) → R`, which lies in
`Type u` whatever universes the original module and index type were in; being a conjugation is
preserved by transporting an algebra automorphism along a linear equivalence
(`Stacks.exists_conjAlgEquiv_eq_of_conj`), so the restricted form applies.
-/

@[expose] public section

universe u v w

namespace Stacks

open Stacks.EtaleCohomology

/-- If the transport of `α` along `e` is `β`, then `α x = e.symm (β (e x))`. -/
private theorem algEquiv_apply_eq_symm_apply_of_trans {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (α : A ≃ₐ[R] A) (β : B ≃ₐ[R] B)
    (h : e.symm.trans (α.trans e) = β) (x : A) : α x = e.symm (β (e x)) := by
  subst h
  simp

/-- Being conjugation by a linear equivalence passes along a change of presentation of the module:
if the transport of `α` along `L` is conjugation by `T'`, then `α` is conjugation by
`L ≪≫ₗ T' ≪≫ₗ L.symm`. -/
theorem exists_conjAlgEquiv_eq_of_conj {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (L : M ≃ₗ[R] N) (α : Module.End R M ≃ₐ[R] Module.End R M) {T' : N ≃ₗ[R] N}
    (hT' : (L.conjAlgEquiv R).symm.trans (α.trans (L.conjAlgEquiv R)) = T'.conjAlgEquiv R) :
    ∃ T : M ≃ₗ[R] M, α = T.conjAlgEquiv R := by
  refine ⟨L ≪≫ₗ T' ≪≫ₗ L.symm, AlgEquiv.ext fun f => ?_⟩
  rw [algEquiv_apply_eq_symm_apply_of_trans _ α _ hT']
  rfl

/-- Skolem--Noether over a local ring, for a free module whose base ring, carrier and index type
all lie in the same universe. This is the direct instantiation of the machinery of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BrauerGroupScheme/EndomorphismAlgebra.lean`;
`Stacks.exists_conjAlgEquiv_eq_of_basis` removes the universe restriction and subsumes it. -/
private theorem exists_conjAlgEquiv_eq_of_basis_aux {R P : Type u} [CommRing R] [IsLocalRing R]
    [AddCommGroup P] [Module R P] {I : Type u} [Finite I] [Nonempty I]
    (b : Module.Basis I R P) (α : Module.End R P ≃ₐ[R] Module.End R P) :
    ∃ T : P ≃ₗ[R] P, α = T.conjAlgEquiv R := by
  obtain ⟨j, k, hjk⟩ :=
    exists_isUnit_coord_smulRight_coord b b α (RingHom.id R) (Classical.arbitrary I)
  exact exists_linearEquiv_conjAlgEquiv_of_isUnit_coord b b α _ j k hjk

/-- **Skolem--Noether over a local ring.** Let `R` be a commutative local ring and let `P` be a
free `R`-module with a basis indexed by a nonempty finite type. Then every algebra automorphism of
`Module.End R P` is conjugation by a linear automorphism of `P`. -/
theorem exists_conjAlgEquiv_eq_of_basis {R : Type u} [CommRing R] [IsLocalRing R] {P : Type v}
    [AddCommGroup P] [Module R P] {I : Type w} [Finite I] [Nonempty I]
    (b : Module.Basis I R P) (α : Module.End R P ≃ₐ[R] Module.End R P) :
    ∃ T : P ≃ₗ[R] P, α = T.conjAlgEquiv R := by
  classical
  let e : I ≃ ULift.{u} (Fin (Nat.card I)) := (Finite.equivFin I).trans Equiv.ulift.symm
  have : Nonempty (ULift.{u} (Fin (Nat.card I))) := ⟨e (Classical.arbitrary I)⟩
  let L : P ≃ₗ[R] (ULift.{u} (Fin (Nat.card I)) → R) := (b.reindex e).equivFun
  obtain ⟨T', hT'⟩ := exists_conjAlgEquiv_eq_of_basis_aux
    (Pi.basisFun R (ULift.{u} (Fin (Nat.card I))))
    ((L.conjAlgEquiv R).symm.trans (α.trans (L.conjAlgEquiv R)))
  exact exists_conjAlgEquiv_eq_of_conj L α hT'

/-- **Skolem--Noether for a matrix algebra over a local ring.** Over a commutative local ring every
algebra automorphism of a matrix algebra indexed by a nonempty finite type is conjugation by a unit
of that matrix algebra. -/
theorem Matrix.exists_units_conj_eq_of_algEquiv {R : Type u} [CommRing R] [IsLocalRing R]
    {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
    (α : Matrix I I R ≃ₐ[R] Matrix I I R) :
    ∃ u : (Matrix I I R)ˣ, ∀ x : Matrix I I R,
      α x = (u : Matrix I I R) * x * ((u⁻¹ : (Matrix I I R)ˣ) : Matrix I I R) := by
  obtain ⟨T, hT⟩ := exists_conjAlgEquiv_eq_of_basis (Pi.basisFun R I)
    (algEquivMatrix'.trans (α.trans (algEquivMatrix' (R := R) (n := I)).symm))
  have h1 : T.toLinearMap * T.symm.toLinearMap = (1 : Module.End R (I → R)) :=
    LinearMap.ext fun y => by simp [Module.End.mul_apply]
  have h2 : T.symm.toLinearMap * T.toLinearMap = (1 : Module.End R (I → R)) :=
    LinearMap.ext fun y => by simp [Module.End.mul_apply]
  obtain ⟨u, hu1, hu2⟩ : ∃ u : (Matrix I I R)ˣ,
      (u : Matrix I I R) = algEquivMatrix' T.toLinearMap ∧
        ((u⁻¹ : (Matrix I I R)ˣ) : Matrix I I R) = algEquivMatrix' T.symm.toLinearMap :=
    ⟨⟨_, _, by rw [← map_mul, h1, map_one], by rw [← map_mul, h2, map_one]⟩, rfl, rfl⟩
  refine ⟨u, fun x => ?_⟩
  rw [algEquiv_apply_eq_symm_apply_of_trans (algEquivMatrix' (R := R) (n := I)).symm α _ hT x,
    AlgEquiv.symm_symm, LinearEquiv.conjAlgEquiv_apply, ← Module.End.mul_eq_comp,
    ← Module.End.mul_eq_comp, map_mul, map_mul, AlgEquiv.apply_symm_apply, hu1, hu2, mul_assoc]

end Stacks
