module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification
public import StacksFrontier.LinearAlgebra.SymmetricPower.BaseChange

/-!
# Naturality of the base change of symmetric powers

`SymmetricAlgebra.symmetricPowerBaseChange` compares `A ⊗_R Symⁿ_R(M)` with
`Symⁿ_A(A ⊗_R M)` for a commutative `R`-algebra `A`. This file records how that comparison
behaves when `A` varies: a ring homomorphism `φ : A →+* B` over `R`, together with a
`φ`-semilinear map `A ⊗_R M →ₛₗ[φ] B ⊗_R M` extending the identity on `1 ⊗ M`, carries one
comparison to the other.

The restriction maps of the presheaf `U ↦ 𝒪(U) ⊗_R M` are of exactly that shape, so this is
what makes the sectionwise comparisons of `Stacks.AssociatedSheaf.associatedPresheaf` into a
morphism of presheaves of modules.

## Main results

* `SymmetricAlgebra.symmetricAlgebraBaseChange_symm_naturality`: naturality at the level of the
  whole symmetric algebra — `SymmetricAlgebra.mapₛₗ φ u` carries
  `(symmetricAlgebraBaseChange R A M).symm (a ⊗ y)` to
  `(symmetricAlgebraBaseChange R B M).symm (φ a ⊗ y)`.
* `SymmetricAlgebra.symmetricPowerBaseChange_naturality`: the same statement for the degree-`n`
  comparison, read in the symmetric algebra of the base change.
* `SymmetricAlgebra.symmetricPowerBaseChange_tmul_mul_ι`: the degree-`n` comparison multiplies a
  degree-one generator onto a symmetric power as the multiplication of the symmetric algebra of
  the base change does.

## Implementation notes

Both naturality statements are proved by induction over `SymmetricAlgebra.induction`, with the
scalar `a` universally quantified so that the multiplicative step may use the induction
hypothesis at `1`: the element `a ⊗ (y * z)` factors as `(a ⊗ y) * (1 ⊗ z)`, and all three maps
involved are ring homomorphisms. The only inputs are `symmetricAlgebraBaseChange_ι`, the
equation that pins the algebra-level comparison down on degree-one generators, and the behaviour
of `SymmetricAlgebra.mapₛₗ` on the base ring and on generators — so nothing here depends on the
particular witness `symmetricAlgebraBaseChange` names.

The hypothesis on the semilinear map is only `u (1 ⊗ m) = 1 ⊗ m`; that is all the induction
uses, and it is what a restriction map of `associatedPresheaf` satisfies on the nose.

## References

* [Stacks Project, Tag 0C6F](https://stacks.math.columbia.edu/tag/0C6F)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public section

open scoped TensorProduct

namespace SymmetricAlgebra

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
  {B : Type*} [CommRing B] [Algebra R B] {M : Type*} [AddCommGroup M] [Module R M]

/-- The base-change comparison on the image of the base ring: it is the algebra structure map,
because the comparison is an isomorphism of `A`-algebras. -/
theorem symmetricAlgebraBaseChange_symm_tmul_one (a : A) :
    (symmetricAlgebraBaseChange R A M).symm (a ⊗ₜ[R] (1 : SymmetricAlgebra R M)) =
      algebraMap A (SymmetricAlgebra A (A ⊗[R] M)) a :=
  (symmetricAlgebraBaseChange R A M).symm.commutes a

/-- Pulling the factor `1 ⊗ z` out of `a ⊗ (y * z)`. -/
private theorem tmul_mul_eq {S : Type*} [CommRing S] [Algebra R S] {C : Type*} [CommRing C]
    [Algebra R C] (a : C) (y z : S) :
    a ⊗ₜ[R] (y * z) = (a ⊗ₜ[R] y) * ((1 : C) ⊗ₜ[R] z) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- The generator case of `tmul_mul_eq`. -/
private theorem tmul_ι_eq (a : A) (m : M) :
    a ⊗ₜ[R] (ι R M m) = (a ⊗ₜ[R] (1 : SymmetricAlgebra R M)) * ((1 : A) ⊗ₜ[R] (ι R M m)) := by
  simpa only [one_mul] using tmul_mul_eq a (1 : SymmetricAlgebra R M) (ι R M m)

/-- Moving a scalar of the base ring across the tensor sign. -/
private theorem tmul_algebraMap_eq {S : Type*} [CommRing S] [Algebra R S] {C : Type*}
    [CommRing C] [Algebra R C] (a : C) (r : R) :
    a ⊗ₜ[R] (algebraMap R S r) = (a * algebraMap R C r) ⊗ₜ[R] (1 : S) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Algebra.smul_def, Algebra.algebraMap_eq_smul_one, mul_comm]

/-- The naturality statement on the image of the base ring. -/
private theorem baseChange_symm_naturality_tmul_one (φ : A →+* B)
    (u : A ⊗[R] M →ₛₗ[φ] B ⊗[R] M) (a : A) :
    mapₛₗ φ u ((symmetricAlgebraBaseChange R A M).symm
        (a ⊗ₜ[R] (1 : SymmetricAlgebra R M))) =
      (symmetricAlgebraBaseChange R B M).symm (φ a ⊗ₜ[R] (1 : SymmetricAlgebra R M)) := by
  rw [symmetricAlgebraBaseChange_symm_tmul_one, symmetricAlgebraBaseChange_symm_tmul_one,
    mapₛₗ_algebraMap]

/-- **Naturality of the base-change comparison of symmetric algebras.** A ring homomorphism
`φ : A →+* B` over `R` and a `φ`-semilinear map `u` fixing `1 ⊗ m` carry the comparison for `A`
to the comparison for `B`.

Both sides are ring homomorphisms of `a ⊗ y`, so the induction is over `y` with `a` quantified;
the generator step is `symmetricAlgebraBaseChange_symm_tmul_ι` on both sides. -/
theorem symmetricAlgebraBaseChange_symm_naturality
    (φ : A →+* B) (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r)
    (u : A ⊗[R] M →ₛₗ[φ] B ⊗[R] M) (hu : ∀ m : M, u ((1 : A) ⊗ₜ[R] m) = (1 : B) ⊗ₜ[R] m) :
    ∀ (y : SymmetricAlgebra R M) (a : A),
      mapₛₗ φ u ((symmetricAlgebraBaseChange R A M).symm (a ⊗ₜ[R] y)) =
        (symmetricAlgebraBaseChange R B M).symm (φ a ⊗ₜ[R] y) := by
  intro y
  induction y using SymmetricAlgebra.induction with
  | algebraMap r =>
      intro a
      rw [tmul_algebraMap_eq, tmul_algebraMap_eq, baseChange_symm_naturality_tmul_one φ u,
        map_mul, hφ r]
  | ι m =>
      intro a
      rw [tmul_ι_eq a m, tmul_ι_eq (φ a) m, map_mul, map_mul, map_mul,
        baseChange_symm_naturality_tmul_one φ u, symmetricAlgebraBaseChange_symm_tmul_ι,
        symmetricAlgebraBaseChange_symm_tmul_ι, mapₛₗ_ι, hu m]
  | mul y z hy hz =>
      intro a
      rw [tmul_mul_eq, tmul_mul_eq, map_mul, map_mul, map_mul, hy a, hz 1, map_one]
  | add y z hy hz =>
      intro a
      rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add, map_add, hy a, hz a]

/-- **Naturality of the degree-`n` base-change comparison**, read in the symmetric algebra of
the base change. -/
theorem symmetricPowerBaseChange_naturality
    (φ : A →+* B) (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r)
    (u : A ⊗[R] M →ₛₗ[φ] B ⊗[R] M) (hu : ∀ m : M, u ((1 : A) ⊗ₜ[R] m) = (1 : B) ⊗ₜ[R] m)
    (n : ℕ) (a : A) (x : SymPow.symmetricPower n R M) :
    mapₛₗ φ u (symmetricPowerBaseChange R A M n (a ⊗ₜ[R] x) :
        SymmetricAlgebra A (A ⊗[R] M)) =
      (symmetricPowerBaseChange R B M n (φ a ⊗ₜ[R] x) :
        SymmetricAlgebra B (B ⊗[R] M)) :=
  symmetricAlgebraBaseChange_symm_naturality φ hφ u hu
    (x : SymmetricAlgebra R M) a

/-- **The degree-`n` comparison and the multiplication by a degree-one generator.** The
comparison carries `1 ⊗ (ι m · x)` to `ι (1 ⊗ m)` times the comparison of `1 ⊗ x`. -/
theorem symmetricPowerBaseChange_tmul_mul_ι (n : ℕ) (m : M)
    (x : SymPow.symmetricPower n R M) :
    (symmetricPowerBaseChange R A M (n + 1)
          ((1 : A) ⊗ₜ[R] SymPow.symMulMap n (LinearMap.id : M →ₗ[R] M) (m ⊗ₜ[R] x)) :
        SymmetricAlgebra A (A ⊗[R] M)) =
      ι A (A ⊗[R] M) ((1 : A) ⊗ₜ[R] m) *
        (symmetricPowerBaseChange R A M n ((1 : A) ⊗ₜ[R] x) :
          SymmetricAlgebra A (A ⊗[R] M)) := by
  rw [symmetricPowerBaseChange_apply_coe, symmetricPowerBaseChange_apply_coe,
    symmetricPowerBaseChangeIncl_tmul, symmetricPowerBaseChangeIncl_tmul]
  rw [SymPow.symMulMap_tmul n (LinearMap.id : M →ₗ[R] M) m x, tmul_mul_eq,
    map_mul, symmetricAlgebraBaseChange_symm_tmul_ι, LinearMap.id_apply]

end SymmetricAlgebra

end
