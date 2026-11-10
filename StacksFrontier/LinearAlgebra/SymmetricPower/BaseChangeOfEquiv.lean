module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.LinearAlgebra.SymmetricPower.BaseChangeNaturality

/-!
# The base change comparison of a symmetric power, through an equivalence

Let `A` be a commutative `R`-algebra, `M` an `R`-module, `N` an `A`-module and `u : M → N` a map
semilinear over `R → A` whose base change comparison `A ⊗_R M → N`, `a ⊗ m ↦ a · u(m)`, is an
isomorphism.  Then the base change comparison of every symmetric power,
`A ⊗_R Symⁿ_R(M) → Symⁿ_A(N)`, `a ⊗ x ↦ a · Symⁿ(u)(x)`, is an isomorphism too: it is the
base change comparison `SymmetricAlgebra.symmetricPowerBaseChange` of the symmetric power,
`A ⊗_R Symⁿ_R(M) ≅ Symⁿ_A(A ⊗_R M)`, followed by the symmetric power of the equivalence
`A ⊗_R M ≅ N`.

This is the algebra behind the statement that the presheaf of sectionwise symmetric powers of a
module cartesian on affine charts is again cartesian on affine charts.

## Main results

* `SymmetricAlgebra.mapₛₗ_eq_mapₛₗ_symmetricAlgebraBaseChange_symm`: the factorization on the
  whole symmetric algebra.
* `SymmetricAlgebra.bijective_of_symmetricPower_baseChange`: **any `A`-linear map
  `A ⊗_R Symⁿ_R(M) → Symⁿ_A(N)` sending `1 ⊗ x` to `Symⁿ(u)(x)` is bijective.**
* `SymmetricAlgebra.bijective_of_symmetricPower_extendScalars`: the same, with the base change
  written through `ModuleCat.extendScalars`, the form a presheaf of modules states it in.

## References

* [Stacks Project, Tag 01CF](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe w

namespace SymmetricAlgebra
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module A N]

/-- **A semilinear map out of `M` through the base change of `Sym_R(M)`.**  Let `u : M → N` be
semilinear over `R → A` and `e : A ⊗_R M ≃ N` an `A`-linear equivalence restricting to `u` on
`1 ⊗ M`.  Then the symmetric algebra map of `u` factors as the base change comparison
`Sym_R(M) → Sym_A(A ⊗_R M)` followed by the symmetric algebra map of `e`. -/
theorem mapₛₗ_eq_mapₛₗ_symmetricAlgebraBaseChange_symm {φ : R →+* A}
    (hφ : ∀ r, φ r = algebraMap R A r) (u : M →ₛₗ[φ] N)
    (e : A ⊗[R] M ≃ₗ[A] N) (he : ∀ m, e (1 ⊗ₜ[R] m) = u m) (y : SymmetricAlgebra R M) :
    mapₛₗ φ u y =
      mapₛₗ (RingHom.id A) (e.toLinearMap : A ⊗[R] M →ₛₗ[RingHom.id A] N)
        ((symmetricAlgebraBaseChange R A M).symm (1 ⊗ₜ[R] y)) := by
  induction y using SymmetricAlgebra.induction with
  | algebraMap r =>
    have h : (1 : A) ⊗ₜ[R] algebraMap R (SymmetricAlgebra R M) r =
        algebraMap R A r ⊗ₜ[R] (1 : SymmetricAlgebra R M) := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        ← Algebra.algebraMap_eq_smul_one]
    rw [mapₛₗ_algebraMap, h, symmetricAlgebraBaseChange_symm_tmul_one, mapₛₗ_algebraMap, hφ]
    rfl
  | ι m => rw [mapₛₗ_ι, symmetricAlgebraBaseChange_symm_tmul_ι, mapₛₗ_ι]; simp [he]
  | mul x y hx hy =>
    have h : (1 : A) ⊗ₜ[R] (x * y) = ((1 : A) ⊗ₜ[R] x) * ((1 : A) ⊗ₜ[R] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [map_mul, h, map_mul, map_mul, hx, hy]
  | add x y hx hy => rw [map_add, TensorProduct.tmul_add, map_add, map_add, hx, hy]

/-- **The base change comparison of a symmetric power is bijective when that of the module is.**
An `A`-linear map `g : A ⊗_R Symⁿ_R(M) → Symⁿ_A(N)` sending `1 ⊗ x` to `Symⁿ(u)(x)` is the base
change comparison of `Symⁿ_R(M)` followed by the symmetric power of the equivalence `e`, and both
factors are bijective. -/
theorem bijective_of_symmetricPower_baseChange {φ : R →+* A}
    (hφ : ∀ r, φ r = algebraMap R A r) (u : M →ₛₗ[φ] N)
    (e : A ⊗[R] M ≃ₗ[A] N) (he : ∀ m, e (1 ⊗ₜ[R] m) = u m) (n : ℕ)
    (g : A ⊗[R] SymPow.symmetricPower n R M →ₗ[A] SymPow.symmetricPower n A N)
    (hg : ∀ x : SymPow.symmetricPower n R M,
      (g (1 ⊗ₜ[R] x) : SymmetricAlgebra A N) = mapₛₗ φ u x) :
    Function.Bijective g := by
  let ψ : A ⊗[R] M →ₛₗ[RingHom.id A] N := e.toLinearMap
  let ψ' : N →ₛₗ[RingHom.id A] A ⊗[R] M := e.symm.toLinearMap
  have key : ∀ y, (g y : SymmetricAlgebra A N) =
      mapₛₗ (RingHom.id A) ψ
        (symmetricPowerBaseChange R A M n y : SymmetricAlgebra A (A ⊗[R] M)) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, map_add, Submodule.coe_add, Submodule.coe_add, map_add, hy, hz]
    | tmul a x =>
      have h1 : a ⊗ₜ[R] x = a • ((1 : A) ⊗ₜ[R] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, map_smul, Submodule.coe_smul, Submodule.coe_smul, mapₛₗ_smul, hg,
        symmetricPowerBaseChange_apply_coe, symmetricPowerBaseChangeIncl_tmul,
        mapₛₗ_eq_mapₛₗ_symmetricAlgebraBaseChange_symm hφ u e he]
      rfl
  have hinv : ∀ w : SymmetricAlgebra A (A ⊗[R] M),
      mapₛₗ (RingHom.id A) ψ' (mapₛₗ (RingHom.id A) ψ w) = w := fun w =>
    ((mapₛₗ_eq_comp ψ ψ' (LinearMap.id) (fun _ => rfl) (fun m => (e.symm_apply_apply m).symm)
      w).symm).trans (mapₛₗ_eq_self _ (fun _ => rfl) (fun _ => rfl) w)
  have hinv' : ∀ w : SymmetricAlgebra A N,
      mapₛₗ (RingHom.id A) ψ (mapₛₗ (RingHom.id A) ψ' w) = w := fun w =>
    ((mapₛₗ_eq_comp ψ' ψ (LinearMap.id) (fun _ => rfl) (fun m => (e.apply_symm_apply m).symm)
      w).symm).trans (mapₛₗ_eq_self _ (fun _ => rfl) (fun _ => rfl) w)
  have hbc := (symmetricPowerBaseChange R A M n).bijective
  refine ⟨fun y y' h => hbc.1 (Subtype.ext ?_), fun w => ?_⟩
  · have h' := congrArg (fun z : SymPow.symmetricPower n A N =>
      mapₛₗ (RingHom.id A) ψ' (z : SymmetricAlgebra A N)) h
    simp only [key, hinv] at h'
    exact h'
  · obtain ⟨y, hy⟩ := hbc.2 ⟨mapₛₗ (RingHom.id A) ψ' w,
      mapₛₗ_mem_symmetricPower (RingHom.id A) ψ' n w.2⟩
    refine ⟨y, Subtype.ext ?_⟩
    rw [key, hy]
    exact hinv' w
open scoped ChangeOfRings in
/-- **The base change comparison of a symmetric power is bijective when that of the module is**,
with the base change written as `ModuleCat.extendScalars` along a ring homomorphism `φ`. -/
theorem bijective_of_symmetricPower_extendScalars {R A : Type w} [CommRing R] [CommRing A]
    (φ : R →+* A) {M : Type w} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N]
    [Module A N] (u : M →ₛₗ[φ] N)
    (e : (ModuleCat.extendScalars φ).obj (ModuleCat.of R M) ⟶ ModuleCat.of A N)
    (he : Function.Bijective e) (he1 : ∀ m : M, e ((1 : A) ⊗ₜ[R, φ] m) = u m) (n : ℕ)
    (g : (ModuleCat.extendScalars φ).obj (ModuleCat.of R (SymPow.symmetricPower n R M)) ⟶
      ModuleCat.of A (SymPow.symmetricPower n A N))
    (hg : ∀ x : SymPow.symmetricPower n R M,
      (g ((1 : A) ⊗ₜ[R, φ] x) : SymmetricAlgebra A N) = mapₛₗ φ u x) :
    Function.Bijective g := by
  let : Algebra R A := φ.toAlgebra
  exact bijective_of_symmetricPower_baseChange (R := R) (A := A) (φ := φ) (fun _ => rfl) u
    (LinearEquiv.ofBijective e.hom he) he1 n g.hom hg
end SymmetricAlgebra

end
