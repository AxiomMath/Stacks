module

public import StacksFrontier.Algebra.Module.Projective.Determinant.BaseChange

/-!
# The rank idempotent across a semilinear equivalence

Let `φ : R ≃+* S` be an isomorphism of commutative rings, `M` an `R`-module, `N` an `S`-module and
`ψ : M ≃+ N` an additive equivalence which is semilinear over `φ`, that is `ψ (r • m) = φ r • ψ m`.
This file identifies the rank idempotents of `M` and of `N`:

`φ (rankIdempotent R M n) = rankIdempotent S N n`.

With `S` made an `R`-algebra through `φ`, the map `s ⊗ₜ m ↦ s • ψ m` is an `S`-linear equivalence
`S ⊗[R] M ≃ₗ[S] N`, so `N` is a base change of `M`.

## Main definitions

* `ProjectiveDeterminant.semilinearBaseChangeEquiv`: **the base change `S ⊗[R] M ≃ₗ[S] N`**
  attached to a semilinear additive equivalence over a ring isomorphism.

## Main results

* `ProjectiveDeterminant.moduleFinite_of_semilinearEquiv` and
  `ProjectiveDeterminant.moduleProjective_of_semilinearEquiv`: `N` is a finite projective
  `S`-module when `M` is a finite projective `R`-module.
* `ProjectiveDeterminant.rankIdempotent_eq_of_semilinearEquiv`: **the rank idempotents
  correspond**, `φ (rankIdempotent R M n) = rankIdempotent S N n`.

## References

* [Stacks Project, Section 0FJ9](https://stacks.math.columbia.edu/tag/0FJ9)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ProjectiveDeterminant

universe u v w

variable {R : Type u} {S : Type v} {M : Type w} {N : Type*}
  [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (φ : R ≃+* S) (ψ : M ≃+ N) (hψ : ∀ (r : R) (m : M), ψ (r • m) = φ r • ψ m)

/-- **A semilinear additive equivalence over a ring isomorphism exhibits its target as a base
change of its source.** With `S` made an `R`-algebra through `φ`, the `S`-linear map
`s ⊗ₜ m ↦ s • ψ m` is an equivalence, with inverse `x ↦ 1 ⊗ₜ ψ.symm x`. -/
def semilinearBaseChangeEquiv :
    letI : Algebra R S := φ.toRingHom.toAlgebra
    (S ⊗[R] M) ≃ₗ[S] N := by
  letI : Algebra R S := φ.toRingHom.toAlgebra
  letI : Module R N := Module.compHom N (φ.toRingHom)
  haveI : IsScalarTower R S N := ⟨fun r s n => by
    change (φ r * s) • n = φ r • (s • n)
    rw [mul_smul]⟩
  letI ψR : M →ₗ[R] N :=
    { toFun := ψ, map_add' := ψ.map_add, map_smul' := fun r m => hψ r m }
  have hsymm : ∀ (s : S) (x : N), ψ.symm (s • x) = φ.symm s • ψ.symm x := fun s x =>
    ψ.injective (by rw [ψ.apply_symm_apply, hψ, φ.apply_symm_apply, ψ.apply_symm_apply])
  have key : ∀ (s : S) (y : M), (1 : S) ⊗ₜ[R] (φ.symm s • y) = s ⊗ₜ[R] y := fun s y =>
    (TensorProduct.smul_tmul (φ.symm s) (1 : S) y).symm.trans (by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact congrArg (fun t : S => t ⊗ₜ[R] y) (φ.apply_symm_apply s))
  have key2 : ∀ (s : S) (y : M), s ⊗ₜ[R] y = s • ((1 : S) ⊗ₜ[R] y) := fun s y =>
    (congrArg (fun t : S => t ⊗ₜ[R] y) (mul_one s).symm).trans
      (TensorProduct.smul_tmul' s (1 : S) y)
  refine LinearEquiv.ofLinearMap
    (TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton S (M →ₗ[R] N) ψR))
    ({ toFun := fun x => (1 : S) ⊗ₜ[R] ψ.symm x
       map_add' := by intro x y; simp [TensorProduct.tmul_add]
       map_smul' := fun s x =>
         ((hsymm s x) ▸ (key s (ψ.symm x))).trans (key2 s (ψ.symm x)) }) ?_ ?_
  · refine LinearMap.ext fun x => ?_
    change (TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton S (M →ₗ[R] N) ψR)) ((1 : S) ⊗ₜ[R] ψ.symm x) = x
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]
    change (1 : S) • ψ (ψ.symm x) = x
    rw [ψ.apply_symm_apply, one_smul]
  · refine TensorProduct.AlgebraTensorModule.ext fun s m => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
      TensorProduct.AlgebraTensorModule.lift_tmul, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.toSpanSingleton_apply]
    rw [show ((s • ψR) m : N) = s • ψ m from rfl, hsymm, ψ.symm_apply_apply]
    exact key s m

variable [Module.Finite R M] [Module.Projective R M]

omit [Module.Projective R M] in
include hψ in
/-- The target of a semilinear additive equivalence over a ring isomorphism is a finite module
when its source is. -/
theorem moduleFinite_of_semilinearEquiv : Module.Finite S N :=
  let : Algebra R S := φ.toRingHom.toAlgebra
  Module.Finite.equiv (semilinearBaseChangeEquiv φ ψ hψ)

omit [Module.Finite R M] in
include hψ in
/-- The target of a semilinear additive equivalence over a ring isomorphism is a projective
module when its source is. -/
theorem moduleProjective_of_semilinearEquiv : Module.Projective S N :=
  let : Algebra R S := φ.toRingHom.toAlgebra
  Module.Projective.of_equiv (semilinearBaseChangeEquiv φ ψ hψ)

include hψ in
/-- **The rank idempotents correspond across a semilinear additive equivalence over a ring
isomorphism.** The image under `φ` of the idempotent cutting out the rank-`n` stratum of `M` is
the idempotent cutting out the rank-`n` stratum of `N`. -/
theorem rankIdempotent_eq_of_semilinearEquiv [Module.Finite S N] [Module.Projective S N]
    (n : ℕ) :
    φ (rankIdempotent (R := R) (M := M) n) = rankIdempotent (R := S) (M := N) n := by
  let : Algebra R S := φ.toRingHom.toAlgebra
  refine (rankIdempotent_baseChange R S M n).trans ?_
  exact rankIdempotent_eq_of_linearEquiv _ _ (semilinearBaseChangeEquiv φ ψ hψ) n

end ProjectiveDeterminant

end
