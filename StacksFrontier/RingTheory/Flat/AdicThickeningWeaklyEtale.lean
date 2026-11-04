module

public import Mathlib.RingTheory.Etale.Weakly
public import StacksFrontier.RingTheory.Flat.AdicFiltration
public import StacksFrontier.RingTheory.Flat.TowerLTensor
public import StacksFrontier.RingTheory.WeaklyEtale.Flat

/-!
# Flatness from the infinitesimal thickenings, through weakly étale local rings

This file contains the commutative algebra behind Stacks 08VP at a geometric point.  There the
local rings in play are étale local rings, which are weakly étale over the rings of affine
charts, and the module is the geometric stalk `M = F_{x̄}` of a coherent module over the étale
local ring `T = 𝒪_{X, x̄}`.  The hypothesis is flatness of the stalks of the pullbacks of `F` to
the thickenings `X_n = Spec(A/Iⁿ) ×_{Spec A} X`, and the conclusion is flatness of `M` over the
étale local ring `R = 𝒪_{Spec A, ȳ}` of the base.

## Main results

* `Module.Flat.tensor_of_flat_tensor_weaklyEtale`: if `D` is a local ring weakly étale over
  `T ⊗_R Rₙ`, with `R → Rₙ` surjective and `T → D` local, then flatness of `D ⊗_T M` over `Rₙ`
  gives flatness of `Rₙ ⊗_R M` over `Rₙ`.
* `Module.Flat.quotient_tensor_of_flat_tensor_weaklyEtale`: if `A → R` and `A/J → Rₙ` are weakly
  étale and `R → Rₙ` is a local homomorphism of local rings over `A → A/J`, then flatness of
  `Rₙ ⊗_R M` over `Rₙ` gives flatness of `(A/J) ⊗_A M` over `A/J`.
* `Module.Flat.of_flat_quotient_tensor_pow_of_weaklyEtale`: Stacks 0523 over the Noetherian ring
  `A`, followed by the passage from `A` to the weakly étale `A`-algebra `R` (Stacks 092C).

## References

* [Stacks Project, Tag 08VP](https://stacks.math.columbia.edu/tag/08VP)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 0523](https://stacks.math.columbia.edu/tag/0523)
* [Stacks Project, Tag 092C](https://stacks.math.columbia.edu/tag/092C)
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public section

open scoped TensorProduct

namespace Module.Flat

/-- Flatness of the base change `(A/I) ⊗_A M` over `A/I` is flatness of the quotient `M/IM`. -/
theorem quotient_of_flat_tensor {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) [Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M)] :
    Module.Flat (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M))) := by
  let e := TensorProduct.quotTensorEquivQuotSMul M I
  let e' : ((A ⧸ I) ⊗[A] M) ≃ₗ[A ⧸ I] (M ⧸ (I • (⊤ : Submodule A M))) :=
    { __ := e.toAddEquiv
      map_smul' := by
        intro r z
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        change e (a • z) = a • e z
        exact e.map_smul a z }
  exact Module.Flat.of_linearEquiv e'.symm

/-- A flat algebra `D` over a ring `C`, where `D` is local and `C` is a quotient of a local ring
`T` with `T → D` local, is faithfully flat. -/
theorem _root_.Module.FaithfullyFlat.of_flat_of_surjective_of_isLocalHom
    {T C D : Type*} [CommRing T] [CommRing C] [CommRing D] [Algebra T C] [Algebra C D]
    [Algebra T D] [IsScalarTower T C D] [IsLocalRing T] [IsLocalRing D]
    (hα : Function.Surjective (algebraMap T C)) [IsLocalHom (algebraMap T D)]
    [Module.Flat C D] : Module.FaithfullyFlat C D := by
  let : Nontrivial C := (algebraMap C D).domain_nontrivial
  let : IsLocalRing C := .of_surjective' (algebraMap T C) hα
  let : IsLocalHom (algebraMap C D) := ⟨by
    intro c hc
    obtain ⟨t, rfl⟩ := hα c
    rw [← IsScalarTower.algebraMap_apply] at hc
    exact (algebraMap T C).isUnit_map ((isUnit_map_iff (algebraMap T D) t).mp hc)⟩
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- **Descent of flatness along a weakly étale local ring over a pushout.**  Let `R → T` be a
ring map, `R → Rₙ` a surjective ring map and `D` a local ring which is a weakly étale algebra over
`T ⊗_R Rₙ` through `φ`, the composite `T → D` being a local homomorphism from the local ring `T`.
For a `T`-module `M`, if `D ⊗_T M` is flat over `Rₙ`, then `Rₙ ⊗_R M` is flat over `Rₙ`. -/
theorem tensor_of_flat_tensor_weaklyEtale
    {R T Rn D M : Type*} [CommRing R] [CommRing T] [CommRing Rn] [CommRing D]
    [Algebra R T] [Algebra R Rn] [Algebra T D] [Algebra Rn D]
    (hsurj : Function.Surjective (algebraMap R Rn))
    (φ : T ⊗[R] Rn →+* D) (hl : φ.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap T D)
    (hr : φ.comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap Rn D)
    (hφ : @Algebra.WeaklyEtale _ _ _ _ φ.toAlgebra)
    [IsLocalRing T] [IsLocalRing D] [IsLocalHom (algebraMap T D)]
    [AddCommGroup M] [Module R M] [Module T M] [IsScalarTower R T M]
    [Module.Flat Rn (D ⊗[T] M)] :
    Module.Flat Rn (Rn ⊗[R] M) := by
  let U := T ⊗[R] Rn
  let : Algebra Rn U := Algebra.TensorProduct.rightAlgebra
  let : Algebra U D := φ.toAlgebra
  have : IsScalarTower T U D := IsScalarTower.of_algebraMap_eq fun t =>
    (RingHom.congr_fun hl t).symm
  have : IsScalarTower Rn U D := IsScalarTower.of_algebraMap_eq fun t =>
    (RingHom.congr_fun hr t).symm
  have : Algebra.WeaklyEtale U D := hφ
  have hTU : Function.Surjective (algebraMap T U) :=
    Algebra.TensorProduct.includeLeft_surjective R T hsurj
  have : Module.FaithfullyFlat U D :=
    Module.FaithfullyFlat.of_flat_of_surjective_of_isLocalHom (T := T) hTU
  let P := U ⊗[T] M
  have : Module.Flat Rn (D ⊗[U] P) := Module.Flat.of_linearEquiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange T U D D M).restrictScalars Rn)
  have : Module.Flat Rn P := Module.Flat.of_tensorProduct_of_faithfullyFlat (C := U) (D := D)
  let e : P ≃ₗ[Rn] Rn ⊗[R] M := Algebra.IsPushout.cancelBaseChange R Rn T U M
  exact Module.Flat.of_linearEquiv e.symm

/-- **From the thickening of the base to the quotient of the base ring.**  Let `A → R` be weakly
étale, `A → Q` surjective and `Q → Rₙ` weakly étale, with `R → Rₙ` a local homomorphism of local
rings over `A`.  For an `R`-module `M`, if `Rₙ ⊗_R M` is flat over `Rₙ`, then `Q ⊗_A M` is flat
over `Q`. -/
theorem quotient_tensor_of_flat_tensor_weaklyEtale
    {A Q R Rn M : Type*} [CommRing A] [CommRing Q] [CommRing R] [CommRing Rn]
    [Algebra A Q] [Algebra A R] [Algebra Q Rn] [Algebra R Rn] [Algebra A Rn]
    [IsScalarTower A Q Rn] [IsScalarTower A R Rn]
    (hsurj : Function.Surjective (algebraMap A Q)) [Algebra.WeaklyEtale A R]
    [Algebra.WeaklyEtale Q Rn] [IsLocalRing R] [IsLocalRing Rn] [IsLocalHom (algebraMap R Rn)]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]
    [Module.Flat Rn (Rn ⊗[R] M)] :
    Module.Flat Q (Q ⊗[A] M) := by
  let R' := Q ⊗[A] R
  let : Algebra R R' := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower A R R' := Algebra.TensorProduct.right_isScalarTower
  let ψ : R' →ₐ[A] Rn := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A Q Rn)
    (IsScalarTower.toAlgHom A R Rn) (fun _ _ => Commute.all _ _)
  let : Algebra R' Rn := ψ.toRingHom.toAlgebra
  have : IsScalarTower Q R' Rn := IsScalarTower.of_algebraMap_eq fun q => by
    change _ = ψ (q ⊗ₜ[A] 1)
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  have : IsScalarTower R R' Rn := IsScalarTower.of_algebraMap_eq fun r => by
    change _ = ψ (1 ⊗ₜ[A] r)
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  have hRR' : Function.Surjective (algebraMap R R') :=
    Algebra.TensorProduct.includeRight_surjective R hsurj
  have : Module.Flat R' Rn :=
    flat_of_flat_of_mul_flat Q R' (Algebra.WeaklyEtale.flat_lmul' Q R') Rn inferInstance
  have : Module.FaithfullyFlat R' Rn :=
    Module.FaithfullyFlat.of_flat_of_surjective_of_isLocalHom (T := R) hRR'
  let P := R' ⊗[R] M
  have : Module.Flat Q (Rn ⊗[R] M) := Module.Flat.trans Q Rn _
  have : Module.Flat Q (Rn ⊗[R'] P) := Module.Flat.of_linearEquiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R R' Rn Rn M).restrictScalars Q)
  have : Module.Flat Q P := Module.Flat.of_tensorProduct_of_faithfullyFlat (C := R') (D := Rn)
  exact Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange A Q R R' M).symm

/-- **Stacks 0523, read through a weakly étale extension of the base.**  Let `A` be a Noetherian
ring, `I ⊆ A` an ideal, `A → R` weakly étale and `R → T` a homomorphism to a Noetherian local
ring with `I T ⊆ 𝔪_T`.  For a finite `T`-module `M`, if `(A/Iⁿ⁺¹) ⊗_A M` is flat over `A/Iⁿ⁺¹`
for every `n`, then `M` is flat over `R`. -/
theorem of_flat_quotient_tensor_pow_of_weaklyEtale
    {A R T M : Type*} [CommRing A] [CommRing R] [CommRing T]
    [IsNoetherianRing A] [IsNoetherianRing T] [IsLocalRing T]
    [Algebra A R] [Algebra R T] [Algebra A T] [IsScalarTower A R T] [Algebra.WeaklyEtale A R]
    [AddCommGroup M] [Module A M] [Module R M] [Module T M]
    [IsScalarTower A R M] [IsScalarTower R T M] [IsScalarTower A T M] [Module.Finite T M]
    (I : Ideal A) (hI : I.map (algebraMap A T) ≤ IsLocalRing.maximalIdeal T)
    (hflat : ∀ n : ℕ, Module.Flat (A ⧸ I ^ (n + 1)) ((A ⧸ I ^ (n + 1)) ⊗[A] M)) :
    Module.Flat R M := by
  let : IsLocalization.AtPrime T (IsLocalRing.maximalIdeal T) :=
    IsLocalization.self fun _ hx => IsLocalRing.notMem_maximalIdeal.mp hx
  let : IsLocalizedModule.AtPrime (IsLocalRing.maximalIdeal T) (LinearMap.id : M →ₗ[T] M) := by
    change IsLocalizedModule (IsLocalRing.maximalIdeal T).primeCompl (LinearMap.id : M →ₗ[T] M)
    exact isLocalizedModule_id (IsLocalRing.maximalIdeal T).primeCompl M T
  have hA : Module.Flat A M := Module.Flat.of_flat_quotient_pow I M
    (fun n => by
      have := hflat n
      exact quotient_of_flat_tensor (I ^ (n + 1)))
    (IsLocalRing.maximalIdeal T) hI M LinearMap.id
  exact flat_of_flat_of_mul_flat A R (Algebra.WeaklyEtale.flat_lmul' A R) M hA

end Module.Flat
