module

public import Mathlib

/-!
# Base change of module homomorphisms along a quotient of the base ring

Let `R` be a commutative ring, let `𝔞 ⊆ R` be an ideal and let `M`, `N` be `R`-modules.  Base
change of an `R`-linear map `h : M →ₗ[R] N` along `R → R ⧸ 𝔞` is Mathlib's
`LinearMap.baseChange`.  This file describes the kernel and the image of the resulting map
`(M →ₗ[R] N) → ((R ⧸ 𝔞) ⊗[R] M →ₗ[R ⧸ 𝔞] (R ⧸ 𝔞) ⊗[R] N)`.

## Main results

* `Stacks.BaseChangeQuotient.baseChange_eq_zero_of_image_mem_smul`: if an ideal `𝔠` of `R` is
  killed by the structure map of an `R`-algebra `S`, then every `R`-linear map whose image lies in
  `𝔠 • (⊤ : Submodule R N)` base changes to the zero map over `S`.
* `Stacks.BaseChangeQuotient.baseChange_quotient_eq_zero_iff`: the base change of `h` along
  `R → R ⧸ 𝔞` vanishes if and only if the image of `h` lies in `𝔞 • (⊤ : Submodule R N)`.
* `Stacks.BaseChangeQuotient.exists_baseChange_quotient_eq`: base change along `R → R ⧸ 𝔞` is full
  on homomorphisms out of a finite projective module, i.e. every `R ⧸ 𝔞`-linear map
  `(R ⧸ 𝔞) ⊗[R] M → (R ⧸ 𝔞) ⊗[R] N` is the base change of some `R`-linear map `M →ₗ[R] N`.

## Implementation notes

The identification `(R ⧸ 𝔞) ⊗[R] N ≃ₗ[R] N ⧸ (𝔞 • ⊤)` used throughout is Mathlib's
`TensorProduct.quotTensorEquivQuotSMul`; the surjectivity consequence that every element of
`(R ⧸ 𝔞) ⊗[R] N` has the form `1 ⊗ₜ n` is isolated as `exists_one_tmul`.

Two inputs that the arguments below need are already available elsewhere and are therefore not
restated here:

* a finite projective module is a direct summand of a finite free module, which is Mathlib's
  `Module.Finite.exists_comp_eq_id_of_projective`;
* `(𝔞 • ⊤) ⊓ (𝔟 • ⊤) = (𝔞 ⊓ 𝔟) • ⊤` for a flat — in particular for a finite projective —
  module, which is `ideal_smul_top_inf` in `StacksFrontier.RingTheory.Flat.ShortExact`.
-/

@[expose] public section

universe u

namespace Stacks.BaseChangeQuotient

open scoped TensorProduct

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- If the structure map of an `R`-algebra `S` kills the ideal `𝔠`, then every element of
`𝔠 • (⊤ : Submodule R N)` is annihilated by tensoring over `R` into `S ⊗[R] N`. -/
theorem tmul_eq_zero_of_mem_smul_top {S : Type u} [CommRing S] [Algebra R S] (𝔠 : Ideal R)
    (hker : ∀ x ∈ 𝔠, algebraMap R S x = 0) (s : S) {n : N}
    (hn : n ∈ 𝔠 • (⊤ : Submodule R N)) : s ⊗ₜ[R] n = (0 : S ⊗[R] N) := by
  refine Submodule.smul_induction_on hn ?_ ?_
  · intro x hx n' _
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, hker x hx, zero_mul,
      TensorProduct.zero_tmul]
  · intro y z hy hz
    rw [TensorProduct.tmul_add, hy, hz, add_zero]

/-- Base change along an `R`-algebra `S` whose structure map kills an ideal `𝔠` annihilates every
`R`-linear map whose image is contained in `𝔠 • (⊤ : Submodule R N)`. -/
theorem baseChange_eq_zero_of_image_mem_smul {S : Type u} [CommRing S] [Algebra R S]
    (𝔠 : Ideal R) (hker : ∀ x ∈ 𝔠, (algebraMap R S) x = 0)
    (h : M →ₗ[R] N) (hh : ∀ m : M, h m ∈ 𝔠 • (⊤ : Submodule R N)) :
    LinearMap.baseChange S h = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply]
  induction x with
  | tmul s m =>
    rw [LinearMap.baseChange_tmul]
    exact tmul_eq_zero_of_mem_smul_top 𝔠 hker s (hh m)
  | add y z hy hz => rw [map_add, hy, hz, add_zero]

/-- Every element of `(R ⧸ 𝔞) ⊗[R] N` is of the form `1 ⊗ₜ n` for some `n : N`; equivalently, the
`R`-linear map `N → (R ⧸ 𝔞) ⊗[R] N`, `n ↦ 1 ⊗ₜ n`, is surjective. -/
theorem exists_one_tmul (𝔞 : Ideal R) (y : (R ⧸ 𝔞) ⊗[R] N) :
    ∃ n : N, (1 : R ⧸ 𝔞) ⊗ₜ[R] n = y := by
  obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective (𝔞 • (⊤ : Submodule R N))
    (TensorProduct.quotTensorEquivQuotSMul N 𝔞 y)
  refine ⟨n, ?_⟩
  rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk 𝔞 n, hn, LinearEquiv.symm_apply_apply]

/-- The base change of `h : M →ₗ[R] N` along `R → R ⧸ 𝔞` is zero exactly when the image of `h` is
contained in the submodule `𝔞 • (⊤ : Submodule R N)`. -/
theorem baseChange_quotient_eq_zero_iff (𝔞 : Ideal R) (h : M →ₗ[R] N) :
    LinearMap.baseChange (R ⧸ 𝔞) h = 0 ↔ ∀ m : M, h m ∈ 𝔞 • (⊤ : Submodule R N) := by
  refine ⟨fun hzero m => ?_, fun hmem => baseChange_eq_zero_of_image_mem_smul 𝔞 ?_ h hmem⟩
  · have hm := LinearMap.congr_fun hzero ((1 : R ⧸ 𝔞) ⊗ₜ[R] m)
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply] at hm
    have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul N 𝔞) hm
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] at hq
    exact (Submodule.Quotient.mk_eq_zero _).mp hq
  · intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

/-- Base change along `R → R ⧸ 𝔞` is full on homomorphisms out of a finite projective module:
every `R ⧸ 𝔞`-linear map `(R ⧸ 𝔞) ⊗[R] M → (R ⧸ 𝔞) ⊗[R] N` is the base change of an `R`-linear
map `M →ₗ[R] N`. -/
theorem exists_baseChange_quotient_eq (𝔞 : Ideal R) [Module.Finite R M] [Module.Projective R M]
    (a : (R ⧸ 𝔞) ⊗[R] M →ₗ[R ⧸ 𝔞] (R ⧸ 𝔞) ⊗[R] N) :
    ∃ h : M →ₗ[R] N, LinearMap.baseChange (R ⧸ 𝔞) h = a := by
  obtain ⟨r, π, σ, -, -, hπσ⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  set a' : (R ⧸ 𝔞) ⊗[R] (Fin r → R) →ₗ[R ⧸ 𝔞] (R ⧸ 𝔞) ⊗[R] N :=
    a ∘ₗ LinearMap.baseChange (R ⧸ 𝔞) π with ha'
  choose n hn using fun i : Fin r =>
    exists_one_tmul 𝔞 (a' ((1 : R ⧸ 𝔞) ⊗ₜ[R] Pi.basisFun R (Fin r) i))
  set ψ : (Fin r → R) →ₗ[R] N := (Pi.basisFun R (Fin r)).constr R n with hψ
  have key : LinearMap.baseChange (R ⧸ 𝔞) ψ = a' := by
    refine ((Pi.basisFun R (Fin r)).baseChange (R ⧸ 𝔞)).ext fun i => ?_
    rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, hψ,
      Module.Basis.constr_basis]
    exact hn i
  refine ⟨ψ ∘ₗ σ, ?_⟩
  rw [LinearMap.baseChange_comp, key, ha', LinearMap.comp_assoc,
    ← LinearMap.baseChange_comp, hπσ, LinearMap.baseChange_id, LinearMap.comp_id]

end Stacks.BaseChangeQuotient

end
