module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Uniqueness of the tensor product of finitely many modules

The tensor product `⨂[R] i, s i` with its universal multilinear map `PiTensorProduct.tprod R`
is unique up to unique isomorphism: any module `T` carrying a multilinear map `g` with the
same universal property is identified with it by a unique linear isomorphism `e` satisfying
`e ∘ tprod R = g`. Existence and the universal property itself are `PiTensorProduct.lift` and
`PiTensorProduct.lift.unique`.
-/

@[expose] public section

open scoped TensorProduct

namespace PiTensorProduct

universe u v w t

variable {ι : Type v} {R : Type u} [CommSemiring R] {s : ι → Type w}
  [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

/-- **Stacks 00CZ.** The tensor product is unique up to unique isomorphism: if a module `T`
and a multilinear map `g : Π i, s i → T` have the universal property (every multilinear map
`f` to a module `P` factors as `f' ∘ g` for a unique linear `f'`), then there is a unique
linear isomorphism `e : (⨂[R] i, s i) ≃ₗ[R] T` with `e ∘ tprod R = g`. -/
@[stacks 00CZ "Uniqueness clause: such a `T` is unique up to unique isomorphism; the existence
of `(T, g)` with the universal property is `PiTensorProduct.lift` with
`PiTensorProduct.lift.unique`."]
theorem existsUnique_linearEquiv_of_universal (T : Type t) [AddCommMonoid T] [Module R T]
    (g : MultilinearMap R s T)
    (hg : ∀ (P : Type (max u v w t)) [AddCommMonoid P] [Module R P] (f : MultilinearMap R s P),
      ∃! f' : T →ₗ[R] P, f'.compMultilinearMap g = f) :
    ∃! e : (⨂[R] i, s i) ≃ₗ[R] T, e.toLinearMap.compMultilinearMap (tprod R) = g := by
  obtain ⟨ψ', hψ', -⟩ := hg (ULift.{t} (⨂[R] i, s i))
    ((ULift.moduleEquiv (R := R)).symm.toLinearMap.compMultilinearMap (tprod R))
  let ψ : T →ₗ[R] ⨂[R] i, s i := (ULift.moduleEquiv (R := R)).toLinearMap ∘ₗ ψ'
  have hψx (x : Π i, s i) : ψ (g x) = tprod R x := by
    have := congrArg (fun F : MultilinearMap R s (ULift.{t} (⨂[R] i, s i)) => F x) hψ'
    simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe] at this
    simp only [ψ, LinearMap.comp_apply, this, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have hφ : (lift g).compMultilinearMap (tprod R) = g := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, lift.tprod]
  have h₁ : (lift g).comp ψ = LinearMap.id := by
    obtain ⟨_, -, huniq⟩ := hg (ULift.{max u v w} T)
      ((ULift.moduleEquiv (R := R)).symm.toLinearMap.compMultilinearMap g)
    have key := (huniq ((ULift.moduleEquiv (R := R)).symm.toLinearMap ∘ₗ (lift g).comp ψ)
      ?_).trans (huniq ((ULift.moduleEquiv (R := R)).symm.toLinearMap) ?_).symm
    · ext y
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
        LinearEquiv.symm_apply_eq, LinearEquiv.apply_symm_apply] using
        congrArg (ULift.moduleEquiv (R := R)) (LinearMap.congr_fun key y)
    · ext x
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hψx, lift.tprod]
    · ext x
      simp only [LinearMap.compMultilinearMap_apply]
  have h₂ : ψ.comp (lift g) = LinearMap.id := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, lift.tprod,
      LinearMap.id_apply, hψx]
  refine ⟨LinearEquiv.ofLinearMap (lift g) ψ h₁ h₂, hφ, fun e he => ?_⟩
  apply LinearEquiv.toLinearMap_injective
  exact PiTensorProduct.ext (he.trans hφ.symm)

end PiTensorProduct
