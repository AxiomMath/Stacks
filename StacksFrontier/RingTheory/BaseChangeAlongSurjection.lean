module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change along a surjective ring map

Let `S` be a commutative `A`-algebra whose structure map `A → S` is **surjective**, and let
`f : M → N` exhibit the `S`-module `N` as the base change of the `A`-module `M`. Then `f` is a
surjection with kernel `I • M`, where `I = ker (A → S)`: the base change along a surjection is
a quotient.

## Main results

* `IsBaseChange.surjective_of_surjective_algebraMap`: the base change of a module along a
  surjective ring map is a surjection.
* `IsBaseChange.eq_zero_iff_mem_ker_smul_top`: its kernel is `ker (A → S) • M`.
* `IsBaseChange.of_surjective_of_ker_eq_ker_smul_top`: conversely, a surjection of an
  `A`-module onto an `S`-module with kernel `ker (A → S) • M` is a base change.

## Implementation notes

Surjectivity is `IsBaseChange.inductionOn`, using that `s • f m = f (a • m)` whenever `s` is
the image of `a`. The kernel is computed by comparing `S ⊗[A] M` with
`(A ⧸ I) ⊗[A] M ≃ₗ[A] M ⧸ I • ⊤`, i.e. `TensorProduct.quotTensorEquivQuotSMul`, along the
isomorphism `A ⧸ ker (A → S) ≃ₐ[A] S` of `Ideal.quotientKerAlgEquivOfSurjective`. No flatness
and no finiteness are used.
-/

@[expose] public section

open TensorProduct

namespace IsBaseChange

variable {A S M N : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
  [Module A M] [AddCommGroup N] [Module A N] [Module S N] [IsScalarTower A S N]

/-- **The base change of a module along a surjective ring map is a surjection.** -/
theorem surjective_of_surjective_algebraMap {f : M →ₗ[A] N} (hf : IsBaseChange S f)
    (hs : Function.Surjective (algebraMap A S)) : Function.Surjective f := by
  intro z
  refine hf.inductionOn (motive := fun n => ∃ y : M, f y = n) z (fun m => ⟨m, rfl⟩)
    (fun s n hn => ?_) fun n₁ n₂ h₁ h₂ => ?_
  · obtain ⟨y, rfl⟩ := hn
    obtain ⟨a, rfl⟩ := hs s
    exact ⟨a • y, by rw [map_smul, IsScalarTower.algebraMap_smul]⟩
  · obtain ⟨y₁, rfl⟩ := h₁
    obtain ⟨y₂, rfl⟩ := h₂
    exact ⟨y₁ + y₂, map_add f y₁ y₂⟩

/-- **The kernel of a base change along a surjective ring map is `I • M`**, for `I` the kernel of
the ring map. -/
theorem eq_zero_iff_mem_ker_smul_top {f : M →ₗ[A] N} (hf : IsBaseChange S f)
    (hs : Function.Surjective (algebraMap A S)) (y : M) :
    f y = 0 ↔ y ∈ RingHom.ker (algebraMap A S) • (⊤ : Submodule A M) := by
  let eA : (A ⧸ RingHom.ker (algebraMap A S)) ≃ₐ[A] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A S) hs
  let e : S ⊗[A] M ≃ₗ[A]
      M ⧸ RingHom.ker (algebraMap A S) • (⊤ : Submodule A M) :=
    TensorProduct.congr eA.symm.toLinearEquiv (LinearEquiv.refl A M) ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker (algebraMap A S))
  have he : e ((1 : S) ⊗ₜ[A] y) = Submodule.Quotient.mk y := by
    have h1 : eA.symm.toLinearEquiv (1 : S) = (1 : A ⧸ RingHom.ker (algebraMap A S)) :=
      map_one eA.symm
    rw [LinearEquiv.trans_apply, TensorProduct.congr_tmul, h1, LinearEquiv.refl_apply,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  have hequiv : hf.equiv ((1 : S) ⊗ₜ[A] y) = f y := by
    rw [hf.equiv_tmul, one_smul]
  constructor
  · intro hy
    have h0 : (1 : S) ⊗ₜ[A] y = 0 := by
      refine hf.equiv.injective ?_
      rw [hequiv, hy, map_zero]
    have hmk : (Submodule.Quotient.mk y :
        M ⧸ RingHom.ker (algebraMap A S) • (⊤ : Submodule A M)) = 0 := by
      rw [← he, h0, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mp hmk
  · intro hy
    have hmk : (Submodule.Quotient.mk y :
        M ⧸ RingHom.ker (algebraMap A S) • (⊤ : Submodule A M)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hy
    have h0 : (1 : S) ⊗ₜ[A] y = 0 := by
      refine e.injective ?_
      rw [he, hmk, map_zero]
    rw [← hequiv, h0, map_zero]

/-- **A surjection with kernel `I • M` is a base change.** Conversely to the two results above,
for a surjective `A → S` with kernel `I` a surjection `f : M → N` of an `A`-module onto an
`S`-module whose kernel is `I • M` exhibits `N` as `S ⊗[A] M`. -/
theorem of_surjective_of_ker_eq_ker_smul_top
    (hs : Function.Surjective (algebraMap A S)) {f : M →ₗ[A] N}
    (hfs : Function.Surjective f)
    (hker : LinearMap.ker f = RingHom.ker (algebraMap A S) • (⊤ : Submodule A M)) :
    IsBaseChange S f := by
  have h₀ : IsBaseChange S (TensorProduct.mk A S M 1) := TensorProduct.isBaseChange A M S
  have hmksurj : Function.Surjective (TensorProduct.mk A S M 1) :=
    h₀.surjective_of_surjective_algebraMap hs
  have hmkzero : ∀ y : M, (TensorProduct.mk A S M 1) y = 0 ↔
      y ∈ RingHom.ker (algebraMap A S) • (⊤ : Submodule A M) :=
    h₀.eq_zero_iff_mem_ker_smul_top hs
  have hlift : ∀ x : M, (h₀.lift f) ((TensorProduct.mk A S M 1) x) = f x := h₀.lift_eq f
  have hbij : Function.Bijective (h₀.lift f) := by
    refine ⟨?_, ?_⟩
    · intro z w hzw
      obtain ⟨x, rfl⟩ := hmksurj z
      obtain ⟨y, rfl⟩ := hmksurj w
      rw [hlift, hlift] at hzw
      have hmem : x - y ∈ RingHom.ker (algebraMap A S) • (⊤ : Submodule A M) := by
        rw [← hker]
        change f (x - y) = 0
        rw [map_sub, hzw, sub_self]
      have hz := (hmkzero (x - y)).2 hmem
      rwa [map_sub, sub_eq_zero] at hz
    · intro y
      obtain ⟨x, rfl⟩ := hfs y
      exact ⟨(TensorProduct.mk A S M 1) x, hlift x⟩
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective (h₀.lift f) hbij) hlift

end IsBaseChange

end
