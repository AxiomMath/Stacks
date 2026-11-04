module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The kernel of `m ↦ 1 ⊗ m` along a surjective ring map

Let `f : A →+* B` be a surjective homomorphism of commutative rings and `M` an `A`-module. The
base change `M ⟶ B ⊗_A M`, `m ↦ 1 ⊗ m`, is surjective onto the pure tensors of the form `1 ⊗ m`
and its kernel is `ker f · M`. This is the identification `B ⊗_A M = M / (ker f) M`, Mathlib's
`TensorProduct.quotTensorEquivQuotSMul` read through `B ≅ A / ker f`.

## Main results

* `TensorProduct.one_tmul_eq_zero_iff_of_surjective_ringHom`.
-/

@[expose] public section

namespace TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f)
  {M : Type*} [AddCommGroup M] [Module A M]

include hf in
/-- **`1 ⊗ m` vanishes in `B ⊗_A M` exactly when `m ∈ ker f · M`**, for a surjective `f`. -/
theorem one_tmul_eq_zero_iff_of_surjective_ringHom (m : M) :
    letI := f.toAlgebra
    ((1 : B) ⊗ₜ[A] m = 0) ↔ m ∈ (RingHom.ker f) • (⊤ : Submodule A M) := by
  let := f.toAlgebra
  let e : (A ⧸ RingHom.ker f) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hf
  let eT : (A ⧸ RingHom.ker f) ⊗[A] M ≃ₗ[A] B ⊗[A] M :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)
  have h1 : eT (1 ⊗ₜ m) = (1 : B) ⊗ₜ[A] m := by
    simp [eT]
  rw [← h1, LinearEquiv.map_eq_zero_iff,
    ← (quotTensorEquivQuotSMul M (RingHom.ker f)).map_eq_zero_iff,
    show (1 : A ⧸ RingHom.ker f) = Ideal.Quotient.mk _ 1 from rfl,
    quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero]

end TensorProduct

end
