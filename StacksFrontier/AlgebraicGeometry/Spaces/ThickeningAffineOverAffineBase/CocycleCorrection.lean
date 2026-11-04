module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Membership in an image descends along a faithfully flat base change of a Čech square

Let `C → B` be faithfully flat and let `φ : M₀ → M₁`, `ψ : M₁ → M₂` be `C`-linear maps. Suppose
the base change `B ⊗ φ` of `φ` is identified with `ψ`, through a surjection
`ι₀ : B ⊗ M₀ → M₁` and an injection `ι₁ : B ⊗ M₁ → M₂`. Then an element `d : M₁` with
`ψ d = ι₁ (1 ⊗ d)` lies in the image of `φ`.

This is the descent step of the vanishing of the first Čech cohomology of a quasi-coherent
module along a faithfully flat covering: after the base change `B ⊗ -` the covering acquires a
section, the base-changed Čech differential becomes `ψ`, and the cocycle `d` is visibly the
coboundary of `ι₀⁻¹ d`; faithful flatness then brings the conclusion back down.

## Main results

* `TensorProduct.mem_range_of_lTensor_square`: the descent step.
-/

@[expose] public section

open TensorProduct

namespace TensorProduct

variable {C B M₀ M₁ M₂ : Type*} [CommRing C] [CommRing B] [Algebra C B]
  [Module.FaithfullyFlat C B]
  [AddCommGroup M₀] [Module C M₀] [AddCommGroup M₁] [Module C M₁]
  [AddCommGroup M₂] [Module C M₂]

/-- **Membership in the image of `φ` descends from the base-changed square.** If the base
change `B ⊗ φ` is identified with `ψ` through a surjection `ι₀` and an injection `ι₁`, then
every `d` with `ψ d = ι₁ (1 ⊗ d)` is in the range of `φ`. -/
theorem mem_range_of_lTensor_square (φ : M₀ →ₗ[C] M₁) (ψ : M₁ →ₗ[C] M₂)
    (ι₀ : B ⊗[C] M₀ →ₗ[C] M₁) (ι₁ : B ⊗[C] M₁ →ₗ[C] M₂)
    (h₀ : Function.Surjective ι₀) (h₁ : Function.Injective ι₁)
    (hc : ∀ y, ι₁ (φ.lTensor B y) = ψ (ι₀ y)) (d : M₁) (hd : ψ d = ι₁ ((1 : B) ⊗ₜ d)) :
    d ∈ LinearMap.range φ := by
  obtain ⟨y, rfl⟩ := h₀ d
  have hy : φ.lTensor B y = (1 : B) ⊗ₜ ι₀ y := h₁ (by rw [hc, hd])
  let π := (LinearMap.range φ).mkQ
  have h0 : (π.comp φ).lTensor B y = 0 := by
    have : π.comp φ = 0 := by
      ext x
      simp [π]
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]
  have h1 : (1 : B) ⊗ₜ[C] π (ι₀ y) = 0 := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply, hy] at h0
    simpa using h0
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h1
  simpa [π] using h1

end TensorProduct

end
