module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor-product comparison for a finite module, in an arbitrary universe

For a finite module `M` over a Noetherian ring `R`, the canonical map
`AdicCompletion I R ⊗[R] M → AdicCompletion I M` is bijective.

Mathlib's `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian` states this for `M`
in the same universe as `R`; here `M` may live in any universe.

## Main results

* `AdicCompletion.bijective_ofTensorProduct`: for a finite module `M` over a Noetherian ring `R`,
  `AdicCompletion.ofTensorProduct I M` is bijective.
-/

@[expose] public section

open TensorProduct

namespace AdicCompletion

/-- For a finite module `M` over a Noetherian ring `R`, the canonical map
`AdicCompletion I R ⊗[R] M → AdicCompletion I M` is bijective. Unlike
`AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`, `M` may live in any
universe. -/
@[ega "0 7.7.8" "B = Â"]
theorem bijective_ofTensorProduct {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective (AdicCompletion.ofTensorProduct I M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  set M' := (Fin n → R) ⧸ LinearMap.ker f
  have e : M' ≃ₗ[R] M := f.quotKerEquivOfSurjective hf
  set g : AdicCompletion I R ⊗[R] M' →ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] M :=
    AlgebraTensorModule.map LinearMap.id e.toLinearMap with hg
  have hbij : Function.Bijective g :=
    (AlgebraTensorModule.congr (LinearEquiv.refl (AdicCompletion I R) _) e).bijective
  refine (Function.Bijective.of_comp_iff _ hbij).mp ?_
  rw [hg, ← LinearMap.coe_comp, ← AdicCompletion.ofTensorProduct_naturality I e.toLinearMap]
  exact (AdicCompletion.congr I e).bijective.comp
    (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M')

end AdicCompletion
