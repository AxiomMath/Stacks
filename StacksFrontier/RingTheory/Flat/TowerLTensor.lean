module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Naturality of the heterobasic associator, and the flatness it transports

For a ring map `A → C`, a `C`-module `D` and a `C`-module `P` that is also an `A`-module over `C`,
the heterobasic associativity isomorphism `(D ⊗[C] P) ⊗[A] X ≅ D ⊗[C] (P ⊗[A] X)` is natural in
`X`. Consequently `(D ⊗[C] P) ⊗[A] u` is injective exactly when `D ⊗[C] (P ⊗[A] u)` is, and
flatness over `A` passes between `P` and `D ⊗[C] P`.

## Main results

* `TensorProduct.AlgebraTensorModule.assoc_comp_lTensor`: naturality in `X` of
  `(D ⊗[C] P) ⊗[A] X ≅ D ⊗[C] (P ⊗[A] X)`.
* `TensorProduct.AlgebraTensorModule.lTensor_baseChange_injective_iff`: `(D ⊗[C] P) ⊗[A] u` is
  injective if and only if `D ⊗[C] (P ⊗[A] u)` is.

* `Module.Flat.tensorProduct_of_flat_left`: if `P` is flat over `A` and `D` is flat over `C`, then
  `D ⊗[C] P` is flat over `A`.
* `Module.Flat.of_tensorProduct_of_faithfullyFlat`: conversely, if `D` is faithfully flat over `C`
  and `D ⊗[C] P` is flat over `A`, then `P` is flat over `A`.

## References

* [StacksProject 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public section

namespace TensorProduct.AlgebraTensorModule

variable {A C D P : Type*} [CommRing A] [CommRing C] [Algebra A C]
  [AddCommGroup D] [Module A D] [Module C D] [IsScalarTower A C D]
  [AddCommGroup P] [Module A P] [Module C P] [IsScalarTower A C P]
  {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]

/-- Naturality in `X` of the heterobasic associativity isomorphism
`(D ⊗_C P) ⊗_A X ≅ D ⊗_C (P ⊗_A X)`: it carries `(D ⊗_C P) ⊗_A u` to `D ⊗_C (P ⊗_A u)`. -/
theorem assoc_comp_lTensor (u : X →ₗ[A] Y) :
    (assoc A C C D P Y).toLinearMap ∘ₗ lTensor C (D ⊗[C] P) u =
      LinearMap.lTensor D (lTensor C P u) ∘ₗ assoc A C C D P X := by
  ext
  rfl

/-- Tensoring an `A`-linear map `u` with `D ⊗_C P` is, up to the associativity isomorphism,
tensoring `P ⊗_A u` with `D` over `C`; so the two have the same injectivity. -/
theorem lTensor_baseChange_injective_iff (u : X →ₗ[A] Y) :
    Function.Injective (LinearMap.lTensor (D ⊗[C] P) u) ↔
      Function.Injective (LinearMap.lTensor D (lTensor C P u)) := by
  rw [← coe_lTensor (A := C), ← EquivLike.comp_injective _ (assoc A C C D P Y),
    ← LinearEquiv.coe_coe, ← LinearMap.coe_comp, assoc_comp_lTensor, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp]

end TensorProduct.AlgebraTensorModule

namespace Module.Flat

open TensorProduct TensorProduct.AlgebraTensorModule

variable {A C D P : Type*} [CommRing A] [CommRing C] [Algebra A C]
  [AddCommGroup D] [Module A D] [Module C D] [IsScalarTower A C D]
  [AddCommGroup P] [Module A P] [Module C P] [IsScalarTower A C P]

/-- If `P` is a `C`-module which is flat over `A` and `D` is a flat `C`-module, then `D ⊗[C] P`
is flat over `A`. -/
theorem tensorProduct_of_flat_left [Module.Flat A P] [Module.Flat C D] :
    Module.Flat A (D ⊗[C] P) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ u hu
  rw [lTensor_baseChange_injective_iff]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := D) _
    (Module.Flat.lTensor_preserves_injective_linearMap (M := P) u hu)

/-- If `D` is a faithfully flat `C`-module and `D ⊗[C] P` is flat over `A`, then the `C`-module
`P` is flat over `A`. -/
theorem of_tensorProduct_of_faithfullyFlat [Module.FaithfullyFlat C D]
    [Module.Flat A (D ⊗[C] P)] : Module.Flat A P := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ u hu
  rw [← coe_lTensor (A := C),
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective (M := D) (f := lTensor C P u),
    ← lTensor_baseChange_injective_iff]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hu

end Module.Flat
