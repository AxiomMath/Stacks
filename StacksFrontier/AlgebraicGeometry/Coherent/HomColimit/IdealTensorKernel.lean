module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The kernel of `I ⊗_A M ⟶ I M` is annihilated by `I`

For a commutative ring `A`, an ideal `I` and an `A`-module `M`, the canonical map

`I ⊗_A M ⟶ M`,  `a ⊗ m ↦ a • m`

has image `I M`, and its kernel `K` satisfies `I K = 0`.  The vanishing is the step that
[Stacks, Tag 01YB] states as "note that `Iⁿ 𝒦 = 0` (proof omitted)", for `I` replaced by a power
of a sheaf of ideals; stated for an arbitrary ideal it covers that case.

The vanishing holds because multiplication by `a ∈ I` on `I ⊗_A M` factors through the
canonical map: `a • ξ = a ⊗ (I ⊗_A M ⟶ M) ξ`.

## Main definitions

* `Stacks.Algebra.IdealTensor.idealTensorToSmul`: the canonical map `I ⊗_A M ⟶ M`.

## Main results

* `Stacks.Algebra.IdealTensor.range_idealTensorToSmul`: its image is `I M`, so it is the
  surjection `I ⊗_A M ⟶ I M`.
* `Stacks.Algebra.IdealTensor.smul_eq_tmul_idealTensorToSmul`: multiplication by an element of
  `I` on `I ⊗_A M` factors through the canonical map.
* `Stacks.Algebra.IdealTensor.smul_ker_idealTensorToSmul`: **`I · ker(I ⊗_A M ⟶ I M) = 0`.**

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Algebra.IdealTensor

variable {A : Type*} [CommRing A] (I : Ideal A)
  (M : Type*) [AddCommGroup M] [Module A M]

/-- **The canonical map `I ⊗_A M ⟶ M`**, sending `a ⊗ m` to `a • m`. -/
public noncomputable def idealTensorToSmul : ↥I ⊗[A] M →ₗ[A] M :=
  TensorProduct.lift ((LinearMap.lsmul A M).comp I.subtype)

/-- The canonical map `I ⊗_A M ⟶ M` sends the pure tensor `a ⊗ m` to `a • m`. -/
@[simp] public theorem idealTensorToSmul_tmul (a : ↥I) (m : M) :
    idealTensorToSmul I M (a ⊗ₜ[A] m) = (a : A) • m := rfl

/-- **The image of `I ⊗_A M ⟶ M` is `I M`**, so the canonical map is a surjection onto
`I M`. -/
public theorem range_idealTensorToSmul :
    LinearMap.range (idealTensorToSmul I M) = I • (⊤ : Submodule A M) := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨ξ, rfl⟩ := hy
    induction ξ using TensorProduct.inductionOn with
    | tmul x m => exact Submodule.smul_mem_smul x.2 Submodule.mem_top
    | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  · rw [Submodule.smul_le]
    intro a ha m _
    exact ⟨(⟨a, ha⟩ : ↥I) ⊗ₜ[A] m, rfl⟩

/-- **Multiplication by an element of `I` on `I ⊗_A M` factors through the canonical map**:
for all `a ∈ I` and `ξ ∈ I ⊗_A M`, `a • ξ = a ⊗ (I ⊗_A M ⟶ M) ξ`. -/
public theorem smul_eq_tmul_idealTensorToSmul {a : A} (ha : a ∈ I) (ξ : ↥I ⊗[A] M) :
    a • ξ = (⟨a, ha⟩ : ↥I) ⊗ₜ[A] idealTensorToSmul I M ξ := by
  induction ξ using TensorProduct.inductionOn with
  | tmul x m =>
      rw [TensorProduct.smul_tmul', idealTensorToSmul_tmul, ← TensorProduct.smul_tmul]
      exact congrArg (fun y : ↥I ↦ y ⊗ₜ[A] m) (Subtype.ext (mul_comm a (x : A)))
  | add p q hp hq => rw [smul_add, hp, hq, map_add, tmul_add]

/-- **`I · ker(I ⊗_A M ⟶ I M) = 0`**: `I` annihilates the kernel of the canonical map. -/
public theorem smul_ker_idealTensorToSmul :
    I • LinearMap.ker (idealTensorToSmul I M) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.mpr fun a ha ξ hξ ↦ ?_) bot_le
  rw [Submodule.mem_bot, smul_eq_tmul_idealTensorToSmul I M ha ξ,
    LinearMap.mem_ker.mp hξ, tmul_zero]

end Stacks.Algebra.IdealTensor

end
