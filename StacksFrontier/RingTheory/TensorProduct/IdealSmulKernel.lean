module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The kernel of the multiplication map `J ⊗ M → J M` is killed by `J`

Let `A` be a commutative ring, `M` an `A`-module and `J ⊆ A` an ideal. Multiplication
`a ⊗ m ↦ a • m` is a surjection of `J ⊗[A] M` onto the submodule `J • M` of `M`, and its kernel
is annihilated by `J`. Neither a Noetherian hypothesis on `A` nor finite generation of `M` is
required.

## Main definitions

* `Stacks.IdealTensor.smulMap`: the multiplication map `N ⊗[A] M →ₗ[A] M`, `n ⊗ m ↦ ι n • m`,
  attached to an `A`-linear map `ι : N →ₗ[A] A`.

## Main results

* `Stacks.IdealTensor.smulMap_comp_mk`: for `b : N` the composite of `smulMap ι` with
  `m ↦ b ⊗ m` is multiplication by `ι b`.
* `Stacks.IdealTensor.smul_eq_zero_of_smulMap_eq_zero`: an element of the kernel of `smulMap ι`
  is killed by every `ι b`.
* `Ideal.smul_ker_smulMap_subtype_eq_bot`: for an ideal `J` of `A`, the kernel of the
  multiplication map `J ⊗[A] M →ₗ[A] M` is annihilated by `J`.
* `Ideal.smulMap_subtype_eq` and `Ideal.range_smulMap_subtype`: for an ideal that map is the
  composite of `LinearMap.rTensor` with `TensorProduct.lid`, and its range is `J • M`.

## Implementation notes

The results are stated for an arbitrary `A`-linear map `ι : N →ₗ[A] A` subject to the
commutativity `ι n • n' = ι n' • n` enjoyed by the inclusion of an ideal, so that they apply to
a module `N` that is not literally a submodule of `A`.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.IdealTensor

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
  [Module A N]

/-- The multiplication map `N ⊗[A] M →ₗ[A] M`, `n ⊗ m ↦ ι n • m`, attached to an `A`-linear map
`ι : N →ₗ[A] A`. -/
noncomputable def smulMap (ι : N →ₗ[A] A) : N ⊗[A] M →ₗ[A] M :=
  TensorProduct.lift ((LinearMap.lsmul A M).comp ι)

/-- The multiplication map `smulMap ι` sends the pure tensor `n ⊗ₜ m` to `ι n • m`. -/
@[simp]
lemma smulMap_tmul (ι : N →ₗ[A] A) (n : N) (m : M) :
    smulMap ι (n ⊗ₜ[A] m) = ι n • m :=
  rfl

/-- Suppose `ι : N →ₗ[A] A` satisfies the commutativity `ι n • n' = ι n' • n` enjoyed by the
inclusion of an ideal. Then for every `b : N` the composite of the multiplication map
`smulMap ι` with `m ↦ b ⊗ m` is multiplication by `ι b` on `N ⊗[A] M`. -/
lemma smulMap_comp_mk (ι : N →ₗ[A] A) (hι : ∀ n n' : N, ι n • n' = ι n' • n) (b : N)
    (z : N ⊗[A] M) :
    b ⊗ₜ[A] smulMap ι z = ι b • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul n m =>
      rw [smulMap_tmul, ← TensorProduct.smul_tmul, hι n b, TensorProduct.smul_tmul']
  | add z w hz hw => rw [map_add, TensorProduct.tmul_add, hz, hw, smul_add]

/-- If `ι : N →ₗ[A] A` satisfies the commutativity `ι n • n' = ι n' • n` enjoyed by the inclusion
of an ideal, then an element of `N ⊗[A] M` killed by the multiplication map `smulMap ι` is killed
by every scalar in the range of `ι`. -/
theorem smul_eq_zero_of_smulMap_eq_zero (ι : N →ₗ[A] A) (hι : ∀ n n' : N, ι n • n' = ι n' • n)
    (b : N) {z : N ⊗[A] M} (hz : smulMap ι z = 0) : ι b • z = 0 := by
  rw [← smulMap_comp_mk ι hι b z, hz, TensorProduct.tmul_zero]

end Stacks.IdealTensor

namespace Ideal

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- For elements `a b` of an ideal `J` of `A`, the scalar `(a : A)` acts on `b` as `(b : A)` acts
on `a`. -/
lemma smul_comm_subtype (J : Ideal A) (a b : J) : (J.subtype a) • b = (J.subtype b) • a :=
  Subtype.ext (mul_comm (a : A) (b : A))

/-- For an ideal `J` of a commutative ring `A` and any `A`-module `M`, the multiplication map
`J ⊗[A] M →ₗ[A] M`, `a ⊗ m ↦ a • m`, has kernel annihilated by `J`. -/
theorem smul_ker_smulMap_subtype_eq_bot (J : Ideal A) :
    J • LinearMap.ker (Stacks.IdealTensor.smulMap (M := M) J.subtype) = ⊥ :=
  le_antisymm
    (Submodule.smul_le.2 fun a ha _z hz ↦
      (Stacks.IdealTensor.smul_eq_zero_of_smulMap_eq_zero J.subtype (J.smul_comm_subtype)
        ⟨a, ha⟩ hz) ▸ Submodule.zero_mem _)
    bot_le

/-- For an ideal `J` of `A`, the map `Stacks.IdealTensor.smulMap` of its inclusion is the
composite of `LinearMap.rTensor` with `TensorProduct.lid`. -/
theorem smulMap_subtype_eq (J : Ideal A) :
    Stacks.IdealTensor.smulMap (M := M) J.subtype =
      (TensorProduct.lid A M).toLinearMap.comp (J.subtype.rTensor M) :=
  TensorProduct.ext' fun _ _ ↦ rfl

/-- The multiplication map `J ⊗[A] M →ₗ[A] M` has range the submodule `J • M` of `M`. -/
theorem range_smulMap_subtype (J : Ideal A) :
    LinearMap.range (Stacks.IdealTensor.smulMap (M := M) J.subtype) =
      J • (⊤ : Submodule A M) := by
  rw [smulMap_subtype_eq]
  exact J.subtype_rTensor_range M

end Ideal

end
