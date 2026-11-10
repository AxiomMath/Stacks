module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Length

/-!
# The determinant of an exact one-differential periodic complex

For an exact two-periodic complex whose two differentials are the same, the periodic
determinant is the sign determined by the length of the image, equivalently by half the length
of the module.

## Main results

* `AlgebraicGeometry.periodicDeterminant_self_eq_negOne_pow_range_length` computes the
  determinant using the length of the image of the differential.
* `AlgebraicGeometry.periodicDeterminant_self_eq_negOne_pow_half_length` computes it using
  half the length of the module.

## Implementation notes

The exact complex `(M, φ, φ)` is expressed by `Function.Exact φ φ`. The two equalities of the
source are stated separately. The sign is a unit in the residue field, and lengths are natural
numbers because `M` has finite length.

## References

* [Stacks Project, Tag 02PM](https://stacks.math.columbia.edu/tag/02PM)
-/

@[expose] public section

open scoped TensorProduct

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

/-- On a one-dimensional space the tensor symmetry is the identity. -/
private theorem tensorProduct_comm_eq_id_of_finrank_eq_one
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    (hV : Module.finrank K V = 1) :
    (TensorProduct.comm K V V).toLinearMap = LinearMap.id := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (by simpa using hV)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hvspan := (finrank_eq_one_iff_of_nonzero' v hv).mp hV
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      obtain ⟨a, rfl⟩ := hvspan x
      obtain ⟨b, rfl⟩ := hvspan y
      change TensorProduct.comm K V V ((a • v) ⊗ₜ[K] (b • v)) =
        (a • v) ⊗ₜ[K] (b • v)
      rw [TensorProduct.comm_tmul]
      simp only [TensorProduct.smul_tmul_smul, mul_comm]

/-- **Stacks Project, Tag 02PM.** The determinant of an exact one-differential periodic
complex is the sign of the length of the image of its differential. -/
@[stacks 02PM "periodic_determinant_sign"]
theorem periodicDeterminant_self_eq_negOne_pow_range_length
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ : M →ₗ[R] M) (hφ : Function.Exact φ φ) (hM : IsFiniteLength R M) :
    periodicDeterminant φ φ hφ hφ hM =
      (-1 : (IsLocalRing.ResidueField R)ˣ) ^ moduleLength R (LinearMap.range φ) := by
  let K := IsLocalRing.ResidueField R
  let D := determinant R (LinearMap.range φ)
  let a := moduleLength R (LinearMap.range φ)
  refine (eq_periodicDeterminant φ φ hφ hφ hM ?_).symm
  change periodicGamma φ φ hφ hM ∘ₗ (TensorProduct.comm K D D).toLinearMap =
    (((-1 : K) ^ (a * a) * (((-1 : Kˣ) ^ a : Kˣ) : K)) • periodicGamma φ φ hφ hM)
  rw [tensorProduct_comm_eq_id_of_finrank_eq_one (finrank_determinant_eq_one
    (hM.of_injective (LinearMap.range φ).subtype_injective)), LinearMap.comp_id]
  suffices (-1 : K) ^ (a * a) * (((-1 : Kˣ) ^ a : Kˣ) : K) = 1 by
    rw [this, one_smul]
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← pow_add,
    show a * a + a = a * (a + 1) by ring]
  exact (Nat.even_mul_succ_self a).neg_one_pow

/-- **Stacks Project, Tag 02PM.** The same determinant is the sign of half the length of the
underlying module. -/
@[stacks 02PM "periodic_determinant_sign"]
theorem periodicDeterminant_self_eq_negOne_pow_half_length
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ : M →ₗ[R] M) (hφ : Function.Exact φ φ) (hM : IsFiniteLength R M) :
    periodicDeterminant φ φ hφ hφ hM =
      (-1 : (IsLocalRing.ResidueField R)ˣ) ^ (moduleLength R M / 2) := by
  rw [periodicDeterminant_self_eq_negOne_pow_range_length φ hφ hM]
  have hlen : moduleLength R M = 2 * moduleLength R (LinearMap.range φ) := by
    simpa [moduleLength] using
      congrArg ENat.toNat (Module.length_eq_twice_image_length φ hφ)
  congr 1
  omega

end AlgebraicGeometry
