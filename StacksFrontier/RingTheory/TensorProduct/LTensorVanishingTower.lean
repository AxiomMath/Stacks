module

public import StacksFrontier.RingTheory.Flat.ZeroFunctorLimit

/-!
# Vanishing of an extension of scalars along a tower, and along an isomorphism

Let `R` be a commutative ring and `u : M →ₗ[R] N` a map of `R`-modules.  For an `R`-algebra `T`
the extension of scalars `T ⊗_R u` may or may not vanish, and this file records how that
condition moves between algebras:

* it is unchanged when `T` is replaced by an isomorphic `R`-algebra;
* it is inherited by any `T`-algebra;
* for a tower `R → A → T` it is the same condition for `u` and for its extension of scalars to
  `A`, the two tensor products being identified by
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`.

## Main results

* `Stacks.Flattening.lTensor_eq_zero_iff_of_algEquiv`: invariance under an isomorphism of
  `R`-algebras.
* `Stacks.Flattening.lTensor_eq_zero_of_tower`: vanishing over `A` gives vanishing over any
  `A`-algebra lying over `R`.
* `Stacks.Flattening.lTensor_baseChange_eq_zero_iff`: transitivity of base change, read as the
  equivalence of the two vanishing conditions.

## Implementation notes

Everything is reduced to `Stacks.Flattening.lTensor_eq_zero_iff`: the extension of scalars of
`u` to `T` vanishes exactly when `1 ⊗ u(m)` vanishes for every `m`, which is a condition on
*elements* and therefore transports along any `R`-linear map `T →ₗ[R] T'` carrying `1` to `1`.
The only statement for which that is not enough is the transitivity one, where the module on
the left is `A ⊗_R M` rather than `M`, and there the generators of the tensor product are run
through by `TensorProduct.induction_on`.

No flatness is used anywhere, and `M` is not assumed finite.
-/

@[expose] public section

open TensorProduct

namespace Stacks.Flattening

variable {R : Type*} [CommRing R]

section Target

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- Vanishing of `1 ⊗ n` transports along an `R`-linear map of `R`-algebras preserving `1`. -/
theorem one_tmul_eq_zero_of_map {T T' : Type*} [CommRing T] [CommRing T'] [Algebra R T]
    [Algebra R T'] (φ : T →ₗ[R] T') (hφ : φ 1 = 1) {n : N} (h : (1 : T) ⊗ₜ[R] n = 0) :
    (1 : T') ⊗ₜ[R] n = 0 := by
  have := congrArg (LinearMap.rTensor N φ) h
  rwa [LinearMap.rTensor_tmul, hφ, map_zero] at this

end Target

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **The extension of scalars of `u` to an `R`-algebra `T` vanishes exactly when it kills every
element `1 ⊗ m`.**  This is `Stacks.Flattening.lTensor_eq_zero_iff` with the two rings of its
tower taken to be the same ring, where the restriction of scalars is the identity. -/
theorem lTensor_eq_zero_iff_one_tmul (u : M →ₗ[R] N) (T : Type*) [CommRing T] [Algebra R T] :
    LinearMap.lTensor T u = 0 ↔ ∀ m : M, (1 : T) ⊗ₜ[R] u m = 0 :=
  lTensor_eq_zero_iff (A := R) (B := R) T u

/-- Vanishing of the extension of scalars transports along an equality of the maps. -/
theorem lTensor_eq_zero_congr {T : Type*} [CommRing T] [Algebra R T] {u : M →ₗ[R] N}
    (hu : LinearMap.lTensor T u = 0) {u' : M →ₗ[R] N} (h : u = u') :
    LinearMap.lTensor T u' = 0 :=
  (congrArg (LinearMap.lTensor T) h).symm.trans hu

/-- Vanishing of the extension of scalars of `u` transports along an `R`-algebra map. -/
private theorem lTensor_eq_zero_of_algHom (u : M →ₗ[R] N) {T T' : Type*} [CommRing T]
    [CommRing T'] [Algebra R T] [Algebra R T'] (f : T →ₐ[R] T')
    (h : LinearMap.lTensor T u = 0) : LinearMap.lTensor T' u = 0 := by
  rw [lTensor_eq_zero_iff_one_tmul] at h ⊢
  exact fun m => one_tmul_eq_zero_of_map f.toLinearMap (map_one f) (h m)

/-- **Vanishing of the extension of scalars of `u` is invariant under an isomorphism of
`R`-algebras.** -/
theorem lTensor_eq_zero_iff_of_algEquiv (u : M →ₗ[R] N) {T T' : Type*} [CommRing T]
    [CommRing T'] [Algebra R T] [Algebra R T'] (e : T ≃ₐ[R] T') :
    LinearMap.lTensor T u = 0 ↔ LinearMap.lTensor T' u = 0 := by
  exact ⟨lTensor_eq_zero_of_algHom u e.toAlgHom, lTensor_eq_zero_of_algHom u e.symm.toAlgHom⟩

/-- **Vanishing of the extension of scalars of `u` to `A` gives its vanishing over every
`A`-algebra lying over `R`.** -/
theorem lTensor_eq_zero_of_tower (u : M →ₗ[R] N) {A T : Type*} [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] [Algebra A T] [IsScalarTower R A T]
    (h : LinearMap.lTensor A u = 0) :
    LinearMap.lTensor T u = 0 := by
  exact lTensor_eq_zero_of_algHom u (IsScalarTower.toAlgHom R A T) h

/-- **Transitivity of base change, read on the vanishing conditions.**  For a tower
`R → A → T` the extension of scalars to `T` over `A` of the extension of scalars of `u` to `A`
vanishes exactly when the extension of scalars of `u` to `T` over `R` does.

The two tensor products are identified by
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, which sends `1 ⊗ (a ⊗ n)` to
`a • 1 ⊗ n`. -/
theorem lTensor_baseChange_eq_zero_iff (u : M →ₗ[R] N) (A T : Type*) [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] [Algebra A T] [IsScalarTower R A T] :
    LinearMap.lTensor T (LinearMap.baseChange A u) = 0 ↔ LinearMap.lTensor T u = 0 := by
  rw [lTensor_eq_zero_iff_one_tmul, lTensor_eq_zero_iff_one_tmul]
  have hcancel : ∀ (a : A) (n : N),
      TensorProduct.AlgebraTensorModule.cancelBaseChange R A T T N
          ((1 : T) ⊗ₜ[A] (a ⊗ₜ[R] n)) = (algebraMap A T a) ⊗ₜ[R] n := by
    intro a n
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
  refine ⟨fun h m => ?_, fun h x => ?_⟩
  · simpa [hcancel] using congrArg
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A T T N) (h ((1 : A) ⊗ₜ[R] m))
  · induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, TensorProduct.tmul_zero]
    | tmul a m =>
      rw [LinearMap.baseChange_tmul]
      refine (TensorProduct.AlgebraTensorModule.cancelBaseChange R A T T N).injective ?_
      rw [hcancel, map_zero, ← mul_one (algebraMap A T a), ← smul_eq_mul,
        ← TensorProduct.smul_tmul', h m, smul_zero]
    | add x y hx hy => rw [map_add, TensorProduct.tmul_add, hx, hy, add_zero]

/-- The two spellings of the extension of scalars of `u` to `T` — as a `T`-linear base change and
as a left tensor product — have the same vanishing condition, being the same function. -/
theorem baseChange_eq_zero_iff_lTensor (u : M →ₗ[R] N) (T : Type*) [CommRing T]
    [Algebra R T] :
    LinearMap.baseChange T u = 0 ↔ LinearMap.lTensor T u = 0 := by
  simp only [← DFunLike.coe_fn_eq, LinearMap.baseChange_eq_ltensor, funext_iff,
    LinearMap.zero_apply]

end Stacks.Flattening

end
