module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.VanishingAfterBaseChange
public import StacksFrontier.RingTheory.TensorProduct.LTensorVanishingTower

/-!
# The flattening ideal of Stacks 083L at an extension of scalars over `C`

Let `R → C` be a ring map and let `u : M ⟶ N` be a map of `C`-modules whose target is
projective over `R`.  There is an ideal `I` of `R` such that, for every ring map `φ : R → A`, the
extension of scalars of `u` over `C` to `C ⊗_R A` vanishes exactly when `I ≤ \ker φ`.

## Main results

* `Stacks.Flattening.one_tmul_tensorProduct_eq_zero_iff`: `1 ⊗ n` vanishes in
  `(C ⊗_R A) ⊗_C N` exactly when it vanishes in `A ⊗_R N`.
* `Stacks.Flattening.lTensor_tensorProduct_eq_zero_iff`: the extension of scalars of `u` over `C`
  to `C ⊗_R A` vanishes exactly when its extension of scalars over `R` to `A` does.
* `Stacks.Flattening.rTensor_eq_zero_iff_lTensor`: the two sides of a tensor product give the
  same vanishing condition.
* `Stacks.Flattening.exists_ideal_lTensor_tensorProduct_eq_zero_iff`: an ideal `I` of `R` with,
  for every ring map `φ : R → A`, the extension of scalars of `u` to `C ⊗_R A` vanishing exactly
  when `I ≤ \ker φ`.

## References

* [Stacks Project, Tag 083L](https://stacks.math.columbia.edu/tag/083L)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Flattening

universe u v w

variable {R : Type u} [CommRing R] {C : Type v} [CommRing C] [Algebra R C]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module C M] [IsScalarTower R C M]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module C N] [IsScalarTower R C N]

/-- **`1 ⊗ n` vanishes after extension of scalars over `C` to `C ⊗_R A` exactly when it
vanishes after extension of scalars over `R` to `A`.** -/
theorem one_tmul_tensorProduct_eq_zero_iff (A : Type*) [CommRing A] [Algebra R A] (n : N) :
    (1 : TensorProduct R C A) ⊗ₜ[C] n = 0 ↔ (1 : A) ⊗ₜ[R] n = 0 := by
  have hval : (TensorProduct.comm R N A)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R C C N A)
        ((TensorProduct.comm C (TensorProduct R C A) N)
          ((1 : TensorProduct R C A) ⊗ₜ[C] n))) = (1 : A) ⊗ₜ[R] n := by
    rw [show (1 : TensorProduct R C A) = (1 : C) ⊗ₜ[R] (1 : A) from
        Algebra.TensorProduct.one_def,
      TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      one_smul, TensorProduct.comm_tmul]
  rw [← hval]
  simp only [LinearEquiv.map_eq_zero_iff]

/-- **The extension of scalars of `u` over `C` to `C ⊗_R A` vanishes exactly when its extension
of scalars over `R` to `A` does.** -/
theorem lTensor_tensorProduct_eq_zero_iff (u : M →ₗ[C] N) (A : Type*) [CommRing A]
    [Algebra R A] :
    LinearMap.lTensor (TensorProduct R C A) u = 0 ↔
      LinearMap.lTensor A (u.restrictScalars R) = 0 := by
  rw [lTensor_eq_zero_iff_one_tmul u (TensorProduct R C A), lTensor_eq_zero_iff A u]
  exact forall_congr' fun m => one_tmul_tensorProduct_eq_zero_iff A (u m)

end Stacks.Flattening

namespace Stacks.Flattening

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

/-- **The two sides of a tensor product give the same vanishing condition.**  The extension of
scalars of `u : M →ₗ[R] N` to `A` written on the right vanishes exactly when the one written on
the left does. -/
theorem rTensor_eq_zero_iff_lTensor (u : M →ₗ[R] N) (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.rTensor A u = 0 ↔ LinearMap.lTensor A u = 0 := by
  rw [← LinearMap.comm_comp_rTensor_comp_comm_eq (Q := A) u]
  simp [LinearMap.ext_iff, (TensorProduct.comm R A M).surjective.forall]

end Stacks.Flattening

namespace Stacks.Flattening

universe u v w

variable {R : Type u} [CommRing R] {C : Type u} [CommRing C] [Algebra R C]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module C M] [IsScalarTower R C M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module C N] [IsScalarTower R C N]

/-- For a map `u` of `C`-modules whose target is projective over `R` there is an ideal `I` of `R`
such that, for every ring map `φ : R → A`, the extension of scalars of `u` over `C` to `C ⊗_R A`
vanishes exactly when `I ≤ \ker φ`. -/
theorem exists_ideal_lTensor_tensorProduct_eq_zero_iff (u : M →ₗ[C] N)
    (hN : Module.Projective R N) :
    ∃ I : Ideal R, ∀ (A : Type u) [CommRing A] (φ : R →+* A),
      letI := φ.toAlgebra
      (LinearMap.lTensor (TensorProduct R C A) u = 0 ↔ I ≤ RingHom.ker φ) := by
  obtain ⟨I, hI⟩ :=
    Module.exists_ideal_rTensor_eq_zero_iff_map_eq_bot.{u, v, w, u} (u.restrictScalars R) hN
  refine ⟨I, fun A _ φ => ?_⟩
  let := φ.toAlgebra
  rw [lTensor_tensorProduct_eq_zero_iff u A,
    ← rTensor_eq_zero_iff_lTensor (u.restrictScalars R) A, hI A φ, Ideal.map_eq_bot_iff_le_ker]

end Stacks.Flattening

namespace Stacks.Flattening

universe u v

variable {R : Type u} [CommRing R] {C : Type u} [CommRing C]

/-- `Stacks.Flattening.exists_ideal_lTensor_tensorProduct_eq_zero_iff` with the `R`-algebra
structure on `C` and the `R`-module structures on `M` and `N` given by a ring map `f : R →+* C`:
for a map `u` of `C`-modules whose target is projective over `R` there is an ideal `I` of `R` such
that, for every ring map `φ : R → A`, the extension of scalars of `u` over `C` to `C ⊗_R A`
vanishes exactly when `I ≤ \ker φ`. -/
theorem exists_ideal_lTensor_tensorProduct_eq_zero_iff_of_ringHom (f : R →+* C)
    {M : Type v} [AddCommGroup M] [Module C M]
    {N : Type v} [AddCommGroup N] [Module C N] (u : M →ₗ[C] N)
    (hN : letI := Module.compHom N f; Module.Projective R N) :
    letI := f.toAlgebra
    ∃ I : Ideal R, ∀ (A : Type u) [CommRing A] (φ : R →+* A),
      letI := φ.toAlgebra
      (LinearMap.lTensor (TensorProduct R C A) u = 0 ↔ I ≤ RingHom.ker φ) := by
  let := f.toAlgebra
  let _ : Module R M := Module.compHom M f
  let _ : Module R N := Module.compHom N f
  have : IsScalarTower R C M := ⟨fun r c m => mul_smul (f r) c m⟩
  have : IsScalarTower R C N := ⟨fun r c n => mul_smul (f r) c n⟩
  exact exists_ideal_lTensor_tensorProduct_eq_zero_iff u hN

end Stacks.Flattening

end
