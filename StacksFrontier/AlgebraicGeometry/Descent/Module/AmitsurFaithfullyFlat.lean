module

public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Amitsur exactness with module coefficients, in the equalizer range

Let `A` be a faithfully flat commutative `R`-algebra and let `M` be an arbitrary `R`-module.
The beginning of the Amitsur (extended Čech) cochain complex of `R → A` with coefficients in
`M` is
`M → A ⊗[R] M → (A ⊗[R] A) ⊗[R] M`,
where the first map is `m ↦ 1 ⊗ₜ m` and the second is `a ⊗ₜ m ↦ (a ⊗ₜ 1 - 1 ⊗ₜ a) ⊗ₜ m`.
This file proves that it is exact: the image of `M` is exactly the submodule on which the two
maps `A ⊗[R] M → (A ⊗[R] A) ⊗[R] M` induced by the two inclusions `A → A ⊗[R] A` agree.

Mathlib's `Algebra.IsEffective.of_faithfullyFlat` is the case `M = R`, up to the canonical
identification `A ⊗[R] R ≅ A`. The proof here is the same descent argument carried out with
coefficients: base change along the faithfully flat `R → A` and exhibit an explicit
contracting homotopy for the base-changed three-term complex, which is enough because
faithful flatness reflects exactness.

## Main results

* `Stacks.Descent.rTensor_includeLeftSubRight_comp_mk` says the two maps compose to zero.
* `Stacks.Descent.exact_mk_rTensor_includeLeftSubRight` is the exactness statement. Together
  with `Module.FaithfullyFlat.tensorProduct_mk_injective`, which gives injectivity of
  `m ↦ 1 ⊗ₜ m`, this says that `M` is the equalizer of the two inclusions with coefficients.

## Implementation notes

The contracting homotopy for the base change is the "multiply the two leading tensor factors"
map. Writing `e` for `m ↦ 1 ⊗ₜ m` and `d` for the difference of the two inclusions, it is the
map `s : A ⊗[R] ((A ⊗[R] A) ⊗[R] M) → A ⊗[R] (A ⊗[R] M)` sending `a ⊗ₜ ((b ⊗ₜ c) ⊗ₜ m)` to
`(a * b) ⊗ₜ (c ⊗ₜ m)`, and it satisfies `s ∘ (A ⊗ d) = (A ⊗ e) ∘ t - id` for the analogous
contraction `t : A ⊗[R] (A ⊗[R] M) → A ⊗[R] M`, `a ⊗ₜ (b ⊗ₜ m) ↦ (a * b) ⊗ₜ m`. Both are
built from `Algebra.TensorProduct.lmul'` and the associator, so the whole identity is a
single computation on pure tensors.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks.Descent

variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
  (M : Type w) [AddCommGroup M] [Module R M]

/-- Multiplication of the two leading tensor factors, `a ⊗ₜ (b ⊗ₜ m) ↦ (a * b) ⊗ₜ m`. -/
noncomputable def mulLeadingTwo : A ⊗[R] (A ⊗[R] M) →ₗ[R] A ⊗[R] M :=
  LinearMap.rTensor M (Algebra.TensorProduct.lmul' R (S := A)).toLinearMap ∘ₗ
    (TensorProduct.assoc R A A M).symm.toLinearMap

/-- Multiplication of the two leading factors of a triple tensor power of `A`. -/
noncomputable def mulLeadingTwoAlg : A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A :=
  LinearMap.rTensor A (Algebra.TensorProduct.lmul' R (S := A)).toLinearMap ∘ₗ
    (TensorProduct.assoc R A A A).symm.toLinearMap

/-- The contracting homotopy of the base-changed Amitsur complex:
`a ⊗ₜ ((b ⊗ₜ c) ⊗ₜ m) ↦ (a * b) ⊗ₜ (c ⊗ₜ m)`. -/
noncomputable def amitsurContraction :
    A ⊗[R] ((A ⊗[R] A) ⊗[R] M) →ₗ[R] A ⊗[R] (A ⊗[R] M) :=
  (TensorProduct.assoc R A A M).toLinearMap ∘ₗ
    LinearMap.rTensor M (mulLeadingTwoAlg R A) ∘ₗ
    (TensorProduct.assoc R A (A ⊗[R] A) M).symm.toLinearMap

/-- The defining property of `amitsurContraction`: it is a contracting homotopy for the
base change along `R → A` of the three-term Amitsur complex with coefficients in `M`. -/
theorem amitsurContraction_comp_lTensor :
    amitsurContraction R A M ∘ₗ
        LinearMap.lTensor A
          (LinearMap.rTensor M (Algebra.TensorProduct.includeLeftSubRight R A)) =
      LinearMap.lTensor A (TensorProduct.mk R A M 1) ∘ₗ mulLeadingTwo R A M -
        LinearMap.id := by
  ext a b m
  simp [amitsurContraction, mulLeadingTwo, mulLeadingTwoAlg, TensorProduct.tmul_sub,
    TensorProduct.sub_tmul]

/-- The two consecutive maps of the Amitsur complex with coefficients in `M` compose to zero. -/
theorem rTensor_includeLeftSubRight_comp_mk :
    LinearMap.rTensor M (Algebra.TensorProduct.includeLeftSubRight R A) ∘ₗ
        (TensorProduct.mk R A M 1) = 0 := by
  ext m
  simp

/-- **Stacks Lemma 023M, equalizer range.** For a faithfully flat `R`-algebra `A` and an
arbitrary `R`-module `M`, the complex `M → A ⊗[R] M → (A ⊗[R] A) ⊗[R] M` is exact at
`A ⊗[R] M`: an element of `A ⊗[R] M` killed by the difference of the two inclusions is
`1 ⊗ₜ m` for some `m : M`. -/
@[sga "1 VIII 1.5" "partial"]
theorem exact_mk_rTensor_includeLeftSubRight [Module.FaithfullyFlat R A] :
    Function.Exact (TensorProduct.mk R A M 1)
      (LinearMap.rTensor M (Algebra.TensorProduct.includeLeftSubRight R A)) := by
  refine Module.FaithfullyFlat.lTensor_reflects_exact R A _ _ ?_
  intro z
  refine ⟨fun hz => ⟨mulLeadingTwo R A M z, ?_⟩, ?_⟩
  · have h := congr($(amitsurContraction_comp_lTensor R A M) z)
    simp only [LinearMap.comp_apply, hz, map_zero, LinearMap.sub_apply,
      LinearMap.id_apply] at h
    exact sub_eq_zero.mp h.symm
  · rintro ⟨y, rfl⟩
    have h := congr($(congrArg (LinearMap.lTensor A)
      (rTensor_includeLeftSubRight_comp_mk R A M)) y)
    simpa [LinearMap.lTensor_comp] using h

end Stacks.Descent

end
