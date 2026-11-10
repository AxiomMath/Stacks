module

public import Mathlib.Algebra.Module.FinitePresentation
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLineBaseChange
public import StacksFrontier.Homology.TwoTermComplex.LineBaseChange

/-!
# The determinant line of a two-term complex commutes with flat base change

Let `R → A` be a flat map of commutative rings and let `K : K₁ → K₀` be a two-term complex of
finite projective `R`-modules. Its determinant line is the module of homomorphisms
`det(K₁) → det(K₀)`, and the comparison
`A ⊗_R Hom_R(det K₁, det K₀) ≅ Hom_A(det(A ⊗_R K₁), det(A ⊗_R K₀))`
identifies its base change with the determinant line of the base-changed complex. This file
reads that comparison on a pure tensor `1 ⊗ φ` and at the canonical element of a rank-zero
complex, which is carried to the canonical element of the base-changed complex.

## Main results

* `TwoTermComplex.determinantLineBaseChange_one_tmul`: the comparison on a pure tensor `1 ⊗ φ`
  is conjugation of the base-changed homomorphism by `ProjectiveDeterminant.baseChangeEquiv`.
* `TwoTermComplex.determinantLineBaseChange_one_tmul_delta`: **the comparison carries the
  canonical element `δ(K)` of a rank-zero two-term complex to `δ(A ⊗_R K)`.**

## Implementation notes

The comparison itself is `TwoTermComplex.determinantLineBaseChange` of
`StacksFrontier.Homology.TwoTermComplex.DeterminantLineBaseChange`, which needs no flatness: the
determinant line `det(K₁)` of a finite projective module is invertible by
`ProjectiveDeterminant.invertible`, hence finite projective, and the base change of a module of
homomorphisms out of such a module is an isomorphism.

`TwoTermComplex.finitePresentation_determinant` records that the determinant line is finitely
presented.

## References

* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TwoTermComplex

universe u v₁ v₀

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
variable {K₁ : Type u} [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁]
  [Module.Projective R K₁]
variable {K₀ : Type u} [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀]
  [Module.Projective R K₀]

/-- The determinant line of a finite projective module is finitely presented, being invertible
and hence finite projective. -/
theorem finitePresentation_determinant :
    Module.FinitePresentation R (ProjectiveDeterminant.module (R := R) (M := K₁)) :=
  have := ProjectiveDeterminant.invertible (R := R) (M := K₁)
  Module.finitePresentation_of_projective _ _

/-- The comparison `A ⊗_R det(K) ≅ det(A ⊗_R K)` on a pure tensor `1 ⊗ φ`: the base change of
the homomorphism, conjugated by `ProjectiveDeterminant.baseChangeEquiv`. -/
theorem determinantLineBaseChange_one_tmul (f : K₁ →ₗ[R] K₀) (φ : determinantLine f) :
    determinantLineBaseChange A f (1 ⊗ₜ[R] φ) =
      (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := A) (M := K₀)).toLinearMap.comp
        ((LinearMap.baseChange A φ).comp
          (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := A)
            (M := K₁)).symm.toLinearMap) := by
  rw [determinantLineBaseChange_tmul, one_smul]
  rfl

/-- **The comparison of determinant lines carries the canonical element of a rank-zero two-term
complex to the canonical element of its base change.** -/
theorem determinantLineBaseChange_one_tmul_delta {f : K₁ →ₗ[R] K₀} (hf : IsRankZero f) :
    determinantLineBaseChange A f (1 ⊗ₜ[R] delta f hf) =
      delta (LinearMap.baseChange A f) (isRankZero_baseChange A hf) := by
  rw [determinantLineBaseChange_tmul, one_smul, determinantLineBaseChangeMap_delta]

end TwoTermComplex

end
