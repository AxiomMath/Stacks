module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksFrontier.Algebra.Homology.SpectralSequence.Kunneth

/-!
# The image of a morphism out of a total complex

A degree-`n` term of the total complex of a bicomplex is, by construction, the coproduct of the
terms `(K.X i₁).X i₂` with `π (i₁, i₂) = n`, and `HomologicalComplex₂.ιTotal` is the inclusion of
a summand. Mathlib exposes that coproduct only through `HomologicalComplex₂.totalDesc` and
`HomologicalComplex₂.total.hom_ext`, never as a `Sigma.desc`, so the lattice-theoretic statement
that an image of a coproduct map is the supremum of the summand images cannot be quoted for a
morphism out of a total complex.

**This file supplies that bridge**: a morphism out of `(K.total c₁₂).X i₁₂` is the `Sigma.desc` of
its restrictions to the summands, so the image of such a morphism is the least upper bound of the
images of its restrictions, and equals the image of one distinguished restriction as soon as that
one dominates the others.

The last form is the one the graded pieces of [Stacks, Section 0FMK] need. The `k`-th step of the
wedge filtration of `Ω^•_{X/S}` is the image of a morphism out of
`Tot(σ^{≥k}f^{-1}Ω^•_{Y/S} ⊗ Ω^•_{X/S})`, whose degree-`n` summand images decrease in the left
index, so in degree `n` the step is the image of the single summand
`f^{-1}Ω^k_{Y/S} ⊗ Ω^{n-k}_{X/S} ⟶ Ω^n_{X/S}`.

## Main results

* `HomologicalComplex₂.sigma_desc_ιTotal_comp`: a morphism out of a term of a total complex is the
  `Sigma.desc` of its restrictions to the summands.
* `HomologicalComplex₂.isLUB_imageSubobject_ιTotal_comp`: the image of such a morphism is the least
  upper bound of the images of its restrictions.
* `HomologicalComplex₂.imageSubobject_eq_of_isGreatest`: if one restriction's image dominates the
  others, the image of the morphism is that one.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GradedObject

namespace HomologicalComplex₂

variable {C : Type*} [Category C] [Abelian C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
  [DecidableEq I₁₂] [TotalComplexShape c₁ c₂ c₁₂]
  (K : HomologicalComplex₂ C c₁ c₂) [K.HasTotal c₁₂]

/-- **A morphism out of a term of a total complex is the sum of its restrictions to the
summands.** The term `(K.total c₁₂).X i₁₂` is the coproduct of the `(K.X i₁).X i₂` with
`π (i₁, i₂) = i₁₂`, and `HomologicalComplex₂.ιTotal` is the inclusion of a summand. -/
theorem sigma_desc_ιTotal_comp {Z : C} {i₁₂ : I₁₂} (W : (K.total c₁₂).X i₁₂ ⟶ Z) :
    Sigma.desc (f := K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c₁₂) i₁₂)
      (fun ij => K.ιTotal c₁₂ ij.1.1 ij.1.2 i₁₂ ij.2 ≫ W) = W := by
  refine (Sigma.hom_ext _ _ fun ij => ?_).symm
  rw [Sigma.ι_desc]
  rfl

/-- **The image of a morphism out of a term of a total complex is the least upper bound of the
images of its restrictions to the summands.** -/
theorem isLUB_imageSubobject_ιTotal_comp {Z : C} {i₁₂ : I₁₂} (W : (K.total c₁₂).X i₁₂ ⟶ Z) :
    IsLUB (Set.range (fun ij : (ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {i₁₂} =>
        imageSubobject (K.ιTotal c₁₂ ij.1.1 ij.1.2 i₁₂ ij.2 ≫ W)))
      (imageSubobject W) := by
  refine ⟨?_, fun Q hQ => ?_⟩
  · rintro _ ⟨ij, rfl⟩
    exact imageSubobject_comp_le _ _
  · have hf : ∀ (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂),
        Q.Factors (K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ W) := fun i₁ i₂ h =>
      Subobject.factors_of_le _ (hQ ⟨⟨(i₁, i₂), h⟩, rfl⟩)
        ((Subobject.factors_iff _ _).2 ⟨_, imageSubobject_arrow_comp _⟩)
    refine imageSubobject_le W
      (K.totalDesc (fun i₁ i₂ h => Q.factorThru (K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ W) (hf i₁ i₂ h))) ?_
    ext i₁ i₂ h
    simp

/-- **A dominating summand carries the whole image**: if the image of the restriction of `W` to
the summand `ij₀` contains the image of every other restriction, then it is the image of `W`. -/
theorem imageSubobject_eq_of_isGreatest {Z : C} {i₁₂ : I₁₂} (W : (K.total c₁₂).X i₁₂ ⟶ Z)
    (ij₀ : (ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {i₁₂})
    (h : ∀ ij : (ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {i₁₂},
      imageSubobject (K.ιTotal c₁₂ ij.1.1 ij.1.2 i₁₂ ij.2 ≫ W) ≤
        imageSubobject (K.ιTotal c₁₂ ij₀.1.1 ij₀.1.2 i₁₂ ij₀.2 ≫ W)) :
    imageSubobject W = imageSubobject (K.ιTotal c₁₂ ij₀.1.1 ij₀.1.2 i₁₂ ij₀.2 ≫ W) :=
  (isLUB_imageSubobject_ιTotal_comp K W).unique
    (IsGreatest.isLUB ⟨⟨ij₀, rfl⟩, by rintro _ ⟨ij, rfl⟩; exact h ij⟩)

end HomologicalComplex₂

end
