module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization

/-!
# The associator of the monoidal derived category, on K-flat representatives

The symmetric monoidal structure on `D(A)` of `CochainComplex.KFlatMonoidal.derivedMonoidal` is
obtained by localizing twice and no coherence constraint is computed there. This file computes
the associator on the images of complexes, at each of the two localizations, and then on the
comparison isomorphism `CochainComplex.KFlatMonoidal.derivedTensorIso` which identifies the
tensor product of `D(A)` with the total tensor product of K-flat complexes.

This is the clause of Stacks Tag 0FPT that
`StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat` records as absent: the
compatibility of the K-flat comparison with the associator, stated as a checkable equation rather
than held to be true by construction.

## Main results

* `CochainComplex.KFlatMonoidal.homotopyMu_associator`: the associator of `K(A)` on images of
  complexes, in terms of the comparison of the first localization.
* `CochainComplex.KFlatMonoidal.derivedMu_associator`: the associator of `D(A)` on images of
  K-flat objects of `K(A)`, in terms of the comparison of the second localization.

## Implementation notes

Each statement is an instantiation of `CategoryTheory.Localization.Monoidal.associator_hom_app`,
exactly as `CochainComplex.KFlatMonoidal.homotopyMu_natural_left` instantiates
`CategoryTheory.Localization.Monoidal.μ_natural_left`. The localization functor, the morphism
property and the unit isomorphism are passed explicitly rather than by `_`, for the reason
recorded in `KFlatLocalization`: left to unification they are solved against the unfolding of
`HomotopyCategory.quotient`, for which Mathlib's `IsLocalization` instance does not fire.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization

universe w v u

namespace CochainComplex.KFlatMonoidal

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

attribute [local instance] homotopyMonoidal

/-- **The associator of `K(A)` on images of complexes.** It is the associator of `Comp(A)`,
conjugated by the comparison isomorphisms of the first localization. -/
lemma homotopyMu_associator (X₁ X₂ X₃ : CochainComplex A ℤ) :
    (α_ ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X₁)
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X₂)
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X₃)).hom =
      ((homotopyMu A X₁ X₂).hom ⊗ₘ
          𝟙 ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X₃)) ≫
        (homotopyMu A (X₁ ⊗ X₂) X₃).hom ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (α_ X₁ X₂ X₃).hom ≫
        (homotopyMu A X₁ (X₂ ⊗ X₃)).inv ≫
        (𝟙 ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X₁) ⊗ₘ
          (homotopyMu A X₂ X₃).inv) :=
  Localization.Monoidal.associator_hom_app
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (Iso.refl (homotopyUnit A)) X₁ X₂ X₃

open CochainComplex.KFlatBifunctor

section Derived

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

include hres in
/-- **The associator of `D(A)` on images of K-flat objects of `K(A)`.** It is the associator of
the K-flat full monoidal subcategory of `K(A)`, conjugated by the comparison isomorphisms of the
second localization. -/
lemma derivedMu_associator
    (Y₁ Y₂ Y₃ : (kFlatObjects (curriedTensor A)).FullSubcategory) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := derivedMonoidal A hres
    (α_ ((kFlatQ (curriedTensor A)).obj Y₁) ((kFlatQ (curriedTensor A)).obj Y₂)
          ((kFlatQ (curriedTensor A)).obj Y₃)).hom =
      ((Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
              (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) Y₁ Y₂).hom ⊗ₘ
          𝟙 ((kFlatQ (curriedTensor A)).obj Y₃)) ≫
        (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
          (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) (Y₁ ⊗ Y₂) Y₃).hom ≫
        (kFlatQ (curriedTensor A)).map (α_ Y₁ Y₂ Y₃).hom ≫
        (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
          (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) Y₁ (Y₂ ⊗ Y₃)).inv ≫
        (𝟙 ((kFlatQ (curriedTensor A)).obj Y₁) ⊗ₘ
          (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
            (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) Y₂ Y₃).inv) :=
  let := kFlatQ_isLocalization (curriedTensor A) hres
  Localization.Monoidal.associator_hom_app (kFlatQ (curriedTensor A))
    (kFlatQuasiIso (curriedTensor A))
    (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) Y₁ Y₂ Y₃

end Derived

end CochainComplex.KFlatMonoidal

end
