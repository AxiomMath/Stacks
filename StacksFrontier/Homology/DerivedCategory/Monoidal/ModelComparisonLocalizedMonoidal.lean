module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.ModelComparisonMonoidal
import all StacksFrontier.Homology.DerivedCategory.Monoidal.ModelComparisonMonoidal
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatMonoidalFunctor

/-!
# The model comparison as a localized monoidal functor

Declarations built on
`StacksFrontier.Homology.DerivedCategory.Monoidal.ModelComparisonMonoidal`.

## Main results

* `modelComparisonLocalized`
* `modelComparisonLifting`
* `modelComparisonMonoidal`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatBifunctor

universe w₁ w₂ v u

namespace CochainComplex.KFlatMonoidal

attribute [local instance] homotopyMonoidal

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory (CochainComplex A ℤ)]
  (h₁ : HasDerivedCategory.{w₁} A) (h₂ : HasDerivedCategory.{w₂} A)
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)
  (Φ : @DerivedCategory A _ _ h₁ ⥤ @DerivedCategory A _ _ h₂)
  (e : @DerivedCategory.Qh A _ _ h₁ ⋙ Φ ≅ @DerivedCategory.Qh A _ _ h₂)

/-- `Φ`, retyped between the type synonyms carrying the localized monoidal structures of the two
models. -/
abbrev modelComparisonLocalized :
    @DerivedLocalized A _ _ _ _ _ _ _ _ _ _ _ h₁ _ hres ⥤
      @DerivedLocalized A _ _ _ _ _ _ _ _ _ _ _ h₂ _ hres := Φ

/-- The lifting of `Φ` along the K-flat localization of the first model, to the K-flat
localization of the second. -/
@[instance_reducible]
def modelComparisonLifting :
    letI := @kFlatQ_isLocalization A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₁ hres
    letI := @kFlatQ_isLocalization A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₂ hres
    Localization.Lifting
      (Localization.Monoidal.toMonoidalCategory
        (@kFlatQ A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₁)
        (kFlatQuasiIso (curriedTensor A))
        (Iso.refl ((@kFlatQ A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₁).obj (𝟙_ _))))
      (kFlatQuasiIso (curriedTensor A))
      (Localization.Monoidal.toMonoidalCategory
        (@kFlatQ A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₂)
        (kFlatQuasiIso (curriedTensor A))
        (Iso.refl ((@kFlatQ A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₂).obj (𝟙_ _))))
      (modelComparisonLocalized h₁ h₂ hres Φ) :=
  ⟨Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e⟩

/-- **A comparison of two models of `D(A)` is monoidal**, for
`CochainComplex.KFlatMonoidal.derivedMonoidal` at both models. -/
@[instance_reducible]
def modelComparisonMonoidal :
    letI := @derivedMonoidal A _ _ _ _ _ _ _ _ _ _ _ h₁ _ hres
    letI := @derivedMonoidal A _ _ _ _ _ _ _ _ _ _ _ h₂ _ hres
    Φ.Monoidal :=
  letI := @kFlatQ_isLocalization A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₁ hres
  letI := @kFlatQ_isLocalization A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₂ hres
  letI := modelComparisonLifting h₁ h₂ hres Φ e
  (Localization.Monoidal.functorMonoidalOfComp
    (Localization.Monoidal.toMonoidalCategory
      (@kFlatQ A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₁)
      (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((@kFlatQ A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₁).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor A))
    (modelComparisonLocalized h₁ h₂ hres Φ)
    (Localization.Monoidal.toMonoidalCategory
      (@kFlatQ A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₂)
      (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((@kFlatQ A A A _ _ _ _ _ _ (curriedTensor A) _ _ _ h₂).obj (𝟙_ _)))) :
    (modelComparisonLocalized h₁ h₂ hres Φ).Monoidal)

end CochainComplex.KFlatMonoidal

end
