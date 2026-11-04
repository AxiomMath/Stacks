module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.DerivedTensorIsoNaturality

/-!
# Naturality of the derived tensor product of K-flat complexes in both variables

`CochainComplex.KFlatMonoidal.derivedTensorIso` identifies the derived tensor product of two
K-flat complexes with the image of their total tensor product.  Its naturality in the first
variable is `CochainComplex.KFlatMonoidal.derivedTensorIso_hom_natural_left`; this file records
the naturality in both variables at once.

## Main results

* `CochainComplex.KFlatMonoidal.derivedTensorIso_hom_natural`: the identification is natural in
  both K-flat complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

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
  [SymmetricCategory (CochainComplex A ℤ)] [HasDerivedCategory.{w} A]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)

/-- **The identification of the derived tensor product of two K-flat complexes with their total
tensor product is natural in both complexes.**  It is the tensorator of the restriction of
`DerivedCategory.Q` to the K-flat complexes (`CochainComplex.KFlatMonoidal.mu_kFlatQRestriction`),
which is natural in both variables. -/
theorem derivedTensorIso_hom_natural {K₁ K₂ L₁ L₂ : CochainComplex A ℤ}
    (f : K₁ ⟶ K₂) (g : L₁ ⟶ L₂)
    (hK₁ : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K₁)
    (hK₂ : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K₂)
    (hL₁ : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L₁)
    (hL₂ : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L₂) :
    letI := derivedMonoidal A hres
    (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫
        (derivedTensorIso A hres hK₂ hL₂).hom =
      (derivedTensorIso A hres hK₁ hL₁).hom ≫ DerivedCategory.Q.map (f ⊗ₘ g) := by
  let := derivedMonoidal A hres
  let := kFlatQRestrictionMonoidal A hres
  rw [← mu_kFlatQRestriction A hres hK₂ hL₂, ← mu_kFlatQRestriction A hres hK₁ hL₁]
  exact Functor.LaxMonoidal.μ_natural (kFlatQRestriction A)
    (ObjectProperty.homMk f :
      (⟨K₁, hK₁⟩ : (_root_.CochainComplex.KFlatBifunctor.kFlatComplexes
        (curriedTensor A)).FullSubcategory) ⟶ ⟨K₂, hK₂⟩)
    (ObjectProperty.homMk g :
      (⟨L₁, hL₁⟩ : (_root_.CochainComplex.KFlatBifunctor.kFlatComplexes
        (curriedTensor A)).FullSubcategory) ⟶ ⟨L₂, hL₂⟩)


end CochainComplex.KFlatMonoidal

end
