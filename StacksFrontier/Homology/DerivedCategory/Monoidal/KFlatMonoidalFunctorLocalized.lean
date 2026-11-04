module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatMonoidalFunctor
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure

/-!
# Additive monoidal functors on localized homotopy categories

For an additive monoidal functor `F : A ⥤ B` between abelian monoidal categories, this file
regards the functor induced by `F` on homotopy categories of cochain complexes as a functor
between the homotopy categories endowed with their localized monoidal structures. It is used
alongside `StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatMonoidalFunctor`.

## Main definitions

* `CochainComplex.KFlatMonoidal.mapHomotopyCategoryLocalized`: The functor `F.mapHomotopyCategory`
  between the homotopy categories with their localized monoidal structures.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatBifunctor

universe w w' v₁ v₂ u₁ u₂

namespace CochainComplex.KFlatMonoidal

attribute [local instance] homotopyMonoidal

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [MonoidalCategory B]
  [(curriedTensor B).Additive] [∀ X : B, ((curriedTensor B).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ B, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X₁)]
  [∀ X₂ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ B, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (F : A ⥤ B) [F.Additive] [F.Monoidal]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) F]

/-! ### The homotopy categories -/

/-- `F.mapHomotopyCategory`, retyped between the type synonyms carrying the localized monoidal
structures of the two homotopy categories. -/
abbrev mapHomotopyCategoryLocalized : HomotopyLocalized A ⥤ HomotopyLocalized B :=
  F.mapHomotopyCategory (ComplexShape.up ℤ)

/-! ### The K-flat objects -/

variable (hF : ∀ K : CochainComplex A ℤ,
  _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K →
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))

/-! ### The derived categories -/

variable [BraidedCategory (CochainComplex A ℤ)] [BraidedCategory (CochainComplex B ℤ)]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (hresA : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)
  (hresB : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B) P ∧ QuasiIso f)
  (Φ : DerivedCategory A ⥤ DerivedCategory B)
  (e : kFlatQ (curriedTensor A) ⋙ Φ ≅ kFlatLift F hF ⋙ kFlatQ (curriedTensor B))

end CochainComplex.KFlatMonoidal

end
