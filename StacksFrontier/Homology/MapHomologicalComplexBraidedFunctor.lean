module

public import StacksFrontier.Algebra.Homology.KoszulSymmetric
public import StacksFrontier.Homology.MapHomologicalComplexBraided
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal

/-!
# Braided functors on cochain complexes

An additive braided monoidal functor `F : C ⥤ D` between symmetric monoidal preadditive
categories induces a braided monoidal functor on cochain complexes indexed by `ℤ`, for the Koszul
braidings on both sides.

## Main definitions

* `CategoryTheory.Functor.mapHomologicalComplexBraided`: the braided structure on
  `F.mapHomologicalComplex (ComplexShape.up ℤ)`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [MonoidalCategory D] [Preadditive C] [Preadditive D]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [SymmetricCategory C] [SymmetricCategory D]
  [HasZeroObject C] [HasZeroObject D]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ : GradedObject ℤ D), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ D, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ D, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ D, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (F : C ⥤ D) [F.Additive] [F.Braided]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) F]

/-- **An additive braided monoidal functor is braided on cochain complexes**, for the Koszul
symmetries `CochainComplex.symmetricCategory` of both sides. -/
@[instance_reducible]
def mapHomologicalComplexBraided :
    letI := CochainComplex.braidedCategory C
    letI := CochainComplex.braidedCategory D
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).Braided :=
  letI := CochainComplex.braidedCategory C
  letI := CochainComplex.braidedCategory D
  { braided := fun K L ↦ by
      apply HomologicalComplex.hom_ext
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      have hμ : ∀ (K L : CochainComplex C ℤ),
          μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L =
            (mapHomologicalComplexTensorator F K L).hom := fun _ _ ↦ rfl
      change HomologicalComplex.ιTensorObj _ _ p q n h ≫
          (μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L).f n ≫
            F.map ((CochainComplex.koszulBraiding K L).hom.f n) =
        HomologicalComplex.ιTensorObj _ _ p q n h ≫
          (CochainComplex.koszulBraiding _ _).hom.f n ≫
            (μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) L K).f n
      rw [hμ, hμ, ι_mapHomologicalComplexTensorator_hom_assoc, ← Functor.map_comp,
        CochainComplex.ιTensorObj_koszulBraiding_assoc, CochainComplex.ιTensorObj_koszulBraiding,
        Units.smul_def, Functor.map_zsmul, ← Units.smul_def, Linear.comp_units_smul,
        Linear.units_smul_comp, Functor.map_comp, assoc, ι_mapHomologicalComplexTensorator_hom]
      congr 1
      exact Functor.LaxBraided.braided_assoc (F := F) (K.X p) (L.X q) _ }

end CategoryTheory.Functor
