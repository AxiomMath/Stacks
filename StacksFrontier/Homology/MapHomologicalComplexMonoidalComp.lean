module

public import StacksFrontier.Homology.MapHomologicalComplexMonoidal

/-!
# Monoidal composition isomorphisms on homological complexes

Let `F : C₁ ⥤ C₂`, `G : C₂ ⥤ C₃` and `H : C₁ ⥤ C₃` be additive monoidal functors preserving the
coproducts occurring in total complexes, and let `e : F ⋙ G ≅ H` be a monoidal isomorphism. Then
the induced isomorphism `F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅
H.mapHomologicalComplex c` is monoidal, for the monoidal structures
`CategoryTheory.Functor.mapHomologicalComplexMonoidal`.

## Main results

* `CategoryTheory.Functor.isMonoidal_mapHomologicalComplexCompIso_hom`
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory
open Functor.LaxMonoidal

namespace CategoryTheory.Functor

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃]
  [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject C₃]
  [(curriedTensor C₁).Additive] [∀ X₁ : C₁, ((curriedTensor C₁).obj X₁).Additive]
  [(curriedTensor C₂).Additive] [∀ X₁ : C₂, ((curriedTensor C₂).obj X₁).Additive]
  [(curriedTensor C₃).Additive] [∀ X₁ : C₃, ((curriedTensor C₃).obj X₁).Additive]
  {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]
  [∀ (X₁ X₂ : GradedObject I C₁), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : C₁, PreservesColimit (Functor.empty.{0} C₁) ((curriedTensor C₁).obj X₁)]
  [∀ X₂ : C₁, PreservesColimit (Functor.empty.{0} C₁) ((curriedTensor C₁).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject I C₁, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject I C₁, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject I C₁, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ : GradedObject I C₂), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : C₂, PreservesColimit (Functor.empty.{0} C₂) ((curriedTensor C₂).obj X₁)]
  [∀ X₂ : C₂, PreservesColimit (Functor.empty.{0} C₂) ((curriedTensor C₂).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject I C₂, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject I C₂, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject I C₂, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ : GradedObject I C₃), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : C₃, PreservesColimit (Functor.empty.{0} C₃) ((curriedTensor C₃).obj X₁)]
  [∀ X₂ : C₃, PreservesColimit (Functor.empty.{0} C₃) ((curriedTensor C₃).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject I C₃, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject I C₃, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject I C₃, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {H : C₁ ⥤ C₃} [F.Additive] [G.Additive] [H.Additive]
  [F.Monoidal] [G.Monoidal] [H.Monoidal]
  [∀ n : I, PreservesColimitsOfShape (Discrete ↥(ComplexShape.π c c c ⁻¹' {n})) F]
  [∀ n : I, PreservesColimitsOfShape (Discrete ↥(ComplexShape.π c c c ⁻¹' {n})) G]
  [∀ n : I, PreservesColimitsOfShape (Discrete ↥(ComplexShape.π c c c ⁻¹' {n})) H]

/-- The lax tensorator of `mapHomologicalComplexMonoidal` is the tensorator
`mapHomologicalComplexTensorator`. -/
lemma mapHomologicalComplex_μ (K L : HomologicalComplex C₁ c) :
    μ (F.mapHomologicalComplex c) K L = (mapHomologicalComplexTensorator F K L).hom :=
  rfl

/-- The lax unit of `mapHomologicalComplexMonoidal` is the unit comparison
`mapHomologicalComplexUnitIso`. -/
lemma mapHomologicalComplex_ε :
    ε (F.mapHomologicalComplex c) = (mapHomologicalComplexUnitIso F).hom :=
  rfl

/-- **The composition isomorphism induced on homological complexes by a monoidal isomorphism
`F ⋙ G ≅ H` is monoidal.** -/
instance isMonoidal_mapHomologicalComplexCompIso_hom (e : F ⋙ G ≅ H)
    [NatTrans.IsMonoidal e.hom] :
    NatTrans.IsMonoidal (Functor.mapHomologicalComplexCompIso e c).hom where
  unit := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    by_cases hn : n = 0
    · subst hn
      rw [← cancel_mono (H.map (HomologicalComplex.singleObjXSelf c 0 (𝟙_ C₁)).hom)]
      simp only [comp_ε, HomologicalComplex.comp_f, mapHomologicalComplex_ε,
        Functor.mapHomologicalComplex_map_f, mapHomologicalComplexCompIso_hom_app_f,
        Category.assoc]
      rw [← e.hom.naturality, mapHomologicalComplexUnitIso_hom_f_zero]
      simp only [Functor.comp_map, ← Functor.map_comp_assoc,
        mapHomologicalComplexUnitIso_hom_f_zero]
      simp only [Functor.map_comp, Category.assoc]
      have hu := NatTrans.IsMonoidal.unit (τ := e.hom)
      rw [comp_ε, Category.assoc] at hu
      rw [reassoc_of% mapHomologicalComplexUnitIso_hom_f_zero (F := G), hu]
    · exact (HomologicalComplex.isZero_single_obj_X c 0 (𝟙_ C₃) n hn).eq_of_src _ _
  tensor K L := by
    refine HomologicalComplex.hom_ext _ _ fun n => HomologicalComplex.mapBifunctor.hom_ext ?_
    intro p q h
    have h₁ := ι_mapHomologicalComplexTensorator_hom G ((F.mapHomologicalComplex c).obj K)
      ((F.mapHomologicalComplex c).obj L) p q n h
    have h₂ : G.map (HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex c).obj K)
          ((F.mapHomologicalComplex c).obj L) p q n h) ≫
          G.map ((mapHomologicalComplexTensorator F K L).hom.f n) =
        G.map (μ F (K.X p) (L.X q)) ≫ G.map (F.map
            (HomologicalComplex.ιTensorObj K L p q n h)) := by
      rw [← G.map_comp, ← G.map_comp, ι_mapHomologicalComplexTensorator_hom]
    have h₃ : G.map (F.map (HomologicalComplex.ιTensorObj K L p q n h)) ≫
        e.hom.app ((K ⊗ L).X n) =
        e.hom.app _ ≫ H.map (HomologicalComplex.ιTensorObj K L p q n h) :=
      e.hom.naturality (HomologicalComplex.ιTensorObj K L p q n h)
    have h₄ := NatTrans.IsMonoidal.tensor (τ := e.hom) (K.X p) (L.X q)
    have h₅ := ι_mapHomologicalComplexTensorator_hom H K L p q n h
    simp only [Functor.comp_obj, comp_μ, Category.assoc] at h₄
    simp only [Functor.mapHomologicalComplex_obj_X] at h₁
    simp only [comp_μ, HomologicalComplex.comp_f, mapHomologicalComplex_μ,
      Functor.mapHomologicalComplex_map_f, mapHomologicalComplexCompIso_hom_app_f,
      Category.assoc, Functor.comp_obj, tensorHom_def, Functor.mapHomologicalComplex_obj_X]
    rw [reassoc_of% h₁, reassoc_of% h₂, h₃, reassoc_of% h₄,
      HomologicalComplex.Monoidal.ι_whiskerRight_assoc,
      HomologicalComplex.Monoidal.ι_whiskerLeft_assoc, h₅]
    simp only [mapHomologicalComplexCompIso_hom_app_f, tensorHom_def, Category.assoc]
    rfl

end CategoryTheory.Functor
