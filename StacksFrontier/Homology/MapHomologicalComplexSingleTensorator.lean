module

public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
public import StacksFrontier.Homology.MapHomologicalComplexMonoidalTensorator
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensorDegreeZero

/-!
# The tensorator of a degreewise monoidal functor at two complexes in degree zero

Let `F : C ⥤ D` be additive and monoidal between monoidal preadditive categories whose tensor
products commute with the coproducts occurring in a total complex, so that
`F.mapHomologicalComplex (ComplexShape.up ℤ)` is monoidal
(`CategoryTheory.Functor.mapHomologicalComplexMonoidal`).  At a pair of objects placed in degree
zero both the source and the target of its tensorator are concentrated in degree zero
(`HomologicalComplex.mapBifunctorSingleIso`), and there the tensorator is `μ F` itself.

## Main results

* `CategoryTheory.Functor.mu_mapHomologicalComplex_single`: **the tensorator of
  `F.mapHomologicalComplex (ComplexShape.up ℤ)` at two objects placed in degree zero is `μ F`**,
  read through `HomologicalComplex.mapBifunctorSingleIso` on each side and through
  `CategoryTheory.Functor.mapHomologicalComplexSingleIso`.

## Implementation notes

The proof is extensionality on the summands of the source, which is a total complex and
therefore a coproduct on the nose.  Every summand off `(0, 0)` vanishes
(`HomologicalComplex.isZero_obj_obj_single_obj_X`), and on the `(0, 0)` summand the four
identifications involved are computed by `CategoryTheory.Functor.ι_mu_mapHomologicalComplex`,
`HomologicalComplex.ι_mapBifunctorSingleIso_hom` and
`CategoryTheory.Functor.mapHomologicalComplexSingleIso_inv_f_self`, after which what is left is
the naturality of `μ F` in both variables.

This is where the two `CategoryTheory.MonoidalCategoryStruct` instances on `HomologicalComplex`
have to be identified, which is possible only in a module where both are section variables; see
`CategoryTheory.Functor.mu_mapHomologicalComplex`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [MonoidalCategory D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ X₁ : D, ((curriedTensor D).obj X₁).Additive]
  (F : C ⥤ D) [F.Additive] [F.Monoidal]
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
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) F]

/-- The tensor product of two morphisms of complexes on the summands of its source. -/
@[reassoc]
lemma ι_tensorHom_f {K₁ L₁ K₂ L₂ : HomologicalComplex C (ComplexShape.up ℤ)}
    (φ : K₁ ⟶ L₁) (ψ : K₂ ⟶ L₂) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ p q n h ≫ (φ ⊗ₘ ψ).f n =
      (φ.f p ⊗ₘ ψ.f q) ≫ HomologicalComplex.ιTensorObj L₁ L₂ p q n h := by
  rw [MonoidalCategory.tensorHom_def, HomologicalComplex.comp_f,
    HomologicalComplex.Monoidal.ι_whiskerRight_assoc,
    HomologicalComplex.Monoidal.ι_whiskerLeft, ← Category.assoc,
    ← MonoidalCategory.tensorHom_def]

/-- **The tensorator of `F.mapHomologicalComplex (ComplexShape.up ℤ)` at two objects placed in
degree zero is `μ F`.**  Both sides of the tensorator are concentrated in degree zero, and read
through the identifications `HomologicalComplex.mapBifunctorSingleIso` of those total complexes
with their degree-zero terms and through
`CategoryTheory.Functor.mapHomologicalComplexSingleIso`, the tensorator is the comparison
`μ F X Y` placed in degree zero. -/
lemma mu_mapHomologicalComplex_single (X Y : C) :
    ((mapHomologicalComplexSingleIso F 0 X).inv ⊗ₘ
          (mapHomologicalComplexSingleIso F 0 Y).inv) ≫
        Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ))
            ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X)
            ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Y) ≫
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (HomologicalComplex.mapBifunctorSingleIso (curriedTensor C) X Y).hom =
      (HomologicalComplex.mapBifunctorSingleIso (curriedTensor D) (F.obj X) (F.obj Y)).hom ≫
        (CochainComplex.singleFunctor D 0).map (Functor.LaxMonoidal.μ F X Y) ≫
          (mapHomologicalComplexSingleIso F 0 (X ⊗ Y)).inv := by
  ext n
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  by_cases h : p = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h
    obtain rfl : n = 0 := hpq.symm.trans (add_zero 0)
    have hC : HomologicalComplex.ιTensorObj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X)
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Y) 0 0 0 hpq ≫
          (HomologicalComplex.mapBifunctorSingleIso (curriedTensor C) X Y).hom.f 0 = _ :=
      HomologicalComplex.ι_mapBifunctorSingleIso_hom (curriedTensor C) X Y
    have hD : HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (F.obj X))
          ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (F.obj Y))
          (curriedTensor D) (ComplexShape.up ℤ) 0 0 0 hpq ≫
        (HomologicalComplex.mapBifunctorSingleIso (curriedTensor D)
          (F.obj X) (F.obj Y)).hom.f 0 = _ :=
      HomologicalComplex.ι_mapBifunctorSingleIso_hom (curriedTensor D) (F.obj X) (F.obj Y)
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ι_tensorHom_f_assoc,
      Functor.ι_mu_mapHomologicalComplex_assoc, HomologicalComplex.comp_f,
      HomologicalComplex.comp_f, reassoc_of% hD,
      Functor.mapHomologicalComplex_map_f, ← F.map_comp, hC]
    simp only [curriedTensor_map_app, curriedTensor_obj_map,
      ← MonoidalCategory.tensorHom_def]
    have hsm : ((CochainComplex.singleFunctor D 0).map
          (Functor.LaxMonoidal.μ F X Y)).f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (F.obj X ⊗ F.obj Y)).hom ≫
          Functor.LaxMonoidal.μ F X Y ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (F.obj (X ⊗ Y))).inv :=
      HomologicalComplex.single_map_f_self _ _ _
    simp only [hsm, HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      Functor.mapHomologicalComplexSingleIso_inv_f_self, eqToHom_map, eqToIso.hom,
      eqToIso.inv, Category.assoc, eqToHom_trans]
    change (𝟙 (F.obj X) ⊗ₘ 𝟙 (F.obj Y)) ≫
        Functor.LaxMonoidal.μ F X Y ≫ F.map (𝟙 X ⊗ₘ 𝟙 Y) =
      (𝟙 (F.obj X) ⊗ₘ 𝟙 (F.obj Y)) ≫ 𝟙 (F.obj X ⊗ F.obj Y) ≫
        Functor.LaxMonoidal.μ F X Y ≫ 𝟙 (F.obj (X ⊗ Y))
    rw [MonoidalCategory.id_tensorHom_id, MonoidalCategory.id_tensorHom_id, Functor.map_id,
      Category.comp_id, Category.id_comp, Category.id_comp]
  · exact (HomologicalComplex.isZero_obj_obj_single_obj_X (curriedTensor D) (F.obj X) (F.obj Y)
      p q (not_and_or.1 h)).eq_of_src _ _

end CategoryTheory.Functor

end
