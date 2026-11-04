module

public import StacksFrontier.Homology.MapHomologicalComplexMonoidal

/-!
# Associativity of a comparison of total tensor complexes, read on summands

Let `μ_{a,b} : F a ⊗ F b ⟶ F (a ⊗ b)` be natural and compatible with the associators, and let
`τ_{K,L} : F K ⊗ F L ⟶ F (K ⊗ L)` be a family of morphisms of complexes which on the summand of
bidegree `(p, q)` is `μ` followed by `F` of the summand inclusion.  Then `τ` is compatible with the
associators of complexes.  No monoidal structure on `F` is needed.

## Main results

* `CategoryTheory.Functor.mapHomologicalComplex_associativity_of_ι`
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v v' u u'

namespace CategoryTheory.Functor

/-- **A comparison of total tensor complexes built from an associative comparison is
associative.** Let `μ_{a,b} : F a ⊗ F b ⟶ F (a ⊗ b)` be natural and compatible with the
associators, and let `τ_{K,L} : F K ⊗ F L ⟶ F (K ⊗ L)` be a family of morphisms of complexes
which on the summand of bidegree `(p, q)` is `μ` followed by `F` of the summand inclusion. Then
`τ` is compatible with the associators of complexes. No monoidal structure on `F` is needed. -/
public lemma mapHomologicalComplex_associativity_of_ι {C : Type u} {D : Type u'}
    {_ : Category.{v} C} {_ : Category.{v'} D} {_ : MonoidalCategory C} {_ : MonoidalCategory D}
    {_ : Preadditive C} {_ : Preadditive D} [HasZeroObject C] [HasZeroObject D]
    [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
    [(curriedTensor D).Additive] [∀ X₁ : D, ((curriedTensor D).obj X₁).Additive]
    {I : Type*} {_ : AddMonoid I} {_ : DecidableEq I} {c : ComplexShape I} {_ : c.TensorSigns}
    [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
    [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ X₁ X₂ X₃ : GradedObject I C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ X₁ X₂ X₃ : GradedObject I C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ : GradedObject I D), GradedObject.HasTensor X₁ X₂]
    [∀ X₁ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
    [∀ X₂ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
    [∀ X₁ X₂ X₃ : GradedObject I D, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ X₁ X₂ X₃ : GradedObject I D, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (F : C ⥤ D) [F.Additive]
    (μ' : ∀ a b : C, F.obj a ⊗ F.obj b ⟶ F.obj (a ⊗ b))
    (hμL : ∀ {a a' : C} (g : a ⟶ a') (b : C),
      F.map g ▷ F.obj b ≫ μ' a' b = μ' a b ≫ F.map (g ▷ b))
    (hμR : ∀ (a : C) {b b' : C} (g : b ⟶ b'),
      F.obj a ◁ F.map g ≫ μ' a b' = μ' a b ≫ F.map (a ◁ g))
    (hμA : ∀ a b d : C, μ' a b ▷ F.obj d ≫ μ' (a ⊗ b) d ≫ F.map (α_ a b d).hom =
      (α_ (F.obj a) (F.obj b) (F.obj d)).hom ≫ F.obj a ◁ μ' b d ≫ μ' a (b ⊗ d))
    (τ : ∀ K L : HomologicalComplex C c,
      (F.mapHomologicalComplex c).obj K ⊗ (F.mapHomologicalComplex c).obj L ⟶
        (F.mapHomologicalComplex c).obj (K ⊗ L))
    (hτ : ∀ (K L : HomologicalComplex C c) (p q n : I) (h : p + q = n),
      HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex c).obj K)
          ((F.mapHomologicalComplex c).obj L) p q n h ≫ (τ K L).f n =
        μ' (K.X p) (L.X q) ≫ F.map (HomologicalComplex.ιTensorObj K L p q n h))
    (K₁ K₂ K₃ : HomologicalComplex C c) :
    τ K₁ K₂ ▷ (F.mapHomologicalComplex c).obj K₃ ≫ τ (K₁ ⊗ K₂) K₃ ≫
          (F.mapHomologicalComplex c).map (α_ K₁ K₂ K₃).hom =
      (α_ ((F.mapHomologicalComplex c).obj K₁) ((F.mapHomologicalComplex c).obj K₂)
            ((F.mapHomologicalComplex c).obj K₃)).hom ≫
        (F.mapHomologicalComplex c).obj K₁ ◁ τ K₂ K₃ ≫ τ K₁ (K₂ ⊗ K₃) := by
  have hτ' : ∀ (K L : HomologicalComplex C c) (p q n : I) (h : p + q = n) {Z : D}
      (z : F.obj ((K ⊗ L).X n) ⟶ Z),
      HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex c).obj K)
          ((F.mapHomologicalComplex c).obj L) p q n h ≫ (τ K L).f n ≫ z =
        μ' (K.X p) (L.X q) ≫ F.map (HomologicalComplex.ιTensorObj K L p q n h) ≫ z :=
    fun K L p q n h _ z => by rw [← Category.assoc, hτ, Category.assoc]
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro i₁ i₂ i₃ h
  have hL : ComplexShape.π c c c (i₁ + i₂, i₃) = n := h
  have hR : ComplexShape.π c c c (i₁, i₂ + i₃) = n := by
    dsimp only [ComplexShape.π] at hL ⊢; rw [← hL]; exact (add_assoc i₁ i₂ i₃).symm
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.Monoidal.ι₁₂_associator_hom_assoc,
    HomologicalComplex.mapBifunctor₂₃.ι_eq (curriedTensor D) (curriedTensor D)
      ((F.mapHomologicalComplex c).obj K₁) ((F.mapHomologicalComplex c).obj K₂)
      ((F.mapHomologicalComplex c).obj K₃) c c c i₁ i₂ i₃ (i₂ + i₃) n rfl hR,
    HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor D) (curriedTensor D)
      ((F.mapHomologicalComplex c).obj K₁) ((F.mapHomologicalComplex c).obj K₂)
      ((F.mapHomologicalComplex c).obj K₃) c c i₁ i₂ i₃ (i₁ + i₂) n rfl hL]
  simp only [Category.assoc]
  rw [HomologicalComplex.Monoidal.ι_whiskerRight_assoc, hτ',
    HomologicalComplex.Monoidal.ι_whiskerLeft_assoc, hτ]
  simp only [curriedTensor_map_app, curriedTensor_obj_map,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, hτ,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hτ]
  have hassoc : (HomologicalComplex.ιTensorObj K₁ K₂ i₁ i₂ (i₁ + i₂) rfl ▷ K₃.X i₃) ≫
      HomologicalComplex.ιTensorObj (K₁ ⊗ K₂) K₃ (i₁ + i₂) i₃ n hL ≫ (α_ K₁ K₂ K₃).hom.f n =
      (α_ (K₁.X i₁) (K₂.X i₂) (K₃.X i₃)).hom ≫
        (K₁.X i₁ ◁ HomologicalComplex.ιTensorObj K₂ K₃ i₂ i₃ (i₂ + i₃) rfl) ≫
          HomologicalComplex.ιTensorObj K₁ (K₂ ⊗ K₃) i₁ (i₂ + i₃) n hR :=
    HomologicalComplex.Monoidal.ι_associator_hom K₁ K₂ K₃ i₁ i₂ i₃ n hL hR
  have hmapL : F.map (HomologicalComplex.ιTensorObj K₁ K₂ i₁ i₂ (i₁ + i₂) rfl ▷ K₃.X i₃) ≫
      F.map (HomologicalComplex.ιTensorObj (K₁ ⊗ K₂) K₃ (i₁ + i₂) i₃ n hL) ≫
        F.map ((α_ K₁ K₂ K₃).hom.f n) =
      F.map (α_ (K₁.X i₁) (K₂.X i₂) (K₃.X i₃)).hom ≫
        F.map (K₁.X i₁ ◁ HomologicalComplex.ιTensorObj K₂ K₃ i₂ i₃ (i₂ + i₃) rfl) ≫
          F.map (HomologicalComplex.ιTensorObj K₁ (K₂ ⊗ K₃) i₁ (i₂ + i₃) n hR) := by
    simp only [← Functor.map_comp]
    exact congrArg F.map hassoc
  have hL' : F.map (HomologicalComplex.ιTensorObj K₁ K₂ i₁ i₂ (i₁ + i₂) rfl) ▷
        F.obj (K₃.X i₃) ≫ μ' ((K₁ ⊗ K₂).X (i₁ + i₂)) (K₃.X i₃) =
      μ' (K₁.X i₁ ⊗ K₂.X i₂) (K₃.X i₃) ≫
        F.map (HomologicalComplex.ιTensorObj K₁ K₂ i₁ i₂ (i₁ + i₂) rfl ▷ K₃.X i₃) :=
    hμL _ _
  have hR' : F.obj (K₁.X i₁) ◁
        F.map (HomologicalComplex.ιTensorObj K₂ K₃ i₂ i₃ (i₂ + i₃) rfl) ≫
          μ' (K₁.X i₁) ((K₂ ⊗ K₃).X (i₂ + i₃)) =
      μ' (K₁.X i₁) (K₂.X i₂ ⊗ K₃.X i₃) ≫
        F.map (K₁.X i₁ ◁ HomologicalComplex.ιTensorObj K₂ K₃ i₂ i₃ (i₂ + i₃) rfl) :=
    hμR _ _
  rw [MonoidalCategory.comp_whiskerRight_assoc, reassoc_of% hL', hmapL,
    MonoidalCategory.whiskerLeft_comp_assoc, reassoc_of% hR',
    reassoc_of% (hμA (K₁.X i₁) (K₂.X i₂) (K₃.X i₃))]

end CategoryTheory.Functor

end
