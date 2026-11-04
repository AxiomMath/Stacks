module

public import Mathlib.Algebra.Homology.Additive
public import StacksFrontier.Algebra.Homology.KoszulSymmetric

/-!
# Comparisons of total tensor complexes commuting with the Koszul braiding

Let `F : C ⥤ D` be an additive functor between symmetric monoidal preadditive categories and
let `μ_{a,b} : F a ⊗ F b ⟶ F (a ⊗ b)` commute with the symmetries. A family of morphisms of
cochain complexes `τ_{K,L} : F K ⊗ F L ⟶ F (K ⊗ L)` which on the summand of bidegree `(p, q)`
is `μ` followed by `F` of the summand inclusion commutes with the Koszul braidings
(`CochainComplex.koszulBraiding`): both sides are `(-1)^{pq}` times `μ ∘ σ` on that summand.

## Main results

* `CategoryTheory.Functor.mapHomologicalComplex_koszulBraiding_of_ι`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory ComplexShape

universe v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [MonoidalCategory C]
  [MonoidalCategory D] [Preadditive C] [Preadditive D] [MonoidalPreadditive C]
  [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D]
  [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ X₁ : D, ((curriedTensor D).obj X₁).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ : GradedObject ℤ D), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- **A comparison of total tensor complexes built from a braided comparison is braided**, for
the Koszul braidings. -/
lemma mapHomologicalComplex_koszulBraiding_of_ι (F : C ⥤ D) [F.Additive]
    (μ' : ∀ a b : C, F.obj a ⊗ F.obj b ⟶ F.obj (a ⊗ b))
    (hμB : ∀ a b : C, μ' a b ≫ F.map (β_ a b).hom = (β_ (F.obj a) (F.obj b)).hom ≫ μ' b a)
    (τ : ∀ K L : CochainComplex C ℤ,
      (F.mapHomologicalComplex _).obj K ⊗ (F.mapHomologicalComplex _).obj L ⟶
        (F.mapHomologicalComplex _).obj (K ⊗ L))
    (hτ : ∀ (K L : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n),
      HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex _).obj K)
          ((F.mapHomologicalComplex _).obj L) p q n h ≫ (τ K L).f n =
        μ' (K.X p) (L.X q) ≫ F.map (HomologicalComplex.ιTensorObj K L p q n h))
    (K L : CochainComplex C ℤ) :
    τ K L ≫ (F.mapHomologicalComplex _).map (CochainComplex.koszulBraiding K L).hom =
      (CochainComplex.koszulBraiding ((F.mapHomologicalComplex _).obj K)
          ((F.mapHomologicalComplex _).obj L)).hom ≫ τ L K := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have h' : p + q = n := h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change HomologicalComplex.ιTensorObj _ _ p q n h' ≫ _ =
    HomologicalComplex.ιTensorObj _ _ p q n h' ≫ _
  rw [reassoc_of% hτ, ← F.map_comp, CochainComplex.ιTensorObj_koszulBraiding,
    CochainComplex.ιTensorObj_koszulBraiding_assoc, F.map_units_smul, Linear.comp_units_smul,
    Linear.units_smul_comp, F.map_comp, reassoc_of% hμB, Category.assoc, hτ]
  rfl

end CategoryTheory.Functor
