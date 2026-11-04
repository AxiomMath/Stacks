module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctor
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedComparison

/-!
# The comparison isomorphisms of the derived tensor product on K-flat complexes

On a pair of K-flat complexes the comparison
`CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso` between the tensor product of the monoidal
derived category and the derived tensor bifunctor is `derivedTensorIso` followed by the inverse of
`comparisonRight`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex.KFlatMonoidal

open CochainComplex.KFlatBifunctor

universe w v u

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

attribute [local instance] homotopyMonoidal homotopyBraided

section Comparison

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))]

attribute [local instance] derivedLocalizedTensorLifting derivedBifunctorLiftingKFlatQ

/-- `derivedLocalizedTensorIso` at a pair of K-flat objects: the tensorator
`Localization.Monoidal.μ` of the K-flat localization, followed by the inverse of the lifting
isomorphism of `derivedBifunctor`. -/
private theorem derivedLocalizedTensorIso_hom_app_app
    (X Y : (kFlatObjects (curriedTensor A)).FullSubcategory) :
    ((derivedLocalizedTensorIso A).hom.app ((kFlatQ (curriedTensor A)).obj X)).app
        ((kFlatQ (curriedTensor A)).obj Y) =
      (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
          (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) X Y).hom ≫
        ((derivedBifunctorComparisonIso (curriedTensor A)).inv.app
          ((ObjectProperty.ιOfLE (kFlatObjects_le_kFlatObjectsLeft A)).obj X)).app Y := by
  refine (Localization.lift₂NatTrans_app_app (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
    (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
    (derivedTensorSource A) (derivedTensorSource A) (derivedLocalizedTensor A)
    (derivedBifunctor (curriedTensor A)) (Iso.refl _).hom X Y).trans ?_
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rfl

/-- `derivedLocalizedTensorIso` followed by the two-sided K-flat comparison, on a pair of K-flat
complexes: the `Q` versus `Qh ∘ quotient` bridges, the tensorator of the K-flat localization and
the tensorator `homotopyMu` of the homotopy localization. -/
theorem derivedLocalizedTensorIso_hom_app_app_comp_comparison {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    ((derivedLocalizedTensorIso A).hom.app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L) ≫
        (comparison (curriedTensor A) K L (kFlatLeft_of_kFlat A hK) hL).hom =
      ((derivedLocalizedTensor A).map ((DerivedCategory.quotientCompQhIso A).inv.app K)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedLocalizedTensor A).obj ((DerivedCategory.Qh (C := A)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).map
          ((DerivedCategory.quotientCompQhIso A).inv.app L) ≫
        (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
          (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))
          (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ :
            (kFlatObjects (curriedTensor A)).FullSubcategory)
          (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩ :
            (kFlatObjects (curriedTensor A)).FullSubcategory)).hom ≫
        (DerivedCategory.Qh (C := A)).map (homotopyMu A K L).hom ≫
        (DerivedCategory.quotientCompQhIso A).hom.app (K ⊗ L) := by
  have n1 := NatTrans.congr_app ((derivedLocalizedTensorIso A).hom.naturality
    ((DerivedCategory.quotientCompQhIso A).inv.app K)) (DerivedCategory.Q.obj L)
  have n2 := ((derivedLocalizedTensorIso A).hom.app ((DerivedCategory.Qh (C := A)).obj
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).naturality
      ((DerivedCategory.quotientCompQhIso A).inv.app L)
  simp only [NatTrans.comp_app] at n1
  simp only [comparison, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv]
  have r' : ((derivedLocalizedTensorIso A).hom.app ((DerivedCategory.Qh (C := A)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj L) ≫
        ((derivedBifunctorComparisonIso (curriedTensor A)).hom.app
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, kFlatLeft_of_kFlat A hK⟩).app
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩ =
      (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
          (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))
          (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ :
            (kFlatObjects (curriedTensor A)).FullSubcategory)
          (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩ :
            (kFlatObjects (curriedTensor A)).FullSubcategory)).hom := by
    refine (congrArg (· ≫ _) (derivedLocalizedTensorIso_hom_app_app A
      (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ :
        (kFlatObjects (curriedTensor A)).FullSubcategory)
      (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩ :
        (kFlatObjects (curriedTensor A)).FullSubcategory))).trans
      ((Category.assoc _ _ _).trans ((congrArg _ (((derivedBifunctorComparisonIso
        (curriedTensor A)).app _).app _).inv_hom_id).trans (Category.comp_id _)))
  rw [← reassoc_of% n1, ← reassoc_of% n2, reassoc_of% r']
  rfl

end Comparison

section Monoidal

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

include hres in
/-- **On a pair of K-flat complexes, the comparison of the tensor product of the monoidal derived
category with the derived tensor bifunctor is `derivedTensorIso` followed by the inverse of the
K-flat comparison `comparisonRight`.** -/
theorem derivedMonoidalTensorIso_hom_app_app_comp_comparisonRight {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    ((derivedMonoidalTensorIso A hres).hom.app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L) ≫
        (comparisonRight (curriedTensor A) K L hL).hom =
      (derivedTensorIso A hres hK hL).hom := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  rw [comparisonRight_eq_comparison _ K L (kFlatLeft_of_kFlat A hK) hL]
  refine (Category.assoc _ _ _).trans ((Category.id_comp _).trans
    ((derivedLocalizedTensorIso_hom_app_app_comp_comparison A hK hL).trans ?_))
  simp only [derivedTensorIso, Iso.trans_hom, tensorIso_hom, MonoidalCategory.tensorHom_def,
    Iso.symm_hom, Category.assoc]
  rfl

end Monoidal

end CochainComplex.KFlatMonoidal
