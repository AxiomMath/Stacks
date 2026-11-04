module

public import StacksFrontier.Homology.ConstMapDerivedCategoryMonoidal

/-!
# The tensorator of constant diagrams on homotopy and derived categories

`CategoryTheory.Functor.constMapHomotopyCategoryMonoidal` and
`CategoryTheory.Functor.constMapDerivedCategoryMonoidal` make constant diagrams a monoidal functor
on homotopy categories and on derived categories.  Each is one application of
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`, whose tensorator Mathlib computes at
the image of the localization functor
(`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_μ`) in terms of the tensorator of the
lifted functor and the lifting isomorphism.  This file records those two computations with the
lifting isomorphism named, and the corresponding unit constraints.

## Main results

* `CategoryTheory.Functor.mu_constKFlatLift_hom`: the tensorator of
  `CategoryTheory.Functor.constKFlatLift` is that of `(Functor.const J).mapHomotopyCategory`.
* `CategoryTheory.Functor.mu_constMapHomotopyCategory`: **the tensorator of
  `(Functor.const J).mapHomotopyCategory` at the images of two complexes**, in terms of the
  comparison of the homotopy localization and the complex-level tensorator of
  `CategoryTheory.Functor.constMapHomologicalComplexMonoidal`.
* `CategoryTheory.Functor.mu_constMapDerivedCategory`: **the tensorator of
  `CategoryTheory.Functor.constMapDerivedCategoryMonoidal` at the images of two K-flat objects of
  the homotopy category**, in terms of the comparison of the K-flat localization and the
  tensorator of `CategoryTheory.Functor.constKFlatLiftMonoidal`.
* `CategoryTheory.Functor.epsilon_constMapHomotopyCategory` and
  `CategoryTheory.Functor.epsilon_constMapDerivedCategory`: the unit constraints of the same two
  monoidal structures.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

universe w w' v₁ u₁ v₂ u₂

namespace CategoryTheory

attribute [local instance] homotopyMonoidal homotopyBraided

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCoproducts.{0} D] [HasColimitsOfSize.{0, 0} D] [HasInitial D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]

omit [HasColimitsOfSize.{0, 0} D] in
/-- **The tensorator of `CategoryTheory.Functor.constKFlatLift` is the tensorator of
`(Functor.const J).mapHomotopyCategory`.** -/
lemma Functor.mu_constKFlatLift_hom
    (X Y : (kFlatObjects (curriedTensor D)).FullSubcategory) :
    letI := Functor.constKFlatLiftMonoidal (J := J) (D := D)
    letI := Functor.constMapHomotopyCategoryMonoidal (J := J) (D := D)
    (Functor.LaxMonoidal.μ (Functor.constKFlatLift (J := J) (D := D)) X Y).hom =
      Functor.LaxMonoidal.μ
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ))
        X.obj Y.obj := by
  let := Functor.constKFlatLiftMonoidal (J := J) (D := D)
  let := Functor.constMapHomotopyCategoryMonoidal (J := J) (D := D)
  have h1 : (Functor.LaxMonoidal.μ (Functor.constKFlatLift (J := J) (D := D)) X Y).hom =
      Functor.LaxMonoidal.μ ((kFlatObjects (curriedTensor D)).ι ⋙
        (Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)) X Y := rfl
  rw [h1, Functor.LaxMonoidal.comp_μ, ObjectProperty.ι_μ, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

/-! ### The tensorator of constant diagrams on the homotopy categories -/

omit [HasColimitsOfSize.{0, 0} D] in
/-- **The tensorator of `(Functor.const J).mapHomotopyCategory` at the images of two complexes.**
Read through the canonical factorization `CategoryTheory.Functor.mapHomotopyCategoryFactors` of
the degreewise action over the homotopy localization, it is the comparison
`CochainComplex.KFlatMonoidal.homotopyMu` of the homotopy localization of `J ⥤ D`, followed by
the image of the complex-level tensorator of
`CategoryTheory.Functor.constMapHomologicalComplexMonoidal`, followed by the inverse of the
comparison for `D`. -/
lemma Functor.mu_constMapHomotopyCategory (K L : CochainComplex D ℤ) :
    letI := Functor.constMapHomotopyCategoryMonoidal (J := J) (D := D)
    Functor.LaxMonoidal.μ
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ))
        ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K)
        ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L) =
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app K ⊗ₘ
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).hom.app L) ≫
        (homotopyMu (J ⥤ D)
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj L)).hom ≫
          (HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ)).map
              (Functor.LaxMonoidal.μ
                ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
                K L) ≫
            ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
                (ComplexShape.up ℤ)).inv.app (K ⊗ L) ≫
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)).map
                (homotopyMu D K L).inv := by
  let := Functor.constMapHomologicalComplexMonoidal (J := J) (D := D)
    (c := ComplexShape.up ℤ)
  let := Functor.constMapHomotopyCategoryLifting (J := J) (D := D)
  have h := Localization.Monoidal.functorMonoidalOfComp_μ
    (Localization.Monoidal.toMonoidalCategory (HomotopyCategory.quotient D (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences D (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit D)))
    (HomologicalComplex.homotopyEquivalences D (ComplexShape.up ℤ))
    (Functor.constMapHomotopyCategoryLocalized (J := J) (D := D))
    ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      Localization.Monoidal.toMonoidalCategory
        (HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences (J ⥤ D) (ComplexShape.up ℤ))
        (Iso.refl (homotopyUnit (J ⥤ D)))) K L
  refine h.trans ?_
  rw [Functor.LaxMonoidal.comp_μ, Category.assoc]
  exact rfl

omit [HasColimitsOfSize.{0, 0} D] in
/-- **The unit constraint of `(Functor.const J).mapHomotopyCategory`.**  It is the unit
constraint of the degreewise action followed by the homotopy localization of `J ⥤ D`, followed
by the inverse of `CategoryTheory.Functor.mapHomotopyCategoryFactors` at the unit and the image
of the oplax unit constraint of the homotopy localization of `D`. -/
lemma Functor.epsilon_constMapHomotopyCategory :
    letI := Functor.constMapHomologicalComplexMonoidal (J := J) (D := D)
      (c := ComplexShape.up ℤ)
    letI := Functor.constMapHomotopyCategoryMonoidal (J := J) (D := D)
    Functor.LaxMonoidal.ε
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)) =
      Functor.LaxMonoidal.ε
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            Localization.Monoidal.toMonoidalCategory
              (HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ))
              (HomologicalComplex.homotopyEquivalences (J ⥤ D) (ComplexShape.up ℤ))
              (Iso.refl (homotopyUnit (J ⥤ D)))) ≫
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app (𝟙_ (CochainComplex D ℤ)) ≫
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)).map
            (Functor.OplaxMonoidal.η
              (Localization.Monoidal.toMonoidalCategory
                (HomotopyCategory.quotient D (ComplexShape.up ℤ))
                (HomologicalComplex.homotopyEquivalences D (ComplexShape.up ℤ))
                (Iso.refl (homotopyUnit D)))) := by
  let := Functor.constMapHomologicalComplexMonoidal (J := J) (D := D)
    (c := ComplexShape.up ℤ)
  let := Functor.constMapHomotopyCategoryLifting (J := J) (D := D)
  exact Localization.Monoidal.functorMonoidalOfComp_ε
    (Localization.Monoidal.toMonoidalCategory (HomotopyCategory.quotient D (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences D (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit D)))
    (HomologicalComplex.homotopyEquivalences D (ComplexShape.up ℤ))
    (Functor.constMapHomotopyCategoryLocalized (J := J) (D := D))
    ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      Localization.Monoidal.toMonoidalCategory
        (HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences (J ⥤ D) (ComplexShape.up ℤ))
        (Iso.refl (homotopyUnit (J ⥤ D))))

section Derived

variable [BraidedCategory (CochainComplex D ℤ)] [BraidedCategory (CochainComplex (J ⥤ D) ℤ)]
  [HasDerivedCategory.{w} D] [HasDerivedCategory.{w'} (J ⥤ D)]
  (hresD : ∀ G : CochainComplex D ℤ, ∃ (P : CochainComplex D ℤ) (f : P ⟶ G),
    KFlat (curriedTensor D) P ∧ QuasiIso f)
  (hresJD : ∀ G : CochainComplex (J ⥤ D) ℤ, ∃ (P : CochainComplex (J ⥤ D) ℤ) (f : P ⟶ G),
    KFlat (curriedTensor (J ⥤ D)) P ∧ QuasiIso f)

omit [HasColimitsOfSize.{0, 0} D] in
/-- The tensorator of `CategoryTheory.Functor.constKFlatLift` followed by the K-flat
localization, as the localization's own comparison followed by the image of the tensorator,
with `CategoryTheory.Functor.OplaxMonoidal.δ` of the localization functor of `D` replaced by the
inverse of its lax tensorator. -/
private lemma mu_constKFlatLift_comp_kFlatQ_grouped
    (h₁ : ∀ G : CochainComplex D ℤ, ∃ (P : CochainComplex D ℤ) (f : P ⟶ G),
      KFlat (curriedTensor D) P ∧ QuasiIso f)
    (h₂ : ∀ G : CochainComplex (J ⥤ D) ℤ, ∃ (P : CochainComplex (J ⥤ D) ℤ) (f : P ⟶ G),
      KFlat (curriedTensor (J ⥤ D)) P ∧ QuasiIso f)
    (X Y : (kFlatObjects (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D h₁
    letI := derivedMonoidal (J ⥤ D) h₂
    letI := kFlatQ_isLocalization (curriedTensor D) h₁
    letI := kFlatQ_isLocalization (curriedTensor (J ⥤ D)) h₂
    letI := Functor.constKFlatLiftMonoidal (J := J) (D := D)
    ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app X.obj ⊗ₘ
        (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app Y.obj) ≫
      Functor.LaxMonoidal.μ
          (Functor.constKFlatLift (J := J) (D := D) ⋙
            Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor (J ⥤ D)))
              (kFlatQuasiIso (curriedTensor (J ⥤ D)))
              (Iso.refl ((kFlatQ (curriedTensor (J ⥤ D))).obj (𝟙_ _)))) X Y ≫
        (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.inv.app (X.obj ⊗ Y.obj) ≫
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
            (Functor.OplaxMonoidal.δ
              (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor D))
                (kFlatQuasiIso (curriedTensor D))
                (Iso.refl ((kFlatQ (curriedTensor D)).obj (𝟙_ _)))) X Y) =
    ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app X.obj ⊗ₘ
        (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app Y.obj) ≫
      ((Localization.Monoidal.μ (kFlatQ (curriedTensor (J ⥤ D)))
            (kFlatQuasiIso (curriedTensor (J ⥤ D)))
            (Iso.refl ((kFlatQ (curriedTensor (J ⥤ D))).obj (𝟙_ _)))
            (Functor.constKFlatLift.obj X) (Functor.constKFlatLift.obj Y)).hom ≫
          (kFlatQ (curriedTensor (J ⥤ D))).map
            (Functor.LaxMonoidal.μ (Functor.constKFlatLift (J := J) (D := D)) X Y)) ≫
        (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.inv.app (X.obj ⊗ Y.obj) ≫
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
            (Localization.Monoidal.μ (kFlatQ (curriedTensor D))
              (kFlatQuasiIso (curriedTensor D))
              (Iso.refl ((kFlatQ (curriedTensor D)).obj (𝟙_ _))) X Y).inv := rfl

omit [HasColimitsOfSize.{0, 0} D] in
/-- **The tensorator of `(Functor.const J).mapDerivedCategory` at the images of two K-flat
objects of the homotopy category.**  Read through the canonical factorization
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the degreewise action over the K-flat
localization, it is the comparison `CategoryTheory.Localization.Monoidal.μ` of the K-flat
localization of `J ⥤ D`, followed by the image of the tensorator of
`CategoryTheory.Functor.constKFlatLiftMonoidal`, followed by the inverse of the comparison for
`D`. -/
lemma Functor.mu_constMapDerivedCategory
    (X Y : (kFlatObjects (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := kFlatQ_isLocalization (curriedTensor D) hresD
    letI := kFlatQ_isLocalization (curriedTensor (J ⥤ D)) hresJD
    letI := Functor.constKFlatLiftMonoidal (J := J) (D := D)
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    Functor.LaxMonoidal.μ ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
        ((kFlatQ (curriedTensor D)).obj X) ((kFlatQ (curriedTensor D)).obj Y) =
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app X.obj ⊗ₘ
          (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app Y.obj) ≫
        ((Localization.Monoidal.μ (kFlatQ (curriedTensor (J ⥤ D)))
              (kFlatQuasiIso (curriedTensor (J ⥤ D)))
              (Iso.refl ((kFlatQ (curriedTensor (J ⥤ D))).obj (𝟙_ _)))
              (Functor.constKFlatLift.obj X) (Functor.constKFlatLift.obj Y)).hom ≫
            (kFlatQ (curriedTensor (J ⥤ D))).map
              (Functor.LaxMonoidal.μ (Functor.constKFlatLift (J := J) (D := D)) X Y)) ≫
          (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.inv.app (X.obj ⊗ Y.obj) ≫
            ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
              (Localization.Monoidal.μ (kFlatQ (curriedTensor D))
                (kFlatQuasiIso (curriedTensor D))
                (Iso.refl ((kFlatQ (curriedTensor D)).obj (𝟙_ _))) X Y).inv := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := kFlatQ_isLocalization (curriedTensor D) hresD
  let := kFlatQ_isLocalization (curriedTensor (J ⥤ D)) hresJD
  let := Functor.constKFlatLiftMonoidal (J := J) (D := D)
  let := Functor.constMapDerivedCategoryLifting hresD hresJD
  have h := Localization.Monoidal.functorMonoidalOfComp_μ
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor D))
      (kFlatQuasiIso (curriedTensor D))
      (Iso.refl ((kFlatQ (curriedTensor D)).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor D))
    (Functor.constMapDerivedCategoryLocalized hresD hresJD)
    (Functor.constKFlatLift (J := J) (D := D) ⋙
      Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor (J ⥤ D)))
        (kFlatQuasiIso (curriedTensor (J ⥤ D)))
        (Iso.refl ((kFlatQ (curriedTensor (J ⥤ D))).obj (𝟙_ _)))) X Y
  exact h.trans (mu_constKFlatLift_comp_kFlatQ_grouped hresD hresJD X Y)

omit [HasColimitsOfSize.{0, 0} D] in
/-- **The unit constraint of `(Functor.const J).mapDerivedCategory`.**  It is the unit
constraint of `CategoryTheory.Functor.constKFlatLift` followed by the K-flat localization of
`J ⥤ D`, followed by the inverse of `CategoryTheory.Functor.mapDerivedCategoryFactorsh` at the
unit and the image of the oplax unit constraint of the K-flat localization of `D`. -/
lemma Functor.epsilon_constMapDerivedCategory :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := kFlatQ_isLocalization (curriedTensor D) hresD
    letI := kFlatQ_isLocalization (curriedTensor (J ⥤ D)) hresJD
    letI := Functor.constKFlatLiftMonoidal (J := J) (D := D)
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    Functor.LaxMonoidal.ε ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory) =
      Functor.LaxMonoidal.ε
          (Functor.constKFlatLift (J := J) (D := D) ⋙
            Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor (J ⥤ D)))
              (kFlatQuasiIso (curriedTensor (J ⥤ D)))
              (Iso.refl ((kFlatQ (curriedTensor (J ⥤ D))).obj (𝟙_ _)))) ≫
        (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.inv.app
            (𝟙_ (kFlatObjects (curriedTensor D)).FullSubcategory).obj ≫
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
            (Functor.OplaxMonoidal.η
              (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor D))
                (kFlatQuasiIso (curriedTensor D))
                (Iso.refl ((kFlatQ (curriedTensor D)).obj (𝟙_ _))))) := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := kFlatQ_isLocalization (curriedTensor D) hresD
  let := kFlatQ_isLocalization (curriedTensor (J ⥤ D)) hresJD
  let := Functor.constKFlatLiftMonoidal (J := J) (D := D)
  let := Functor.constMapDerivedCategoryLifting hresD hresJD
  exact Localization.Monoidal.functorMonoidalOfComp_ε
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor D))
      (kFlatQuasiIso (curriedTensor D))
      (Iso.refl ((kFlatQ (curriedTensor D)).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor D))
    (Functor.constMapDerivedCategoryLocalized hresD hresJD)
    (Functor.constKFlatLift (J := J) (D := D) ⋙
      Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor (J ⥤ D)))
        (kFlatQuasiIso (curriedTensor (J ⥤ D)))
        (Iso.refl ((kFlatQ (curriedTensor (J ⥤ D))).obj (𝟙_ _))))

end Derived

end CategoryTheory

end
