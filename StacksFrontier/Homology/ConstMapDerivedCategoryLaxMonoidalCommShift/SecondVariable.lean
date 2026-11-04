module

public import StacksFrontier.Homology.ConstMapDerivedCategoryLaxMonoidalCommShift.SecondVariableLegs

/-!
# The derived constant tensorator commutes with the shift

The identity blocks of the second-variable chain and the identification of the tensorator with it,
`CategoryTheory.commShift_muNatTransSnd_constMapDerivedCategory_kFlat`, and the main result
`CategoryTheory.constMapDerivedCategoryLaxMonoidalCommShift`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

universe w w' v u v₁ u₁ v₂ u₂

namespace CategoryTheory

attribute [local instance] homotopyMonoidal homotopyBraided

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCoproducts.{0} D] [HasColimitsOfSize.{0, 0} D] [HasInitial D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]
  [SymmetricCategory (CochainComplex D ℤ)] [SymmetricCategory (CochainComplex (J ⥤ D) ℤ)]
  [HasDerivedCategory.{w} D] [HasDerivedCategory.{w'} (J ⥤ D)]
  (hresD : ∀ G : CochainComplex D ℤ, ∃ (P : CochainComplex D ℤ) (f : P ⟶ G),
    KFlat (curriedTensor D) P ∧ QuasiIso f)
  (hresJD : ∀ G : CochainComplex (J ⥤ D) ℤ, ∃ (P : CochainComplex (J ⥤ D) ℤ) (f : P ⟶ G),
    KFlat (curriedTensor (J ⥤ D)) P ∧ QuasiIso f)


omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idSnd1 (K L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
    ((((Functor.associator (kFlatComplexes (curriedTensor D)).ι (DerivedCategory.Q (C := D))
      (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory) ⋙
      (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
      ((kFlatComplexQ (curriedTensor D)).obj K))))).hom) ≫
      (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (DerivedCategory.Q (C := D))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
          (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj K)))).inv))).app L = 𝟙 _ := by
  let := derivedMonoidal_tensorCommShift D hresD
  let := derivedMonoidal_tensorCommShift (J ⥤ D) hresJD
  exact idComp2 (by rfl)
      (by rfl)

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idSnd2 (K L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
    (((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
      (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
      (ComplexShape.up ℤ)) (DerivedCategory.Q (C := J ⥤ D))
      (tensorLeft ((DerivedCategory.Q (C := J ⥤ D)).obj
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K.obj)))).hom) ≫
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorLeft
          ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj))))).inv) ≫
      (Functor.whiskerRight ((kFlatComplexes (curriedTensor (J ⥤ D))).liftCompιIso
          ((kFlatComplexes (curriedTensor D)).ι ⋙
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlat_constMapHomologicalComplex K.obj K.property)).inv
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorLeft
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              K.obj))))) ≫
      ((Functor.associator (Functor.constKFlatComplexLift (J := J) (D := D))
          (kFlatComplexes (curriedTensor (J ⥤ D))).ι ((DerivedCategory.Q (C := J ⥤ D)) ⋙
          (tensorLeft ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj))))).hom) ≫
      (Functor.whiskerLeft (Functor.constKFlatComplexLift (J := J) (D := D))
          (Functor.associator (kFlatComplexes (curriedTensor (J ⥤ D))).ι
          (DerivedCategory.Q (C := J ⥤ D)) (tensorLeft ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj)))).inv))).app L = 𝟙 _ := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := derivedMonoidal_tensorCommShift D hresD
  let := derivedMonoidal_tensorCommShift (J ⥤ D) hresJD
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  have h2 : ((kFlatComplexes (curriedTensor (J ⥤ D))).liftCompιIso
        ((kFlatComplexes (curriedTensor D)).ι ⋙
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
        (fun K => kFlat_constMapHomologicalComplex K.obj K.property)).inv.app L = 𝟙 _ := rfl
  exact idComp5 (by rfl)
      (by rfl) (by first | rfl | (simp [h2]; try rfl))
      (by rfl) (by rfl)

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idSnd3 (K L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
    ((((Functor.associator (Functor.constKFlatComplexLift (J := J) (D := D))
      (kFlatComplexes (curriedTensor (J ⥤ D))).ι ((tensorLeft
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj)) ⋙
      (DerivedCategory.Q (C := J ⥤ D)))).inv) ≫
      (Functor.whiskerRight ((kFlatComplexes (curriedTensor (J ⥤ D))).liftCompιIso
          ((kFlatComplexes (curriedTensor D)).ι ⋙
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlat_constMapHomologicalComplex K.obj K.property)).hom
              ((tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))) ≫
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          ((tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))).hom) ≫
      (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj)) (DerivedCategory.Q (C := J ⥤ D))).inv))).app L = 𝟙 _ :=
          by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := derivedMonoidal_tensorCommShift D hresD
  let := derivedMonoidal_tensorCommShift (J ⥤ D) hresJD
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  have h1 : ((kFlatComplexes (curriedTensor (J ⥤ D))).liftCompιIso
        ((kFlatComplexes (curriedTensor D)).ι ⋙
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
        (fun K => kFlat_constMapHomologicalComplex K.obj K.property)).hom.app L = 𝟙 _ := rfl
  exact idComp4 (by rfl)
      (by first | rfl | (simp [h1]; try rfl)) (by rfl)
      (by rfl)

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idSnd4 (K L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
    (((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
        (Functor.associator (tensorLeft K.obj)
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.Q (C := J ⥤ D))).hom))).app L = 𝟙 _ := by
  let := derivedMonoidal_tensorCommShift D hresD
  let := derivedMonoidal_tensorCommShift (J ⥤ D) hresJD
  rfl

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idSnd5 (K L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
    (((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
      (Functor.associator (tensorLeft K.obj) (DerivedCategory.Q (C := D))
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ≫
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((tensorLeft K.obj) ⋙ (DerivedCategory.Q (C := D)))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv))).app L = 𝟙 _ := by
  let := derivedMonoidal_tensorCommShift D hresD
  let := derivedMonoidal_tensorCommShift (J ⥤ D) hresJD
  exact idComp2 (by rfl)
      (by rfl)

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idSnd6 (K L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
    ((((Functor.associator ((kFlatComplexes (curriedTensor D)).ι ⋙ (DerivedCategory.Q (C := D)))
        (tensorLeft ((DerivedCategory.Q (C := D)).obj K.obj))
        ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).hom))).app L = 𝟙 _ := by
  let := derivedMonoidal_tensorCommShift D hresD
  let := derivedMonoidal_tensorCommShift (J ⥤ D) hresJD
  rfl

include hresD hresJD in
/-- **The tensorator, whiskered to the K-flat complexes and read in the second variable, IS the
reassociated chain**: componentwise this is
`CategoryTheory.Functor.mu_constMapDerivedCategory_eq`, with the two K-flat comparisons put at
the spelling of `CochainComplex.KFlatMonoidal.derivedTensorIso` and every reassociation
cancelled. -/
private theorem keySnd (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
    (kFlatComplexQ (curriedTensor D)).whiskerLeft
        (Functor.LaxMonoidal.μNatTransSnd
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
          ((kFlatComplexQ (curriedTensor D)).obj K)) =
      ((((Functor.associator (kFlatComplexes (curriedTensor D)).ι (DerivedCategory.Q (C := D))
          (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory) ⋙
          (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj K))))).hom) ≫
          (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
              (Functor.associator (DerivedCategory.Q (C := D))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
              (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
              ((kFlatComplexQ (curriedTensor D)).obj K)))).inv)) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerLeft ((DerivedCategory.Q (C := D)) ⋙
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory))
          ((curriedTensor (DerivedCategory (J ⥤ D))).map
          (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).hom.app K.obj))))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerRight ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).hom
          (tensorLeft ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj)))))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) (DerivedCategory.Q (C := J ⥤ D))
          (tensorLeft ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj)))).hom) ≫
          ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorLeft
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              K.obj))))).inv) ≫
          (Functor.whiskerRight ((kFlatComplexes (curriedTensor (J ⥤ D))).liftCompιIso
              ((kFlatComplexes (curriedTensor D)).ι ⋙
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlat_constMapHomologicalComplex K.obj K.property)).inv
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorLeft
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              K.obj))))) ≫
          ((Functor.associator (Functor.constKFlatComplexLift (J := J) (D := D))
              (kFlatComplexes (curriedTensor (J ⥤ D))).ι
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorLeft
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              K.obj))))).hom) ≫
          (Functor.whiskerLeft (Functor.constKFlatComplexLift (J := J) (D := D))
              (Functor.associator (kFlatComplexes (curriedTensor (J ⥤ D))).ι
              (DerivedCategory.Q (C := J ⥤ D)) (tensorLeft
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              K.obj)))).inv)) ≫
      ((Functor.whiskerLeft (Functor.constKFlatComplexLift (J := J) (D := D))
          (derivedTensorSecondIso (J ⥤ D) hresJD
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj)
          (kFlatLeft_of_kFlat (J ⥤ D) (kFlat_constMapHomologicalComplex K.obj K.property))).hom)) ≫
      (((Functor.associator (Functor.constKFlatComplexLift (J := J) (D := D))
          (kFlatComplexes (curriedTensor (J ⥤ D))).ι ((tensorLeft
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj)) ⋙
          (DerivedCategory.Q (C := J ⥤ D)))).inv) ≫
          (Functor.whiskerRight ((kFlatComplexes (curriedTensor (J ⥤ D))).liftCompιIso
              ((kFlatComplexes (curriedTensor D)).ι ⋙
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlat_constMapHomologicalComplex K.obj K.property)).hom
              ((tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))) ≫
          ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
              ((tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))).hom) ≫
          (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
              (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ))
              (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K.obj)) (DerivedCategory.Q (C := J ⥤ D))).inv)) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerRight (Functor.LaxMonoidal.μNatTransSnd
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)) K.obj)
          (DerivedCategory.Q (C := J ⥤ D))))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (tensorLeft K.obj)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.Q (C := J ⥤ D))).hom)) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerLeft (tensorLeft K.obj)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).inv))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (tensorLeft K.obj) (DerivedCategory.Q (C := D))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ≫
          ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
              ((tensorLeft K.obj) ⋙ (DerivedCategory.Q (C := D)))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv)) ≫
      ((Functor.whiskerRight (derivedTensorSecondIso D hresD K.obj
          (kFlatLeft_of_kFlat D K.property)).inv
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory))) ≫
      (((Functor.associator ((kFlatComplexes (curriedTensor D)).ι ⋙ (DerivedCategory.Q (C := D)))
          (tensorLeft ((DerivedCategory.Q (C := D)).obj K.obj))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).hom))) := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := derivedMonoidal_tensorCommShift D hresD
  let := derivedMonoidal_tensorCommShift (J ⥤ D) hresJD
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  ext L
  have hiso : (derivedTensorSecondIso D hresD K.obj (kFlatLeft_of_kFlat D K.property)).app L =
      derivedTensorIso D hresD K.property L.property :=
    Iso.ext (derivedTensorSecondIso_hom_app D hresD K.property L)
  exact chainCongr (idSnd1 hresD hresJD K L) (idSnd2 hresD hresJD K L)
    (idSnd3 hresD hresJD K L) (idSnd4 hresD hresJD K L) (idSnd5 hresD hresJD K L)
    (idSnd6 hresD hresJD K L)
    (derivedTensorSecondIso_hom_app (J ⥤ D) hresJD
      (kFlat_constMapHomologicalComplex K.obj K.property)
      (Functor.constKFlatComplexLift.obj L))
    (congrArg ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map (congrArg Iso.inv hiso))
    (Functor.mu_constMapDerivedCategory_eq hresD hresJD K.property L.property)

include hresD hresJD in
/-- The second-variable half. -/
theorem commShift_muNatTransSnd_constMapDerivedCategory_kFlat
    (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
    NatTrans.CommShift ((kFlatComplexQ (curriedTensor D)).whiskerLeft
      (Functor.LaxMonoidal.μNatTransSnd
        ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
        ((kFlatComplexQ (curriedTensor D)).obj K))) ℤ := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := derivedMonoidal_tensorCommShift D hresD
  let := derivedMonoidal_tensorCommShift (J ⥤ D) hresJD
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  have := derivedTensorSecondIso_commShift (J ⥤ D) hresJD
    (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj)
    (kFlatLeft_of_kFlat (J ⥤ D) (kFlat_constMapHomologicalComplex K.obj K.property))
  have := derivedTensorSecondIso_commShift D hresD K.obj (kFlatLeft_of_kFlat D K.property)
  have : NatTrans.CommShift ((kFlatComplexes (curriedTensor (J ⥤ D))).liftCompιIso
        ((kFlatComplexes (curriedTensor D)).ι ⋙
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
        (fun K => kFlat_constMapHomologicalComplex K.obj K.property)).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ ℤ
  have := Functor.commShift_μNatTransSnd_mapHomologicalComplex
    (Functor.const J : D ⥤ (J ⥤ D)) K.obj
  have := hchainSnd hresD hresJD K
  exact NatTrans.commShift_of_eq (keySnd hresD hresJD K)


include hresD hresJD in
/-- **The tensorator of the derived constant diagram commutes with the shift.**  By
`CategoryTheory.Functor.LaxMonoidal.CommShift.of_essSurj` the condition may be tested after
restriction along `CochainComplex.KFlatBifunctor.kFlatComplexQ`, which is essentially surjective
because the K-flat objects of `K(D)` are (`CochainComplex.KFlatBifunctor.kFlatQ_essSurj`) and
every K-flat object is the homotopy class of a K-flat complex; the two restricted readings are
`CategoryTheory.commShift_muNatTransFst_constMapDerivedCategory_kFlat` and
`commShift_muNatTransSnd_constMapDerivedCategory_kFlat`.

This is the hypothesis `hμ` of
`Stacks.CategoryHomology.commShift_externalMateNatTransFst_derivedExternalTensor`. -/
theorem constMapDerivedCategoryLaxMonoidalCommShift :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    Functor.LaxMonoidal.CommShift
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory) ℤ := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := derivedMonoidal_tensorCommShift D hresD
  let := derivedMonoidal_tensorCommShift (J ⥤ D) hresJD
  have hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D) :=
    fun _ hK => kFlatLeft_of_kFlat D hK
  have : (kFlatComplexQ (curriedTensor D)).EssSurj := by
    let := kFlatQ_isLocalization (curriedTensor D) hresD
    have := kFlatQ_essSurj (curriedTensor D)
    exact Functor.essSurj_of_iso (kFlatQuotientCompQIso (curriedTensor D))
  exact Functor.LaxMonoidal.CommShift.of_essSurj _ ℤ (kFlatComplexQ (curriedTensor D))
    (fun L => commShift_muNatTransFst_constMapDerivedCategory_kFlat hresD hresJD hle L)
    (fun K => commShift_muNatTransSnd_constMapDerivedCategory_kFlat hresD hresJD K)

end CategoryTheory

end
