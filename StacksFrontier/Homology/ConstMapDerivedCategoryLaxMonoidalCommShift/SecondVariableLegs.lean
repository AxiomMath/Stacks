module

public import StacksFrontier.Homology.ConstMapDerivedCategoryLaxMonoidalCommShift.FirstVariable

/-!
# The legs of the second-variable chain of the derived constant tensorator

The legs of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex, and
the shift-compatibility of the whole chain.
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
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd1 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
      (((Functor.associator (kFlatComplexes (curriedTensor D)).ι (DerivedCategory.Q (C := D))
          (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory) ⋙
          (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj K))))).hom) ≫
      (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (DerivedCategory.Q (C := D))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
          (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj K)))).inv)) ℤ := by
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  have g0 : NatTrans.CommShift
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι (DerivedCategory.Q (C := D))
          (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory) ⋙
          (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj K))))).hom) ℤ := inferInstance
  have g1 : NatTrans.CommShift
      (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (DerivedCategory.Q (C := D))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
          (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj K)))).inv) ℤ := inferInstance
  exact NatTrans.commShift_comp_of_eq_data _ _ g0 (g1)

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd2 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerLeft ((DerivedCategory.Q (C := D)) ⋙
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory))
          ((curriedTensor (DerivedCategory (J ⥤ D))).map
          (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).hom.app K.obj))))) ℤ := by
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
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd3 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerRight ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).hom
          (tensorLeft ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj)))))) ℤ := by
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd4 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
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
          (kFlatComplexes (curriedTensor (J ⥤ D))).ι ((DerivedCategory.Q (C := J ⥤ D)) ⋙
          (tensorLeft ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj))))).hom) ≫
      (Functor.whiskerLeft (Functor.constKFlatComplexLift (J := J) (D := D))
          (Functor.associator (kFlatComplexes (curriedTensor (J ⥤ D))).ι
          (DerivedCategory.Q (C := J ⥤ D)) (tensorLeft ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj)))).inv)) ℤ := by
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  have g0 : NatTrans.CommShift
      (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) (DerivedCategory.Q (C := J ⥤ D))
          (tensorLeft ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj)))).hom) ℤ := inferInstance
  have g1 : NatTrans.CommShift
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorLeft
          ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj))))).inv) ℤ := inferInstance
  have g2 : NatTrans.CommShift
      (Functor.whiskerRight ((kFlatComplexes (curriedTensor (J ⥤ D))).liftCompιIso
          ((kFlatComplexes (curriedTensor D)).ι ⋙
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlat_constMapHomologicalComplex K.obj K.property)).inv
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorLeft
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              K.obj))))) ℤ := inferInstance
  have g3 : NatTrans.CommShift
      ((Functor.associator (Functor.constKFlatComplexLift (J := J) (D := D))
          (kFlatComplexes (curriedTensor (J ⥤ D))).ι ((DerivedCategory.Q (C := J ⥤ D)) ⋙
          (tensorLeft ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj))))).hom) ℤ := inferInstance
  have g4 : NatTrans.CommShift
      (Functor.whiskerLeft (Functor.constKFlatComplexLift (J := J) (D := D))
          (Functor.associator (kFlatComplexes (curriedTensor (J ⥤ D))).ι
          (DerivedCategory.Q (C := J ⥤ D)) (tensorLeft ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          K.obj)))).inv) ℤ := inferInstance
  exact NatTrans.commShift_comp_of_eq_data _ _ g0 (NatTrans.commShift_comp_of_eq_data _ _ g1
      (NatTrans.commShift_comp_of_eq_data _ _ g2 (NatTrans.commShift_comp_of_eq_data _ _ g3 (g4))))

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd5 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
      ((Functor.whiskerLeft (Functor.constKFlatComplexLift (J := J) (D := D))
          (derivedTensorSecondIso (J ⥤ D) hresJD
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj)
          (kFlatLeft_of_kFlat (J ⥤ D) (kFlat_constMapHomologicalComplex K.obj K.property))).hom))
              ℤ := by
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
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd6 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
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
          (ComplexShape.up ℤ)) (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj)) (DerivedCategory.Q (C := J ⥤ D))).inv)) ℤ := by
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  have g0 : NatTrans.CommShift
      ((Functor.associator (Functor.constKFlatComplexLift (J := J) (D := D))
          (kFlatComplexes (curriedTensor (J ⥤ D))).ι ((tensorLeft
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj)) ⋙
          (DerivedCategory.Q (C := J ⥤ D)))).inv) ℤ := inferInstance
  have g1 : NatTrans.CommShift
      (Functor.whiskerRight ((kFlatComplexes (curriedTensor (J ⥤ D))).liftCompιIso
          ((kFlatComplexes (curriedTensor D)).ι ⋙
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlat_constMapHomologicalComplex K.obj K.property)).hom
              ((tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))) ℤ :=
              inferInstance
  have g2 : NatTrans.CommShift
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          ((tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))).hom) ℤ :=
          inferInstance
  have g3 : NatTrans.CommShift
      (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) (tensorLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj)) (DerivedCategory.Q (C := J ⥤ D))).inv) ℤ := inferInstance
  exact NatTrans.commShift_comp_of_eq_data _ _ g0 (NatTrans.commShift_comp_of_eq_data _ _ g1
      (NatTrans.commShift_comp_of_eq_data _ _ g2 (g3)))

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd7 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerRight (Functor.LaxMonoidal.μNatTransSnd
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)) K.obj)
          (DerivedCategory.Q (C := J ⥤ D))))) ℤ := by
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd8 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (tensorLeft K.obj)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.Q (C := J ⥤ D))).hom)) ℤ := by
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd9 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerLeft (tensorLeft K.obj)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).inv))) ℤ := by
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd10 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (tensorLeft K.obj) (DerivedCategory.Q (C := D))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ≫
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((tensorLeft K.obj) ⋙ (DerivedCategory.Q (C := D)))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv)) ℤ := by
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  have g0 : NatTrans.CommShift
      (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (tensorLeft K.obj) (DerivedCategory.Q (C := D))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ℤ := inferInstance
  have g1 : NatTrans.CommShift
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((tensorLeft K.obj) ⋙ (DerivedCategory.Q (C := D)))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ℤ := inferInstance
  exact NatTrans.commShift_comp_of_eq_data _ _ g0 (g1)

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd11 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
      ((Functor.whiskerRight (derivedTensorSecondIso D hresD K.obj
          (kFlatLeft_of_kFlat D K.property)).inv
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory))) ℤ := by
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
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- One leg of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the second variable at the image of a K-flat complex:
every factor of it is shift-compatible, and the junctions are joined by
`CategoryTheory.NatTrans.commShift_comp_of_eq_data`. -/
private theorem legSnd12 (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
      (((Functor.associator ((kFlatComplexes (curriedTensor D)).ι ⋙ (DerivedCategory.Q (C := D)))
          (tensorLeft ((DerivedCategory.Q (C := D)).obj K.obj))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).hom)) ℤ := by
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  infer_instance

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- **The whole reassociated chain is shift-compatible**, by composing its legs across the
junctions where the two commutation data are the same structure spelled two ways. -/
theorem hchainSnd (K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
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
    NatTrans.CommShift
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
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).hom))) ℤ := by
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  let := Functor.constKFlatComplexLift_commShift (J := J) (D := D)
  exact NatTrans.commShift_comp_of_eq_data _ _ (legSnd1 hresD hresJD K)
    (NatTrans.commShift_comp_of_eq_data _ _ (legSnd2 hresD hresJD K)
    (NatTrans.commShift_comp_of_eq_data _ _ (legSnd3 hresD hresJD K)
    (NatTrans.commShift_comp_of_eq_data _ _ (legSnd4 hresD hresJD K)
    (NatTrans.commShift_comp_of_eq_data _ _ (legSnd5 hresD hresJD K)
    (NatTrans.commShift_comp_of_eq_data _ _ (legSnd6 hresD hresJD K)
    (NatTrans.commShift_comp_of_eq_data _ _ (legSnd7 hresD hresJD K)
    (NatTrans.commShift_comp_of_eq_data _ _ (legSnd8 hresD hresJD K)
    (NatTrans.commShift_comp_of_eq_data _ _ (legSnd9 hresD hresJD K)
    (NatTrans.commShift_comp_of_eq_data _ _ (legSnd10 hresD hresJD K)
    (NatTrans.commShift_comp_of_eq_data _ _ (legSnd11 hresD hresJD K)
    (legSnd12 hresD hresJD K)))))))))))

end CategoryTheory

end
