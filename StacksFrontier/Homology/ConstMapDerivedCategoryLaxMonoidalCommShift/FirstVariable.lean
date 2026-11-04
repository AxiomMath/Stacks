module

public import StacksFrontier.Homology.ConstMapDerivedCategoryLaxMonoidalCommShift.FirstVariableLegs

/-!
# The derived constant tensorator in the first variable commutes with the shift

The shift-compatibility of the reassociated chain computing the tensorator of
`(Functor.const J).mapDerivedCategory` in the first variable at the image of a K-flat complex, its
identity blocks, the identification of the tensorator with it, and hence
`CategoryTheory.commShift_muNatTransFst_constMapDerivedCategory_kFlat`.
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
/-- **The whole reassociated chain is shift-compatible**, by composing its legs across the
junctions where the two commutation data are the same structure spelled two ways. -/
private theorem hchainFst
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift
      ((((Functor.associator (kFlatComplexes (curriedTensor D)).ι (DerivedCategory.Q (C := D))
          (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory) ⋙
          (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj L))))).hom) ≫
          (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
              (Functor.associator (DerivedCategory.Q (C := D))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
              (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
              ((kFlatComplexQ (curriedTensor D)).obj L)))).inv)) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerRight ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).hom
          (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj L)))))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))
          ((curriedTensor (DerivedCategory (J ⥤ D))).flip.map
          (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).hom.app L.obj))))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) (DerivedCategory.Q (C := J ⥤ D))
          (tensorRight ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          L.obj)))).hom) ≫
          ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              L.obj))))).inv) ≫
          (Functor.whiskerRight ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
              ((kFlatComplexes (curriedTensor D)).ι ⋙
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).inv
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              L.obj))))) ≫
          ((Functor.associator (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
              (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              L.obj))))).hom) ≫
          (Functor.whiskerLeft (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
              (Functor.associator (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι
              (DerivedCategory.Q (C := J ⥤ D)) (tensorRight
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              L.obj)))).inv)) ≫
      ((Functor.whiskerLeft (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
          (derivedTensorFirstIso (J ⥤ D) hresJD
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)
          (kFlat_constMapHomologicalComplex L.obj L.property)).hom)) ≫
      (((Functor.associator (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
          (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι
          ((tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))).inv) ≫
          (Functor.whiskerRight ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
              ((kFlatComplexes (curriedTensor D)).ι ⋙
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).hom
              ((tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))) ≫
          ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
              ((tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))).hom) ≫
          (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
              (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ))
              (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L.obj)) (DerivedCategory.Q (C := J ⥤ D))).inv)) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerRight (Functor.LaxMonoidal.μNatTransFst
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)) L.obj)
          (DerivedCategory.Q (C := J ⥤ D))))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (tensorRight L.obj)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.Q (C := J ⥤ D))).hom)) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerLeft (tensorRight L.obj)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).inv))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (tensorRight L.obj) (DerivedCategory.Q (C := D))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ≫
          ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
              ((tensorRight L.obj) ⋙ (DerivedCategory.Q (C := D)))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ≫
          (Functor.whiskerRight (Functor.whiskerRight (ObjectProperty.ιOfLECompιIso hle).inv
              ((tensorRight L.obj) ⋙ (DerivedCategory.Q (C := D))))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
          (Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
              (kFlatComplexesLeft (curriedTensor D)).ι ((tensorRight L.obj) ⋙
              (DerivedCategory.Q (C := D)))).hom
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory))) ≫
      ((Functor.whiskerRight (Functor.whiskerLeft (ObjectProperty.ιOfLE hle)
          (derivedTensorFirstIso D hresD L.obj L.property).inv)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory))) ≫
      ((Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
          ((kFlatComplexesLeft (curriedTensor D)).ι ⋙ (DerivedCategory.Q (C := D)))
          (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L))).inv
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
          (Functor.whiskerRight (Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
              (kFlatComplexesLeft (curriedTensor D)).ι (DerivedCategory.Q (C := D))).inv
              (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L)))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
          (Functor.whiskerRight (Functor.whiskerRight (Functor.whiskerRight
              (ObjectProperty.ιOfLECompιIso hle).hom (DerivedCategory.Q (C := D)))
              (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L)))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
          ((Functor.associator ((kFlatComplexes (curriedTensor D)).ι ⋙ (DerivedCategory.Q (C := D)))
              (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).hom))) ℤ := by
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
  let := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  have := derivedTensorFirstIso_commShift (J ⥤ D) hresJD
    (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)
    (kFlat_constMapHomologicalComplex L.obj L.property)
  have := derivedTensorFirstIso_commShift D hresD L.obj L.property
  have : NatTrans.CommShift ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
        ((kFlatComplexes (curriedTensor D)).ι ⋙
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
        (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).hom
            ℤ :=
    Functor.CommShift.ofComp_compatibility _ ℤ
  have : NatTrans.CommShift (ObjectProperty.ιOfLECompιIso hle).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ ℤ
  have := Functor.commShift_μNatTransFst_mapHomologicalComplex
    (Functor.const J : D ⥤ (J ⥤ D)) L.obj
  exact NatTrans.commShift_comp_of_eq_data _ _ (legFst1 hresD hresJD hle L)
    (NatTrans.commShift_comp_of_eq_data _ _ (legFst2 hresD hresJD hle L)
    (NatTrans.commShift_comp_of_eq_data _ _ (legFst3 hresD hresJD hle L)
    (NatTrans.commShift_comp_of_eq_data _ _ (legFst4 hresD hresJD hle L)
    (NatTrans.commShift_comp_of_eq_data _ _ (legFst5 hresD hresJD hle L)
    (NatTrans.commShift_comp_of_eq_data _ _ (legFst6 hresD hresJD hle L)
    (NatTrans.commShift_comp_of_eq_data _ _ (legFst7 hresD hresJD hle L)
    (NatTrans.commShift_comp_of_eq_data _ _ (legFst8 hresD hresJD hle L)
    (NatTrans.commShift_comp_of_eq_data _ _ (legFst9 hresD hresJD hle L)
    (NatTrans.commShift_comp_of_eq_data _ _ (legFst10 hresD hresJD hle L)
    (NatTrans.commShift_comp_of_eq_data _ _ (legFst11 hresD hresJD hle L)
    (legFst12 hresD hresJD hle L)))))))))))

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idFst1 (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    ((((Functor.associator (kFlatComplexes (curriedTensor D)).ι (DerivedCategory.Q (C := D))
      (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory) ⋙
      (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
      ((kFlatComplexQ (curriedTensor D)).obj L))))).hom) ≫
      (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (DerivedCategory.Q (C := D))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
          (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj L)))).inv))).app K = 𝟙 _ := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  exact idComp2 (by rfl)
      (by rfl)

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idFst2 (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    (((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
      (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
      (ComplexShape.up ℤ)) (DerivedCategory.Q (C := J ⥤ D))
      (tensorRight ((DerivedCategory.Q (C := J ⥤ D)).obj
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      L.obj)))).hom) ≫
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
          ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          L.obj))))).inv) ≫
      (Functor.whiskerRight ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
          ((kFlatComplexes (curriedTensor D)).ι ⋙
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).inv
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              L.obj))))) ≫
      ((Functor.associator (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
          (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι
          ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
          ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          L.obj))))).hom) ≫
      (Functor.whiskerLeft (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
          (Functor.associator (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι
          (DerivedCategory.Q (C := J ⥤ D)) (tensorRight
          ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          L.obj)))).inv))).app K = 𝟙 _ := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  have h : ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
        ((kFlatComplexes (curriedTensor D)).ι ⋙
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
        (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).inv.app
      K = 𝟙 _ := rfl
  exact idComp5 (by rfl)
      (by rfl)
      (by first | rfl | (simp [h]; try rfl))
      (by rfl)
      (by rfl)

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idFst3 (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    ((((Functor.associator (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
      (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι ((tensorRight
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)) ⋙
      (DerivedCategory.Q (C := J ⥤ D)))).inv) ≫
      (Functor.whiskerRight ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
          ((kFlatComplexes (curriedTensor D)).ι ⋙
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).hom
              ((tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))) ≫
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          ((tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))).hom) ≫
      (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj)) (DerivedCategory.Q (C := J ⥤ D))).inv))).app K = 𝟙 _ :=
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
  have h : ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
        ((kFlatComplexes (curriedTensor D)).ι ⋙
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
        (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).hom.app
      K = 𝟙 _ := rfl
  exact idComp4 (by rfl)
      (by first | rfl | (simp [h]; try rfl))
      (by rfl)
      (by rfl)

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idFst4 (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    (((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
        (Functor.associator (tensorRight L.obj)
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.Q (C := J ⥤ D))).hom))).app K = 𝟙 _ := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  rfl

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idFst5 (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    (((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
      (Functor.associator (tensorRight L.obj) (DerivedCategory.Q (C := D))
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ≫
      ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
          ((tensorRight L.obj) ⋙ (DerivedCategory.Q (C := D)))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ≫
      (Functor.whiskerRight (Functor.whiskerRight (ObjectProperty.ιOfLECompιIso hle).inv
          ((tensorRight L.obj) ⋙ (DerivedCategory.Q (C := D))))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
      (Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
          (kFlatComplexesLeft (curriedTensor D)).ι ((tensorRight L.obj) ⋙
          (DerivedCategory.Q (C := D)))).hom
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)))).app K = 𝟙 _ := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  have h : (ObjectProperty.ιOfLECompιIso hle).inv.app K = 𝟙 _ := rfl
  exact idComp4 (by rfl)
      (by rfl)
      (by first | rfl | (simp [h]; try rfl))
      (by first | rfl | (simp; try rfl))

omit [HasColimitsOfSize.{0, 0} D] in
include hresD hresJD in
/-- A block of reassociations in the chain is the identity on components: associators, the
comparison of `CategoryTheory.ObjectProperty.lift` with the inclusion, and their images under
functors. -/
private lemma idFst6 (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L K : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    (((Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
      ((kFlatComplexesLeft (curriedTensor D)).ι ⋙ (DerivedCategory.Q (C := D)))
      (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L))).inv
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
      (Functor.whiskerRight (Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
          (kFlatComplexesLeft (curriedTensor D)).ι (DerivedCategory.Q (C := D))).inv
          (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L)))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
      (Functor.whiskerRight (Functor.whiskerRight (Functor.whiskerRight
          (ObjectProperty.ιOfLECompιIso hle).hom (DerivedCategory.Q (C := D)))
          (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L)))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
      ((Functor.associator ((kFlatComplexes (curriedTensor D)).ι ⋙ (DerivedCategory.Q (C := D)))
          (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).hom))).app K = 𝟙 _ := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  let := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
  let := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
  let := fun K : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
  let := fun M : DerivedCategory (J ⥤ D) =>
    derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
  have h : (ObjectProperty.ιOfLECompιIso hle).hom.app K = 𝟙 _ := rfl
  exact idComp4 (by first | rfl | (simp; try rfl))
      (by first | rfl | (simp; try rfl))
      (by first | rfl | (simp [h]; try rfl))
      (by rfl)

include hresD hresJD in
/-- **The tensorator, whiskered to the K-flat complexes and read in the first variable, IS the
reassociated chain**: componentwise this is
`CategoryTheory.Functor.mu_constMapDerivedCategory_eq`, with the two K-flat comparisons put at
the spelling of `CochainComplex.KFlatMonoidal.derivedTensorIso` and every reassociation
cancelled. -/
private theorem keyFst
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    (kFlatComplexQ (curriedTensor D)).whiskerLeft
        (Functor.LaxMonoidal.μNatTransFst
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
          ((kFlatComplexQ (curriedTensor D)).obj L)) =
      ((((Functor.associator (kFlatComplexes (curriedTensor D)).ι (DerivedCategory.Q (C := D))
          (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory) ⋙
          (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj L))))).hom) ≫
          (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
              (Functor.associator (DerivedCategory.Q (C := D))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
              (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
              ((kFlatComplexQ (curriedTensor D)).obj L)))).inv)) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerRight ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).hom
          (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
          ((kFlatComplexQ (curriedTensor D)).obj L)))))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerLeft (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))
          ((curriedTensor (DerivedCategory (J ⥤ D))).flip.map
          (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).hom.app L.obj))))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)) (DerivedCategory.Q (C := J ⥤ D))
          (tensorRight ((DerivedCategory.Q (C := J ⥤ D)).obj
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          L.obj)))).hom) ≫
          ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              L.obj))))).inv) ≫
          (Functor.whiskerRight ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
              ((kFlatComplexes (curriedTensor D)).ι ⋙
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).inv
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              L.obj))))) ≫
          ((Functor.associator (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
              (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι
              ((DerivedCategory.Q (C := J ⥤ D)) ⋙ (tensorRight
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              L.obj))))).hom) ≫
          (Functor.whiskerLeft (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
              (Functor.associator (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι
              (DerivedCategory.Q (C := J ⥤ D)) (tensorRight
              ((DerivedCategory.Q (C := J ⥤ D)).obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              L.obj)))).inv)) ≫
      ((Functor.whiskerLeft (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
          (derivedTensorFirstIso (J ⥤ D) hresJD
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)
          (kFlat_constMapHomologicalComplex L.obj L.property)).hom)) ≫
      (((Functor.associator (Functor.constKFlatComplexLiftLeft (J := J) (D := D))
          (kFlatComplexesLeft (curriedTensor (J ⥤ D))).ι
          ((tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))).inv) ≫
          (Functor.whiskerRight ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
              ((kFlatComplexes (curriedTensor D)).ι ⋙
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
          (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).hom
              ((tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))) ≫
          ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
              ((tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L.obj)) ⋙ (DerivedCategory.Q (C := J ⥤ D)))).hom) ≫
          (Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
              (Functor.associator ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ))
              (tensorRight (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L.obj)) (DerivedCategory.Q (C := J ⥤ D))).inv)) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerRight (Functor.LaxMonoidal.μNatTransFst
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)) L.obj)
          (DerivedCategory.Q (C := J ⥤ D))))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (tensorRight L.obj)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.Q (C := J ⥤ D))).hom)) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.whiskerLeft (tensorRight L.obj)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors).inv))) ≫
      ((Functor.whiskerLeft (kFlatComplexes (curriedTensor D)).ι
          (Functor.associator (tensorRight L.obj) (DerivedCategory.Q (C := D))
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ≫
          ((Functor.associator (kFlatComplexes (curriedTensor D)).ι
              ((tensorRight L.obj) ⋙ (DerivedCategory.Q (C := D)))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)).inv) ≫
          (Functor.whiskerRight (Functor.whiskerRight (ObjectProperty.ιOfLECompιIso hle).inv
              ((tensorRight L.obj) ⋙ (DerivedCategory.Q (C := D))))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
          (Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
              (kFlatComplexesLeft (curriedTensor D)).ι ((tensorRight L.obj) ⋙
              (DerivedCategory.Q (C := D)))).hom
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory))) ≫
      ((Functor.whiskerRight (Functor.whiskerLeft (ObjectProperty.ιOfLE hle)
          (derivedTensorFirstIso D hresD L.obj L.property).inv)
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory))) ≫
      ((Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
          ((kFlatComplexesLeft (curriedTensor D)).ι ⋙ (DerivedCategory.Q (C := D)))
          (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L))).inv
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
          (Functor.whiskerRight (Functor.whiskerRight (Functor.associator (ObjectProperty.ιOfLE hle)
              (kFlatComplexesLeft (curriedTensor D)).ι (DerivedCategory.Q (C := D))).inv
              (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L)))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
          (Functor.whiskerRight (Functor.whiskerRight (Functor.whiskerRight
              (ObjectProperty.ιOfLECompιIso hle).hom (DerivedCategory.Q (C := D)))
              (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L)))
              ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)) ≫
          ((Functor.associator ((kFlatComplexes (curriedTensor D)).ι ⋙ (DerivedCategory.Q (C := D)))
              (tensorRight ((kFlatComplexQ (curriedTensor D)).obj L))
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
  let := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  have := derivedTensorFirstIso_commShift (J ⥤ D) hresJD
    (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)
    (kFlat_constMapHomologicalComplex L.obj L.property)
  have := derivedTensorFirstIso_commShift D hresD L.obj L.property
  have : NatTrans.CommShift ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
        ((kFlatComplexes (curriedTensor D)).ι ⋙
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
        (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).hom
            ℤ :=
    Functor.CommShift.ofComp_compatibility _ ℤ
  have : NatTrans.CommShift (ObjectProperty.ιOfLECompιIso hle).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ ℤ
  have := Functor.commShift_μNatTransFst_mapHomologicalComplex
    (Functor.const J : D ⥤ (J ⥤ D)) L.obj
  ext K
  have hiso : (derivedTensorFirstIso D hresD L.obj L.property).app
        ((ObjectProperty.ιOfLE hle).obj K) =
      derivedTensorIso D hresD K.property L.property :=
    Iso.ext (derivedTensorFirstIso_hom_app D hresD K.property L.property)
  exact chainCongr (idFst1 hresD hresJD hle L K) (idFst2 hresD hresJD hle L K)
    (idFst3 hresD hresJD hle L K) (idFst4 hresD hresJD hle L K) (idFst5 hresD hresJD hle L K)
    (idFst6 hresD hresJD hle L K)
    (derivedTensorFirstIso_hom_app (J ⥤ D) hresJD
      (kFlat_constMapHomologicalComplex K.obj K.property)
      (kFlat_constMapHomologicalComplex L.obj L.property))
    (congrArg ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map (congrArg Iso.inv hiso))
    (Functor.mu_constMapDerivedCategory_eq hresD hresJD K.property L.property)

include hresD hresJD in
/-- **The tensorator of the derived constant diagram, read in the first variable at the image of a
K-flat complex, commutes with the shift.** -/
theorem commShift_muNatTransFst_constMapDerivedCategory_kFlat
    (hle : kFlatComplexes (curriedTensor D) ≤ kFlatComplexesLeft (curriedTensor D))
    (L : (kFlatComplexes (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    letI := fun K : DerivedCategory D => derivedMonoidal_tensorLeft_commShift D hresD K
    letI := fun M : DerivedCategory D => derivedMonoidal_tensorRight_commShift D hresD M
    letI := fun K : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorLeft_commShift (J ⥤ D) hresJD K
    letI := fun M : DerivedCategory (J ⥤ D) =>
      derivedMonoidal_tensorRight_commShift (J ⥤ D) hresJD M
    letI := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
    letI : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
      Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
    NatTrans.CommShift ((kFlatComplexQ (curriedTensor D)).whiskerLeft
      (Functor.LaxMonoidal.μNatTransFst
        ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
        ((kFlatComplexQ (curriedTensor D)).obj L))) ℤ := by
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
  let := Functor.constKFlatComplexLiftLeft_commShift (J := J) (D := D)
  let : (ObjectProperty.ιOfLE hle).CommShift ℤ :=
    Functor.CommShift.ofComp (ObjectProperty.ιOfLECompιIso hle) ℤ
  have := derivedTensorFirstIso_commShift (J ⥤ D) hresJD
    (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)
    (kFlat_constMapHomologicalComplex L.obj L.property)
  have := derivedTensorFirstIso_commShift D hresD L.obj L.property
  have : NatTrans.CommShift ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
        ((kFlatComplexes (curriedTensor D)).ι ⋙
        ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)))
        (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))).hom
            ℤ :=
    Functor.CommShift.ofComp_compatibility _ ℤ
  have : NatTrans.CommShift (ObjectProperty.ιOfLECompιIso hle).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ ℤ
  have := Functor.commShift_μNatTransFst_mapHomologicalComplex
    (Functor.const J : D ⥤ (J ⥤ D)) L.obj
  have := hchainFst hresD hresJD hle L
  exact NatTrans.commShift_of_eq (keyFst hresD hresJD hle L)

end CategoryTheory

end
