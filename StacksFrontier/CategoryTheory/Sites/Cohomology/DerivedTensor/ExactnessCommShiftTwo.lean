module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorCommShiftTwo
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoLocalization
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExactnessQuotientIso

/-!
# Exactness of the derived tensor product on K-flat models, at the canonical shift structure

For a K-flat complex `A`, the identification of `A ⊗^L_O -` with the descent of `Tot(A ⊗_O -)`
commutes with the shift carried by `Stacks.SheafOfModules.derivedTensorBifunctor_commShift₂Int`,
and likewise in the other variable; hence `A ⊗^L_O -` and `- ⊗^L_O B` are exact there
(Stacks 06YM, 05R7).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u d

namespace CategoryTheory.Localization

variable {C₁ C₂ D₁ D₂ E : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  [Category E] {M : Type*} [AddMonoid M] [HasShift C₂ M] [HasShift D₂ M] [HasShift E M]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₂.CommShift M]
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ F F']
  [∀ X₁ : C₁, (F.obj X₁).CommShift M]
  [∀ (X₁ Y₁ : C₁) (f : X₁ ⟶ Y₁), NatTrans.CommShift (F.map f) M]

/-- The isomorphism `L₂ ⋙ F'.obj (L₁.obj X₁) ≅ F.obj X₁` of a lifting commutes with the shift,
for the commutation of `F'.obj (L₁.obj X₁)` with the shift of
`CategoryTheory.Localization.objCommShift`. -/
theorem objCommShift_fst_iso_hom (X₁ : C₁) :
    letI : (F'.obj (L₁.obj X₁)).CommShift M :=
      objCommShift L₁ L₂ W₁ W₂ F F' (L₁.obj X₁)
    letI := Lifting₂.fst L₁ L₂ W₁ W₂ F F' X₁
    NatTrans.CommShift
      (Lifting.iso L₂ W₂ (F.obj X₁) (F'.obj (L₁.obj X₁))).hom M := by
  let : (F'.obj (L₁.obj X₁)).CommShift M :=
    objCommShift L₁ L₂ W₁ W₂ F F' (L₁.obj X₁)
  let := Lifting₂.fst L₁ L₂ W₁ W₂ F F' X₁
  refine ⟨fun a ↦ ?_⟩
  ext X₂
  have e : ∀ Y₂, (Lifting.iso L₂ W₂ (F.obj X₁) (F'.obj (L₁.obj X₁))).hom.app Y₂ =
      ((Lifting₂.iso L₁ L₂ W₁ W₂ F F').hom.app X₁).app Y₂ := fun _ ↦ rfl
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, objCommShift_commShiftIso_hom_app_app, e]
  simp [← Functor.map_comp_assoc, ← Functor.map_comp]

end CategoryTheory.Localization

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))]

attribute [local instance] kFlatQ_isLocalization derivedTensorBifunctorLifting
  kFlatQuasiIso_hasLeftCalculusOfFractions kFlatQ_mapArrow_essSurj

/-- For a K-flat complex `A`, the identification of `Qh ⋙ (A ⊗^L_O -)` with the class of
`Tot(A ⊗_O -)` commutes with the shift, for the commutation of `A ⊗^L_O -` with the shift
descended from the total tensor product of complexes. -/
theorem derivedTensorObjLifting_commShift
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) :
    letI := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A
    NatTrans.CommShift (derivedTensorObjLiftingIso X A hA).hom ℤ := by
  let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A
  have : NatTrans.CommShift (derivedTensorObjQuotientIso X A hA).hom ℤ := by
    have := Localization.objCommShift_fst_iso_hom (M := ℤ) (kFlatComplexQ X)
      DerivedCategory.Q
      (kFlatComplexQuasiIso X)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (kFlatTensorToDerived X) (derivedTensorBifunctor X) (kFlatObj X A hA)
    let := Localization.Lifting₂.fst (kFlatComplexQ X) DerivedCategory.Q
      (kFlatComplexQuasiIso X)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (kFlatTensorToDerived X) (derivedTensorBifunctor X) (kFlatObj X A hA)
    exact (inferInstance : NatTrans.CommShift ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).hom
        ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)) ≫
      (Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
        ((kFlatTensorToDerived X).obj (kFlatObj X A hA))
        ((derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj (kFlatObj X A hA)))).hom) ℤ)
  have : NatTrans.CommShift (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A).hom ℤ := by
    have := Stacks.SheafOfModules.Tensor.Reduction.map₂HomologicalComplex_obj_additive
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A
    exact Quotient.liftCommShift_compatibility _ _ _ _
  have : NatTrans.CommShift (bifunctorPhiQuotientIso X A).hom ℤ :=
    (inferInstance : NatTrans.CommShift ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A).hom DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj A)
        (DerivedCategory.quotientCompQhIso _).hom) ℤ)
  refine NatTrans.commShift_of_whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) _ ?_
  refine NatTrans.commShift_of_eq (θ := (derivedTensorObjQuotientIso X A hA).hom ≫
    (bifunctorPhiQuotientIso X A).inv) ?_
  ext K
  simp [derivedTensorObjLiftingIso]

/-- **Exactness in the second variable, for a K-flat first factor**, for the commutation of
`A ⊗^L_O -` with the shift descended from the total tensor product of complexes. -/
theorem isTriangulated_derivedTensorBifunctor_obj_kFlat
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) :
    ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)).IsTriangulated := by
  let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A
  have := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A
  have := derivedTensorObjLifting_commShift X A hA
  exact Functor.isTriangulated_of_precomp_iso (derivedTensorObjLiftingIso X A hA)

/-- For a complex `B`, the identification of `kFlatQ ⋙ (- ⊗^L_O B)` with the descent of
`Tot(- ⊗_O B)` commutes with the shift, for the commutation of `- ⊗^L_O B` with the shift
descended from the total tensor product of complexes. -/
theorem derivedTensorFlipObjLifting_commShift
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    letI := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
    NatTrans.CommShift (derivedTensorFlipObjLiftingIso X B).hom ℤ := by
  let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
  -- The instances of Mathlib for `ObjectProperty.lift` are not found by instance search here:
  -- unifying their membership hypothesis would unfold `ObjectProperty.inverseImage`.
  let : (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O)).CommShift ℤ :=
    ObjectProperty.instCommShiftFullSubcategoryLift _ _ _
  have : NatTrans.CommShift (ObjectProperty.liftCompιIso (kFlatObjects.{c, u, u} X.O)
      ((kFlatComplexes X).ι ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (fun K ↦ K.2)).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  have : NatTrans.CommShift
      (ObjectProperty.complexSubcategoryQuotientCompIso (kFlatObjects.{c, u, u} X.O)).hom ℤ :=
    (inferInstance : NatTrans.CommShift ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (ObjectProperty.liftCompιIso (kFlatObjects.{c, u, u} X.O) _ _).hom
        DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (kFlatComplexes X).ι (DerivedCategory.quotientCompQhIso _).hom) ℤ)
  have : NatTrans.CommShift (derivedTensorFlipObjQuotientIso X B).hom ℤ := by
    have := Localization.objCommShift_fst_iso_hom (M := ℤ) DerivedCategory.Q
      (kFlatComplexQ X)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (kFlatComplexQuasiIso X) (kFlatTensorToDerived X).flip (derivedTensorBifunctor X).flip B
    let := Localization.Lifting₂.snd (kFlatComplexQ X) DerivedCategory.Q
      (kFlatComplexQuasiIso X)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (kFlatTensorToDerived X) (derivedTensorBifunctor X) B
    exact (inferInstance : NatTrans.CommShift ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (ObjectProperty.complexSubcategoryQuotientCompIso (kFlatObjects.{c, u, u} X.O)).hom
        ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)) ≫
      (Localization.Lifting.iso (kFlatComplexQ X) (kFlatComplexQuasiIso X)
        ((kFlatTensorToDerived X).flip.obj B)
        ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))).hom) ℤ)
  have : NatTrans.CommShift (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B).hom ℤ := by
    have := Stacks.SheafOfModules.Tensor.Reduction.map₂HomologicalComplex_flip_obj_additive
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
    exact Quotient.liftCommShift_compatibility _ _ _ _
  have : NatTrans.CommShift (bifunctorPhiRQuotientIso X B).hom ℤ :=
    (inferInstance : NatTrans.CommShift ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (ObjectProperty.liftCompιIso (kFlatObjects.{c, u, u} X.O) _ _).hom
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (kFlatComplexes X).ι ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B).hom DerivedCategory.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj B)
          (DerivedCategory.quotientCompQhIso _).hom)) ℤ)
  refine NatTrans.commShift_of_whiskerLeft
    (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O)) _ ?_
  refine NatTrans.commShift_of_eq (θ := (derivedTensorFlipObjQuotientIso X B).hom ≫
    (bifunctorPhiRQuotientIso X B).inv) ?_
  ext K
  simp [derivedTensorFlipObjLiftingIso]

/-- **Exactness in the first variable, for a complex as second factor**, for the commutation of
`- ⊗^L_O B` with the shift descended from the total tensor product of complexes. -/
theorem isTriangulated_derivedTensorBifunctor_flip_obj_complex
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)).IsTriangulated := by
  let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
  have := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
  have := derivedTensorFlipObjLifting_commShift X B
  exact Functor.isTriangulated_of_precomp_iso (derivedTensorFlipObjLiftingIso X B)

end Stacks.SheafOfModules

end
