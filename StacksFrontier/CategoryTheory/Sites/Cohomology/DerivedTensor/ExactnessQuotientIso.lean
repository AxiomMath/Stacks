module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Assembly
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Exactness

/-!
# The derived tensor product with a fixed object, through K-flat lifts

For a fixed object of `D(O)`, the derived tensor product with it, and with it in the second
variable, is identified with the functor induced by the tensor complex with a K-flat
representative, through the quotient of the homotopy category.

## Main definitions

* `Stacks.SheafOfModules.derivedTensorObjLiftingIso`: for a K-flat complex `A`, the functor
  `A ⊗^L_O -` restricted along `DerivedCategory.Qh` is the descent of `Tot(A ⊗_O -)` to the
  homotopy category followed by `DerivedCategory.Qh`.
* `Stacks.SheafOfModules.derivedTensorFlipObjLiftingIso`: for a complex `B`, the functor
  `- ⊗^L_O B` restricted along `Stacks.SheafOfModules.kFlatQ` is the descent of `Tot(- ⊗_O B)` to
  the homotopy category, on K-flat objects, followed by `DerivedCategory.Qh`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u d

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

/-- For a K-flat complex `A`, the functor `A ⊗^L_O -` restricted along the homotopy quotient and
`DerivedCategory.Qh` is the class of `Tot(A ⊗_O -)` in the derived category. -/
def derivedTensorObjQuotientIso
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh ⋙ (derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)) ≅
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q :=
  letI := Localization.Lifting₂.fst (kFlatComplexQ X) DerivedCategory.Q
    (kFlatComplexQuasiIso X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (kFlatTensorToDerived X) (derivedTensorBifunctor X) (kFlatObj X A hA)
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
      ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)) ≪≫
    Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      ((kFlatTensorToDerived X).obj (kFlatObj X A hA))
      ((derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj (kFlatObj X A hA)))

/-- The descent `Φ_A` of `Tot(A ⊗_O -)` to the homotopy category, restricted along the homotopy
quotient and followed by `DerivedCategory.Qh`, is the class of `Tot(A ⊗_O -)`. -/
def bifunctorPhiQuotientIso
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A ⋙ DerivedCategory.Qh) ≅
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A)
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj A)
      (DerivedCategory.quotientCompQhIso _)

/-- For a K-flat complex `A`, the functor `A ⊗^L_O -` on the derived category, restricted along
`DerivedCategory.Qh`, is the descent `Φ_A` of `Tot(A ⊗_O -)` to the homotopy category, followed by
`DerivedCategory.Qh`. -/
def derivedTensorObjLiftingIso
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) :
    DerivedCategory.Qh ⋙ (derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A) ≅
      Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A ⋙ DerivedCategory.Qh :=
  letI : Localization.Lifting (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℤ))
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q)
      (DerivedCategory.Qh ⋙ (derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)) :=
    ⟨derivedTensorObjQuotientIso X A hA⟩
  letI : Localization.Lifting (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℤ))
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q)
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A ⋙ DerivedCategory.Qh) :=
    ⟨bifunctorPhiQuotientIso X A⟩
  Localization.liftNatIso (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℤ))
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q)
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q) _ _ (Iso.refl _)
      |>.symm

attribute [local instance] kFlatQuasiIso_hasLeftCalculusOfFractions

attribute [local instance] kFlatQ_mapArrow_essSurj

/-- For a complex `B`, the functor `- ⊗^L_O B` restricted along the K-flat complexes is the class
of `Tot(- ⊗_O B)` in the derived category, presented through the K-flat objects of the homotopy
category. -/
def derivedTensorFlipObjQuotientIso
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O) ⋙
        (kFlatQ.{c, u, d} X ⋙ (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)) ≅
      (kFlatTensorToDerived X).flip.obj B :=
  letI := Localization.Lifting₂.snd (kFlatComplexQ X) DerivedCategory.Q
    (kFlatComplexQuasiIso X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (kFlatTensorToDerived X) (derivedTensorBifunctor X) B
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ObjectProperty.complexSubcategoryQuotientCompIso (kFlatObjects.{c, u, u} X.O))
      ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)) ≪≫
    Localization.Lifting.iso (kFlatComplexQ X) (kFlatComplexQuasiIso X)
      ((kFlatTensorToDerived X).flip.obj B)
      ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))

/-- The descent `Φ^R_B` of `Tot(- ⊗_O B)` to the homotopy category, on K-flat objects, restricted
along the K-flat complexes and followed by `DerivedCategory.Qh`, is the class of
`Tot(- ⊗_O B)`. -/
def bifunctorPhiRQuotientIso
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O) ⋙
        ((kFlatObjects.{c, u, u} X.O).ι ⋙
          Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh) ≅
      (kFlatTensorToDerived X).flip.obj B :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ObjectProperty.liftCompιIso (kFlatObjects.{c, u, u} X.O) _ _)
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (kFlatComplexes X).ι
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B) DerivedCategory.Qh ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj B)
          (DerivedCategory.quotientCompQhIso _))

/-- For a complex `B`, the functor `- ⊗^L_O B` on the derived category, restricted along
`Stacks.SheafOfModules.kFlatQ`, is the descent `Φ^R_B` of `Tot(- ⊗_O B)` to the homotopy
category, on K-flat objects, followed by `DerivedCategory.Qh`. -/
def derivedTensorFlipObjLiftingIso
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    kFlatQ.{c, u, d} X ⋙ (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B) ≅
      (kFlatObjects.{c, u, u} X.O).ι ⋙
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh :=
  letI : Localization.Lifting
      (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
      ((HomologicalComplex.homotopyEquivalences
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
      ((kFlatTensorToDerived X).flip.obj B)
      (kFlatQ.{c, u, d} X ⋙ (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)) :=
    ⟨derivedTensorFlipObjQuotientIso X B⟩
  letI : Localization.Lifting
      (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
      ((HomologicalComplex.homotopyEquivalences
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
      ((kFlatTensorToDerived X).flip.obj B)
      ((kFlatObjects.{c, u, u} X.O).ι ⋙
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
          DerivedCategory.Qh) :=
    ⟨bifunctorPhiRQuotientIso X B⟩
  Localization.liftNatIso
    (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
    ((HomologicalComplex.homotopyEquivalences
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
    ((kFlatTensorToDerived X).flip.obj B) ((kFlatTensorToDerived X).flip.obj B)
    _ _ (Iso.refl _) |>.symm

end Stacks.SheafOfModules

end
