module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorCommShiftTwo
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ToOrdinaryTensor

/-!
# The canonical map to the total tensor complex commutes with the shifts

Let `(C, O)` be a ringed site and `K` a complex of `O`-modules.  The canonical map
`K ⊗^L L ⟶ Tot(K ⊗ L)` of Stacks 0FPH (`Stacks.SheafOfModules.toTensor`), natural in the complex
`L`, commutes with the shifts in `L`: the commutation of `K ⊗^L -` with the shift is the one
carried by the two-variable shift coherence of the canonical derived tensor product, and that of
`Tot(K ⊗ -)` the sign-twisted one of Mathlib.

For a K-flat `K` this is the defining property of that coherence (it is descended from
`Tot(K ⊗ -)` along the localizations); in general `toTensor` is the K-flat comparison of a K-flat
resolution `P ⟶ K` followed by `Tot(P ⊗ -) ⟶ Tot(K ⊗ -)`, both of which commute with the shifts.

## Main definitions

* `Stacks.SheafOfModules.kFlatComparisonNatTrans`: the K-flat comparison, as a natural
  transformation in the second variable.
* `Stacks.SheafOfModules.toTensorNatTrans`: `toTensor K -`, as a natural transformation.

## Main results

* `Stacks.SheafOfModules.kFlatComparisonNatTrans_commShift`,
  `Stacks.SheafOfModules.toTensorNatTrans_commShift`: they commute with the shifts.
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

attribute [local instance] derivedTensorBifunctorLifting
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.tensorComplex

/-- The K-flat comparison `Q K ⊗^L Q L ≅ Q Tot(K ⊗ L)` at a K-flat `K`, as a natural
transformation in `L`. -/
def kFlatComparisonNatTrans
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) :
    DerivedCategory.Q ⋙ (derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A) ⟶
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q where
  app L := (kFlatComparison X A hA L).hom
  naturality {L L'} g := by
    simpa using kFlatComparison_naturality X hA hA (𝟙 A) g

/-- **The K-flat comparison commutes with the shifts in the second variable.**  This is the
formula for the descended commutation isomorphism over the images of the two localizations,
`CategoryTheory.Localization.objCommShift_commShiftIso_hom_app_app`. -/
instance kFlatComparisonNatTrans_commShift
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) :
    NatTrans.CommShift (kFlatComparisonNatTrans X A hA) ℤ := ⟨fun n => by
  ext L
  have h := Localization.objCommShift_commShiftIso_hom_app_app (kFlatComplexQ X)
    DerivedCategory.Q (kFlatComplexQuasiIso X)
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) (kFlatTensorToDerived X)
    (derivedTensorBifunctor X) (kFlatObj X A hA) L n
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.commShiftIso_comp_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  let I := Localization.Lifting₂.iso (kFlatComplexQ X) DerivedCategory.Q
    (kFlatComplexQuasiIso X) (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (kFlatTensorToDerived X) (derivedTensorBifunctor X)
  have hF : (Functor.commShiftIso ((kFlatTensorToDerived X).obj (kFlatObj X A hA)) n).hom.app L =
      DerivedCategory.Q.map ((Functor.commShiftIso
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A) n).hom.app L) ≫
        (Functor.commShiftIso DerivedCategory.Q n).hom.app _ :=
    Functor.commShiftIso_comp_hom_app ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A)
      DerivedCategory.Q n L
  have h' : (Functor.commShiftIso
      ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)) n).hom.app
      (DerivedCategory.Q.obj L) =
      ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)).map
          ((Functor.commShiftIso DerivedCategory.Q n).inv.app L) ≫
        (kFlatComparisonNatTrans X A hA).app (L⟦n⟧) ≫
        (DerivedCategory.Q.map ((Functor.commShiftIso
          ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A) n).hom.app L) ≫
          (Functor.commShiftIso DerivedCategory.Q n).hom.app _) ≫
        (shiftFunctor _ n).map ((I.inv.app (kFlatObj X A hA)).app L) := by
    rwa [← hF]
  have hinv : (I.inv.app (kFlatObj X A hA)).app L ≫ (kFlatComparisonNatTrans X A hA).app L =
      𝟙 _ :=
    NatTrans.congr_app (Iso.inv_hom_id_app I (kFlatObj X A hA)) L
  have hc : ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)).map
        ((Functor.commShiftIso DerivedCategory.Q n).hom.app L) ≫
      ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)).map
        ((Functor.commShiftIso DerivedCategory.Q n).inv.app L) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have hs : (shiftFunctor (DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).map ((I.inv.app (kFlatObj X A hA)).app L) ≫
      (shiftFunctor _ n).map ((kFlatComparisonNatTrans X A hA).app L) = 𝟙 _ := by
    rw [← Functor.map_comp, hinv, CategoryTheory.Functor.map_id]
  rw [h']
  simp only [Category.assoc]
  rw [reassoc_of% hc, hs]
  exact congrArg _ (congrArg _ (Category.comp_id _))⟩

/-- The canonical map `Q K ⊗^L Q L ⟶ Q Tot(K ⊗ L)` of Stacks 0FPH, as a natural transformation
in `L`. -/
def toTensorNatTrans
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q ⋙ (derivedTensorBifunctor X).obj (DerivedCategory.Q.obj K) ⟶
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K ⋙ DerivedCategory.Q where
  app L := toTensor X K L
  naturality {L L'} g := by
    simpa using toTensor_naturality X (𝟙 K) g

/-- `Q P ⊗^L - ≅ Q K ⊗^L -` along the chosen K-flat resolution `P ⟶ K`. -/
def kFlatResTensorIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q ⋙ (derivedTensorBifunctor X).obj (DerivedCategory.Q.obj (kFlatRes X K)) ≅
      DerivedCategory.Q ⋙ (derivedTensorBifunctor X).obj (DerivedCategory.Q.obj K) :=
  NatIso.ofComponents
    (fun L => asIso (((derivedTensorBifunctor X).map
      (DerivedCategory.Q.map (kFlatResMap X K))).app (DerivedCategory.Q.obj L)))
    (fun g => ((derivedTensorBifunctor X).map
      (DerivedCategory.Q.map (kFlatResMap X K))).naturality (DerivedCategory.Q.map g))

/-- `Q P ⊗^L - ⟶ Q K ⊗^L -` commutes with the shifts: it is whiskered from a morphism of
bifunctors. -/
instance (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    NatTrans.CommShift (kFlatResTensorIso X K).hom ℤ := by
  have : (kFlatResTensorIso X K).hom = Functor.whiskerLeft DerivedCategory.Q
      ((derivedTensorBifunctor X).map (DerivedCategory.Q.map (kFlatResMap X K))) := by
    ext L
    rfl
  rw [this]
  infer_instance

/-- The inverse `Q K ⊗^L - ⟶ Q P ⊗^L -` commutes with the shifts. -/
instance (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    NatTrans.CommShift (kFlatResTensorIso X K).inv ℤ :=
  NatTrans.CommShift.of_iso_inv _ _

/-- `toTensor` through the chosen K-flat resolution `P ⟶ K`. -/
theorem toTensorNatTrans_eq
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    toTensorNatTrans X K =
      (kFlatResTensorIso X K).inv ≫
        kFlatComparisonNatTrans X (kFlatRes X K) (isKFlat_kFlatRes X K) ≫
        Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map
          (kFlatResMap X K)) DerivedCategory.Q := by
  ext L
  rfl

/-- **`toTensor K -` commutes with the shifts.** -/
instance toTensorNatTrans_commShift
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    NatTrans.CommShift (toTensorNatTrans X K) ℤ := by
  rw [toTensorNatTrans_eq]
  infer_instance

end Stacks.SheafOfModules

end
