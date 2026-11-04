module

public import Mathlib.CategoryTheory.Localization.Predicate
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Homology.KFlat.BifunctorSingleShift

/-!
# Tensoring with a shifted structure sheaf is a shift

Let `(C, 𝒪)` be a ringed site and `T` a derived tensor product on it in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct`. For `q : ℤ` the structure sheaf placed in degree
`q` is K-flat, and tensoring with it, on either side, is the shift by `-q`:

`- ⊗^L_𝒪 𝒪[-q] ≅ (-)⟦-q⟧` and `𝒪[-q] ⊗^L_𝒪 - ≅ (-)⟦-q⟧`

as natural isomorphisms of functors on `D(𝒪)`. In particular both functors are
autoequivalences of `D(𝒪)`.

## Main definitions

* `Stacks.SheafOfModules.tensorComplexSingleUnitIso`: `Tot(K ⊗ 𝒪[q]) ≅ K⟦-q⟧`.
* `Stacks.SheafOfModules.singleUnitTensorComplexIso`: `Tot(𝒪[q] ⊗ K) ≅ K⟦-q⟧`.
* `Stacks.SheafOfModules.DerivedTensorProduct.rightSingleUnitNatIso`
* `Stacks.SheafOfModules.DerivedTensorProduct.leftSingleUnitNatIso`

## Main results

* `CochainComplex.KFlatBifunctor.totalSingleShiftIso_hom_naturality`: the identification
  `CochainComplex.KFlatBifunctor.totalSingleShiftIso` is natural in the first complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- `CochainComplex.KFlatBifunctor.totalSingleShiftIso` is natural in the first complex. -/
lemma totalSingleShiftIso_hom_naturality {K K' : CochainComplex A ℤ} (f : K ⟶ K') (M : B)
    (q : ℤ) :
    HomologicalComplex.mapBifunctorMap f
          (𝟙 ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M)) F
          (ComplexShape.up ℤ) ≫
        (totalSingleShiftIso F K' M q).hom =
      (totalSingleShiftIso F K M q).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex D ℤ) (-q)).map (rowComplexMap F f M) := by
  let _hT : (StacksDraft.TotalSingleRow.singleRow (rowComplex F K M) q).HasTotal
      (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (mapBifunctorSingleIso F K M q) _
  let _hT' : (StacksDraft.TotalSingleRow.singleRow (rowComplex F K' M) q).HasTotal
      (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (mapBifunctorSingleIso F K' M q) _
  have : IsIso (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M) q) :=
    StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit _ _
  have : IsIso (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K' M) q) :=
    StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit _ _
  have hK : (totalSingleShiftIso F K M q).hom =
      HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M q).hom (ComplexShape.up ℤ) ≫
        CategoryTheory.inv
            (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M) q) := rfl
  have hK' : (totalSingleShiftIso F K' M q).hom =
      HomologicalComplex₂.total.map (mapBifunctorSingleIso F K' M q).hom (ComplexShape.up ℤ) ≫
        CategoryTheory.inv
            (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K' M) q) := rfl
  have hid : ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map f).app
          ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M) ≫
        ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj K').map
          (𝟙 ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M)) =
      ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).app
        ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M) := by
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h0 : HomologicalComplex.mapBifunctorMap f
        (𝟙 ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M)) F
        (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map
        (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).map f).app
          ((HomologicalComplex.single B (ComplexShape.up ℤ) q).obj M))
        (ComplexShape.up ℤ) :=
    congrArg (fun m ↦ HomologicalComplex₂.total.map m (ComplexShape.up ℤ)) hid
  have h1 : HomologicalComplex₂.total.map
          (((HomologicalComplex.single D (ComplexShape.up ℤ) q).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (rowComplexMap F f M)) (ComplexShape.up ℤ) ≫
        CategoryTheory.inv
          (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K' M) q) =
      CategoryTheory.inv
          (StacksDraft.TotalSingleRow.totalSingleRowUnit (rowComplex F K M) q) ≫
        (CategoryTheory.shiftFunctor (CochainComplex D ℤ) (-q)).map
          (rowComplexMap F f M) := by
    rw [IsIso.comp_inv_eq, Category.assoc,
      StacksDraft.TotalSingleRow.totalSingleRowUnit_naturality (rowComplexMap F f M) q,
      IsIso.inv_hom_id_assoc]
  rw [h0, hK, hK', ← Category.assoc, ← HomologicalComplex₂.total.map_comp,
    mapBifunctorSingleIso_naturality F f M q, HomologicalComplex₂.total.map_comp,
    Category.assoc, h1, Category.assoc]

end CochainComplex.KFlatBifunctor

namespace Stacks.SheafOfModules

open CochainComplex.KFlatBifunctor

section Complexes

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (S : Sheaf J CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor S).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor S).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor S)
      (ComplexShape.up ℤ)]

/-- The structure sheaf placed in degree `q`, as a complex. -/
abbrev singleUnitComplex (q : ℤ) :
    CochainComplex (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S))

/-- **The structure sheaf placed in any degree is a K-flat complex.** -/
theorem isKFlat_singleUnitComplex (q : ℤ) : IsKFlat S (singleUnitComplex S q) :=
  kFlat_single_of_exact (Stacks.SheafOfModules.Tensor.sheafTensor S) _ q
    (fun G hG n =>
      HomologicalComplex.ExactAt.of_iso (hG n) (rowComplexUnitIsoFreeSections S G).symm)

/-- **`Tot(K ⊗_𝒪 𝒪[q]) ≅ K⟦-q⟧`.** -/
def tensorComplexSingleUnitIso
    (K : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ) (q : ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex S).obj K).obj (singleUnitComplex S q) ≅
      (CategoryTheory.shiftFunctor _ (-q)).obj K :=
  totalSingleShiftIso (Stacks.SheafOfModules.Tensor.sheafTensor S) K
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S)) q ≪≫
    (CategoryTheory.shiftFunctor _ (-q)).mapIso (rowComplexUnitIsoFreeSections S K)

/-- `Stacks.SheafOfModules.tensorComplexSingleUnitIso` is natural in the complex. -/
lemma tensorComplexSingleUnitIso_naturality
    {K K' : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ} (φ : K ⟶ K') (q : ℤ) :
    HomologicalComplex.mapBifunctorMap φ (𝟙 (singleUnitComplex S q))
        (Stacks.SheafOfModules.Tensor.sheafTensor S) (ComplexShape.up ℤ) ≫
        (tensorComplexSingleUnitIso S K' q).hom =
      (tensorComplexSingleUnitIso S K q).hom ≫ (CategoryTheory.shiftFunctor _ (-q)).map φ := by
  show _ ≫ (totalSingleShiftIso _ K' _ q).hom ≫
      (CategoryTheory.shiftFunctor _ (-q)).map (rowComplexUnitIsoFreeSections S K').hom =
    ((totalSingleShiftIso _ K _ q).hom ≫
      (CategoryTheory.shiftFunctor _ (-q)).map (rowComplexUnitIsoFreeSections S K).hom) ≫
      (CategoryTheory.shiftFunctor _ (-q)).map φ
  rw [← Category.assoc, totalSingleShiftIso_hom_naturality, Category.assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact (NatIso.mapHomologicalComplex (sheafTensorUnitNatIsoFreeSections S)
      (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.naturality φ

/-- The left unit law `𝒪 ⊗_𝒪 M ≅ M` of sheaves of modules, with the sections universe free. -/
def sheafTensorLeftUnitNatIsoFreeSections :
    (Stacks.SheafOfModules.Tensor.sheafTensor S).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S)) ≅
      𝟭 (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S)) :=
  (Stacks.SheafOfModules.Tensor.sheafTensorBraiding S).app _ ≪≫
    sheafTensorUnitNatIsoFreeSections S

/-- The termwise complex `p ↦ 𝒪 ⊗_𝒪 K^p` is `K`. -/
def rowComplexLeftUnitIsoFreeSections
    (K : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ) :
    rowComplex (Stacks.SheafOfModules.Tensor.sheafTensor S).flip K
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S)) ≅ K :=
  (NatIso.mapHomologicalComplex (sheafTensorLeftUnitNatIsoFreeSections S)
      (ComplexShape.up ℤ)).app K ≪≫
    (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app K

/-- **`Tot(𝒪[q] ⊗_𝒪 K) ≅ K⟦-q⟧`.** -/
def singleUnitTensorComplexIso
    (K : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ) (q : ℤ) :
    HomologicalComplex.mapBifunctor (singleUnitComplex S q) K
        (Stacks.SheafOfModules.Tensor.sheafTensor S) (ComplexShape.up ℤ) ≅
      (CategoryTheory.shiftFunctor _ (-q)).obj K :=
  (HomologicalComplex.mapBifunctorFlipIso (singleUnitComplex S q) K
      (Stacks.SheafOfModules.Tensor.sheafTensor S) (ComplexShape.up ℤ)).symm ≪≫
    totalSingleShiftIso (Stacks.SheafOfModules.Tensor.sheafTensor S).flip K
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S)) q ≪≫
    (CategoryTheory.shiftFunctor _ (-q)).mapIso (rowComplexLeftUnitIsoFreeSections S K)

/-- `Stacks.SheafOfModules.singleUnitTensorComplexIso` is natural in the complex. -/
lemma singleUnitTensorComplexIso_naturality
    {K K' : CochainComplex (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf S)) ℤ} (φ : K ⟶ K') (q : ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 (singleUnitComplex S q)) φ
        (Stacks.SheafOfModules.Tensor.sheafTensor S) (ComplexShape.up ℤ) ≫
        (singleUnitTensorComplexIso S K' q).hom =
      (singleUnitTensorComplexIso S K q).hom ≫ (CategoryTheory.shiftFunctor _ (-q)).map φ := by
  have hflip := HomologicalComplex.mapBifunctorFlipIso_hom_naturality
    (𝟙 (singleUnitComplex S q)) φ (Stacks.SheafOfModules.Tensor.sheafTensor S)
    (ComplexShape.up ℤ)
  have h' : HomologicalComplex.mapBifunctorMap (𝟙 (singleUnitComplex S q)) φ
        (Stacks.SheafOfModules.Tensor.sheafTensor S) (ComplexShape.up ℤ) ≫
        (HomologicalComplex.mapBifunctorFlipIso (singleUnitComplex S q) K'
          (Stacks.SheafOfModules.Tensor.sheafTensor S) (ComplexShape.up ℤ)).inv =
      (HomologicalComplex.mapBifunctorFlipIso (singleUnitComplex S q) K
          (Stacks.SheafOfModules.Tensor.sheafTensor S) (ComplexShape.up ℤ)).inv ≫
        HomologicalComplex.mapBifunctorMap φ (𝟙 (singleUnitComplex S q))
          (Stacks.SheafOfModules.Tensor.sheafTensor S).flip (ComplexShape.up ℤ) := by
    rw [Iso.comp_inv_eq, Category.assoc, hflip, Iso.inv_hom_id_assoc]
  have hrow : rowComplexMap (Stacks.SheafOfModules.Tensor.sheafTensor S).flip φ
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S)) ≫
        (rowComplexLeftUnitIsoFreeSections S K').hom =
      (rowComplexLeftUnitIsoFreeSections S K).hom ≫ φ :=
    (NatIso.mapHomologicalComplex (sheafTensorLeftUnitNatIsoFreeSections S)
      (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.naturality φ
  simp only [singleUnitTensorComplexIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [reassoc_of% h', reassoc_of% totalSingleShiftIso_hom_naturality, ← Functor.map_comp,
    hrow, Functor.map_comp]

end Complexes

namespace DerivedTensorProduct

open AlgebraicGeometry.RingedSite

variable {X : AlgebraicGeometry.RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : DerivedTensorProduct.{u, v, w, d} X)

/-- `- ⊗^L 𝒪[q] ≅ (-)⟦-q⟧` on the images of complexes, naturally in the complex. -/
def rightSingleUnitComparisonNatIso (q : ℤ) :
    DerivedCategory.Q ⋙ T.tensor.flip.obj (DerivedCategory.Q.obj (singleUnitComplex X.O q)) ≅
      DerivedCategory.Q (C := Modules.{u, v, w} X) ⋙ CategoryTheory.shiftFunctor _ (-q) :=
  NatIso.ofComponents (G := CategoryTheory.shiftFunctor (CochainComplex (Modules.{u, v, w} X) ℤ)
      (-q) ⋙ DerivedCategory.Q)
    (fun K => T.comparisonRight K (singleUnitComplex X.O q) (isKFlat_singleUnitComplex X.O q) ≪≫
      DerivedCategory.Q.mapIso (tensorComplexSingleUnitIso X.O K q))
    (fun {K K'} h => by
      have hc := T.comparisonRight_naturality h (𝟙 (singleUnitComplex X.O q))
        (isKFlat_singleUnitComplex X.O q) (isKFlat_singleUnitComplex X.O q)
      rw [DerivedCategory.Q.map_id, (T.tensor.obj (DerivedCategory.Q.obj K')).map_id,
        Category.id_comp] at hc
      dsimp only [Functor.comp_map, Functor.flip_obj_map, Iso.trans_hom, Functor.mapIso_hom]
      rw [← Category.assoc, hc]
      refine (Category.assoc _ _ _).trans ((congrArg (fun t => _ ≫ t) ?_).trans
        (Category.assoc _ _ _).symm)
      exact (DerivedCategory.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Q.map (tensorComplexSingleUnitIso_naturality X.O h q)).trans
          (DerivedCategory.Q.map_comp _ _))) ≪≫
    DerivedCategory.Q.commShiftIso (-q)

/-- **Tensoring with the structure sheaf in degree `q` on the right is the shift by `-q`**:
`- ⊗^L_𝒪 𝒪[q] ≅ (-)⟦-q⟧` on `D(𝒪)`. -/
def rightSingleUnitNatIso (q : ℤ) :
    T.tensor.flip.obj (DerivedCategory.Q.obj (singleUnitComplex X.O q)) ≅
      CategoryTheory.shiftFunctor (DerivedModules.{u, v, w, d} X) (-q) :=
  Localization.liftNatIso (DerivedCategory.Q (C := Modules.{u, v, w} X))
    (HomologicalComplex.quasiIso (Modules.{u, v, w} X) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ T.tensor.flip.obj (DerivedCategory.Q.obj (singleUnitComplex X.O q)))
    (DerivedCategory.Q ⋙ CategoryTheory.shiftFunctor _ (-q))
    _ _ (T.rightSingleUnitComparisonNatIso q)

/-- `𝒪[q] ⊗^L - ≅ (-)⟦-q⟧` on the images of complexes, naturally in the complex. -/
def leftSingleUnitComparisonNatIso (q : ℤ) :
    DerivedCategory.Q ⋙ T.tensor.obj (DerivedCategory.Q.obj (singleUnitComplex X.O q)) ≅
      DerivedCategory.Q (C := Modules.{u, v, w} X) ⋙ CategoryTheory.shiftFunctor _ (-q) :=
  NatIso.ofComponents (G := CategoryTheory.shiftFunctor (CochainComplex (Modules.{u, v, w} X) ℤ)
      (-q) ⋙ DerivedCategory.Q)
    (fun K => T.comparisonLeft (singleUnitComplex X.O q) K (isKFlat_singleUnitComplex X.O q) ≪≫
      DerivedCategory.Q.mapIso (singleUnitTensorComplexIso X.O K q))
    (fun {K K'} h => by
      have hc := T.comparisonLeft_naturality (𝟙 (singleUnitComplex X.O q)) h
        (isKFlat_singleUnitComplex X.O q) (isKFlat_singleUnitComplex X.O q)
      rw [DerivedCategory.Q.map_id, T.tensor.map_id, NatTrans.id_app, Category.id_comp] at hc
      dsimp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom]
      rw [← Category.assoc, hc]
      refine (Category.assoc _ _ _).trans ((congrArg (fun t => _ ≫ t) ?_).trans
        (Category.assoc _ _ _).symm)
      exact (DerivedCategory.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Q.map (singleUnitTensorComplexIso_naturality X.O h q)).trans
          (DerivedCategory.Q.map_comp _ _))) ≪≫
    DerivedCategory.Q.commShiftIso (-q)

/-- **Tensoring with the structure sheaf in degree `q` on the left is the shift by `-q`**:
`𝒪[q] ⊗^L_𝒪 - ≅ (-)⟦-q⟧` on `D(𝒪)`. -/
def leftSingleUnitNatIso (q : ℤ) :
    T.tensor.obj (DerivedCategory.Q.obj (singleUnitComplex X.O q)) ≅
      CategoryTheory.shiftFunctor (DerivedModules.{u, v, w, d} X) (-q) :=
  Localization.liftNatIso (DerivedCategory.Q (C := Modules.{u, v, w} X))
    (HomologicalComplex.quasiIso (Modules.{u, v, w} X) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ T.tensor.obj (DerivedCategory.Q.obj (singleUnitComplex X.O q)))
    (DerivedCategory.Q ⋙ CategoryTheory.shiftFunctor _ (-q))
    _ _ (T.leftSingleUnitComparisonNatIso q)

/-- Tensoring on the right with an object isomorphic to `𝒪[q]` is an autoequivalence. -/
theorem isEquivalence_tensor_flip_obj_of_iso {E : DerivedModules.{u, v, w, d} X} (q : ℤ)
    (e : E ≅ DerivedCategory.Q.obj (singleUnitComplex X.O q)) :
    (T.tensor.flip.obj E).IsEquivalence :=
  Functor.isEquivalence_of_iso
    ((T.rightSingleUnitNatIso q).symm ≪≫ T.tensor.flip.mapIso e.symm)

/-- Tensoring on the left with an object isomorphic to `𝒪[q]` is an autoequivalence. -/
theorem isEquivalence_tensor_obj_of_iso {E : DerivedModules.{u, v, w, d} X} (q : ℤ)
    (e : E ≅ DerivedCategory.Q.obj (singleUnitComplex X.O q)) :
    (T.tensor.obj E).IsEquivalence :=
  Functor.isEquivalence_of_iso ((T.leftSingleUnitNatIso q).symm ≪≫ T.tensor.mapIso e.symm)

end DerivedTensorProduct

end Stacks.SheafOfModules

end
