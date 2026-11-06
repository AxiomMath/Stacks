module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLawGeneral
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionTransposeReduction
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedAlgebraMultiplication
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ProjectiveSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorUnitSmul
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.GlobalSectionLinear

/-!
# The diagonal map of a relative dualizing complex generates
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect
  AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf


namespace HomologicalComplex

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ M : C₁, (F.obj M).Additive]

omit [Preadditive C₂] [Preadditive D] [HasZeroObject C₂] [HasZeroObject D]
  [F.Additive] [∀ M : C₁, (F.obj M).Additive] in
/-- In degree zero, the map of complexes `φ[0] : A[0] ⟶ B[0]` is `φ` itself. -/
theorem singleFunctor_map_f_zero {A B : C₁} (φ : A ⟶ B) :
    ((CochainComplex.singleFunctor C₁ 0).map φ).f 0 = φ :=
  (single_map_f_self _ _ φ).trans ((Category.id_comp _).trans (Category.comp_id _))

/-- On the `(0, 0)` summand, the identification `Tot(F(M[0], N[0])) ≅ F(M, N)[0]` is the
identity of `F(M, N)`. -/
@[reassoc]
theorem ιMapBifunctor_mapBifunctorSingleIso_hom_f (M : C₁) (N : C₂)
    [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
      ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)] :
    ιMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
        ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ) 0 0 0 (by simp) ≫
        (mapBifunctorSingleIso F M N).hom.f 0 = 𝟙 ((F.obj M).obj N) := by
  simp only [mapBifunctorSingleIso, mapBifunctorSingleXZeroIso, Hom.isoOfComponents_hom_f,
    ↓reduceDIte, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
  refine (ι_mapBifunctorDesc_assoc _ _ _ _ _).trans ?_
  simp only [↓reduceDIte]
  exact (Category.id_comp _).trans ((congrArg (· ≫ _) ((F.map_id M).symm ▸ rfl :
    (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 M).hom).app _ = 𝟙 _)).trans
      ((Category.id_comp _).trans ((F.obj M).map_id N)))

/-- **The identification `Tot(F(M[0], N[0])) ≅ F(M, N)[0]` is natural in `M` and `N`.** -/
theorem mapBifunctorMap_single_comp_mapBifunctorSingleIso_hom {M M' : C₁} {N N' : C₂}
    (f : M ⟶ M') (g : N ⟶ N')
    [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
      ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)]
    [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M')
      ((CochainComplex.singleFunctor C₂ 0).obj N') F (ComplexShape.up ℤ)] :
    mapBifunctorMap ((CochainComplex.singleFunctor C₁ 0).map f)
        ((CochainComplex.singleFunctor C₂ 0).map g) F (ComplexShape.up ℤ) ≫
        (mapBifunctorSingleIso F M' N').hom =
      (mapBifunctorSingleIso F M N).hom ≫
        (CochainComplex.singleFunctor D 0).map ((F.map f).app N ≫ (F.obj M').map g) := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  by_cases hk : k = 0
  · subst hk
    refine mapBifunctor.hom_ext fun i j hij => ?_
    by_cases hi : i = 0
    · subst hi
      obtain rfl : j = 0 := by
        change 0 + j = 0 at hij
        omega
      rw [comp_f, comp_f, ι_mapBifunctorMap_assoc, ιMapBifunctor_mapBifunctorSingleIso_hom_f,
        ιMapBifunctor_mapBifunctorSingleIso_hom_f_assoc, singleFunctor_map_f_zero,
        singleFunctor_map_f_zero, singleFunctor_map_f_zero]
      exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans (Category.id_comp _).symm
    · exact (isZero_obj_obj_single_obj_X F M N i j (Or.inl hi)).eq_of_src _ _
  · exact (isZero_single_obj_X _ 0 _ k hk).eq_of_tgt _ _

end HomologicalComplex

namespace Stacks.RelativeSpec.AlgebraSheaf

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory

variable {Y : Scheme.{u}} (A : AlgebraSheaf Y)

/-- The sections of the underlying module of a sheaf of algebras form a commutative ring. -/
local instance sectionsCommRing' (U : (Opens Y)ᵒᵖ) :
    CommRing ((moduleOfAlgebra A).val.obj U) :=
  inferInstanceAs (CommRing (A.right.obj.obj U))

/-- The section `1` of a sheaf of algebras, as a global section of its underlying module. -/
def unitSections : (moduleOfAlgebra A).sections :=
  PresheafOfModules.sectionsMk (fun U => (1 : A.right.obj.obj U))
    (fun _ _ f => map_one (A.right.obj.map f).hom)

/-- **The unit `𝒪_Y ⟶ A` of a sheaf of algebras**, as a morphism of sheaves of `𝒪_Y`-modules: it
sends a local section `r` of `𝒪_Y` to `r · 1`. -/
def unitMap : SheafOfModules.unit Y.ringCatSheaf ⟶ moduleOfAlgebra A :=
  (moduleOfAlgebra A).unitHomEquiv.symm (unitSections A)

/-- The unit `𝒪_Y ⟶ A` sends the section `1` to the section `1`. -/
theorem unitMap_app_one (U : (Opens Y)ᵒᵖ) :
    (unitMap A).val.app U (1 : Y.ringCatSheaf.obj.obj U) = 1 :=
  congrArg (fun s => s.val U) ((moduleOfAlgebra A).unitHomEquiv.apply_symm_apply (unitSections A))

/-- The unit `𝒪_Y ⟶ A` sends a local section `r` of `𝒪_Y` to `r • 1`. -/
theorem unitMap_app (U : (Opens Y)ᵒᵖ) (r : Y.ringCatSheaf.obj.obj U) :
    (unitMap A).val.app U r = r • (1 : (moduleOfAlgebra A).val.obj U) := by
  calc (unitMap A).val.app U r = (unitMap A).val.app U (r • (1 : Y.ringCatSheaf.obj.obj U)) := by
        rw [smul_eq_mul, mul_one]
    _ = r • (unitMap A).val.app U (1 : Y.ringCatSheaf.obj.obj U) := map_smul _ _ _
    _ = r • (1 : (moduleOfAlgebra A).val.obj U) := by rw [unitMap_app_one]

/-- **The unit of a sheaf of algebras is a unit for its multiplication**: `A ⊗ 𝒪_Y ⟶ A ⊗ A ⟶ A`
is the canonical isomorphism `A ⊗ 𝒪_Y ≅ A`. -/
theorem sheafTensor_map_unitMap_comp_mul :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj (moduleOfAlgebra A)).map
      (unitMap A) ≫ mul A =
      (Stacks.SheafOfModules.sheafTensorUnitIsoFreeSections Y.sheaf (moduleOfAlgebra A)).hom := by
  refine PresheafOfModules.sheafification_hom_ext ?_
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let G := SheafOfModules.forget Y.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)
  let h := PresheafOfModules.tensorHom (𝟙 (moduleOfAlgebra A).val) (unitMap A).val
  have hmul : adj.unit.app (PresheafOfModules.tensorObj (moduleOfAlgebra A).val
      (moduleOfAlgebra A).val) ≫ G.map (mul A) = presheafMul A :=
    (adj.homEquiv_unit (f := mul A)).symm.trans (sheafificationHomEquiv_mul A)
  have hL : adj.unit.app _ ≫ G.map ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map h
      ≫ mul A) = h ≫ presheafMul A :=
    (congrArg (adj.unit.app _ ≫ ·) (G.map_comp _ _)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ G.map (mul A)) (PresheafOfModules.unit_comp_map h)).trans
        ((Category.assoc _ _ _).trans (congrArg (h ≫ ·) hmul))))
  let adj' := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)
  let G' := SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) ⋙
    PresheafOfModules.restrictScalars (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)
  let ρp := (MonoidalCategory.rightUnitor ((SheafOfModules.forget
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)).obj (moduleOfAlgebra A))).hom
  have hR : adj'.unit.app _ ≫ G'.map ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).map ρp ≫
        adj'.counit.app (moduleOfAlgebra A)) = ρp :=
    (congrArg (adj'.unit.app _ ≫ ·) (G'.map_comp _ _)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ G'.map (adj'.counit.app _)) (PresheafOfModules.unit_comp_map ρp)).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (adj'.right_triangle_components _)).trans
          (Category.comp_id _)))))
  refine hL.trans (Eq.trans ?_ hR.symm)
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (TensorProduct.ext' fun x r => ?_)
  show (presheafMul A).app U (PresheafOfModules.Hom.app h U (x ⊗ₜ r)) = _
  rw [PresheafOfModules.tensorHom_tmul]
  simp only [presheafMul]
  show x * (unitMap A).val.app U r = _
  refine (congrArg (x * ·) (unitMap_app A U r)).trans ?_
  refine Eq.trans ?_ (ModuleCat.MonoidalCategory.rightUnitor_hom_apply x r).symm
  show x * ((show (moduleOfAlgebra A).val.obj U from (structureMap A).hom.app U r) * 1) =
    (show (moduleOfAlgebra A).val.obj U from (structureMap A).hom.app U r) * x
  rw [mul_one, mul_comm]

/-- **The unit of a sheaf of algebras is a unit for its multiplication**, in the form that
`A ⊗ 𝒪_Y ⟶ A ⊗ A ⟶ A` is invertible. -/
theorem isIso_sheafTensor_map_unitMap_comp_mul :
    IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj (moduleOfAlgebra A)).map
      (unitMap A) ≫ mul A) := by
  rw [sheafTensor_map_unitMap_comp_mul]
  infer_instance

/-- **Multiplication by a global scalar commutes with the multiplication of a sheaf of
algebras**, in the first factor. -/
theorem sheafTensor_map_globalSectionToEnd_comp_mul
    (a : (Y.ringCatSheaf.obj ⋙ forget RingCat).sections) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).map
        ((Stacks.SheafOfModules.globalSectionToEnd Y.ringCatSheaf a).asHom.app
          (moduleOfAlgebra A))).app (moduleOfAlgebra A) ≫ mul A =
      mul A ≫ (Stacks.SheafOfModules.globalSectionToEnd Y.ringCatSheaf a).asHom.app
        (moduleOfAlgebra A) :=
  (congrArg (· ≫ mul A) (AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd
    Y.sheaf (moduleOfAlgebra A) a (moduleOfAlgebra A))).trans
    ((Stacks.SheafOfModules.globalSectionToEnd Y.ringCatSheaf a).asHom.naturality (mul A)).symm

/-! ### The derived unit law -/

attribute [local instance 2000] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- `𝒪_Y[0] ⟶ A[0]`, the unit of `A` on complexes concentrated in degree zero. -/
abbrev singleUnitMap :
    (CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).obj
        (SheafOfModules.unit Y.ringCatSheaf) ⟶ single A :=
  (CochainComplex.singleFunctor _ 0).map (unitMap A)

/-- On complexes concentrated in degree zero, `f[0] ⊗ g[0]` followed by the multiplication of `A[0]`
is the identification with `M ⊗ N` followed by `f ⊗ g` and the multiplication of `A`. -/
private theorem mapBifunctorMap_single_map_comp_singleMul
    {M N : SheafOfModules.{u} Y.ringCatSheaf} (f : M ⟶ moduleOfAlgebra A)
    (g : N ⟶ moduleOfAlgebra A) :
    HomologicalComplex.mapBifunctorMap
      (C₁ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (C₂ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (D := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      ((CochainComplex.singleFunctor _ 0).map f) ((CochainComplex.singleFunctor _ 0).map g)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) (ComplexShape.up ℤ) ≫
        singleMul A =
      (HomologicalComplex.mapBifunctorSingleIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) M N).hom ≫
        (CochainComplex.singleFunctor _ 0).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map f).app N ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
              (moduleOfAlgebra A)).map g ≫ mul A) := by
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [HomologicalComplex.mapBifunctorMap_single_comp_mapBifunctorSingleIso_hom, Category.assoc,
    ← Functor.map_comp, Category.assoc]

/-- On complexes, `A[0] ⊗ 𝒪_Y[0] ⟶ A[0] ⊗ A[0] ⟶ A[0]` is an isomorphism. -/
theorem isIso_mapBifunctorMap_singleUnitMap_comp_singleMul :
    IsIso (HomologicalComplex.mapBifunctorMap
      (C₁ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (C₂ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (D := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (𝟙 (single A)) (singleUnitMap A)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) (ComplexShape.up ℤ) ≫
        singleMul A) := by
  have := mapBifunctorMap_single_map_comp_singleMul A (𝟙 (moduleOfAlgebra A)) (unitMap A)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at this
  erw [this]
  have := isIso_sheafTensor_map_unitMap_comp_mul A
  infer_instance

/-- The canonical map `A ⊗^L 𝒪_Y ⟶ Tot(A[0] ⊗ 𝒪_Y[0])` is invertible, `𝒪_Y[0]` being K-flat. -/
theorem isIso_toTensor_single_unit :
    IsIso ((Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite Y.sheaf)).toTensor (single A)
      ((CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).obj
        (SheafOfModules.unit Y.ringCatSheaf))) := by
  have hc := (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite Y.sheaf)).toTensor_eq_comparisonRight (single A)
    ((CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).obj
        (SheafOfModules.unit Y.ringCatSheaf)) (Stacks.SheafOfModules.isKFlat_single_unit _)
  exact hc ▸ inferInstance

/-- Naturality of the canonical map to the total tensor complex, at the unit of `A`. -/
theorem derivedTensor_map_singleUnitMap_comp_toTensor :
    ((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj
        (DerivedCategory.Q.obj (single A))).map (DerivedCategory.Q.map (singleUnitMap A)) ≫
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite Y.sheaf)).toTensor (single A) (single A) =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite Y.sheaf)).toTensor (single A)
      ((CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).obj
        (SheafOfModules.unit Y.ringCatSheaf)) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      (C₁ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (C₂ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (D := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (𝟙 (single A)) (singleUnitMap A)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) (ComplexShape.up ℤ)) := by
  exact Stacks.SheafOfModules.toTensor_naturality_right Y.sheaf (single A) (singleUnitMap A)

/-- **The derived unit law**: `A ⊗^L 𝒪_Y ⟶ A ⊗^L A ⟶ A`, the derived tensor product of `A` with
the unit followed by the derived multiplication, is an isomorphism. -/
theorem isIso_derivedTensor_map_singleUnitMap_comp_derivedMul :
    IsIso (((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj
        (DerivedCategory.Q.obj (single A))).map (DerivedCategory.Q.map (singleUnitMap A)) ≫
      derivedMul A) := by
  have key : ((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj
        (DerivedCategory.Q.obj (single A))).map (DerivedCategory.Q.map (singleUnitMap A)) ≫
        derivedMul A =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite Y.sheaf)).toTensor (single A)
      ((CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).obj
        (SheafOfModules.unit Y.ringCatSheaf)) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      (C₁ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (C₂ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (D := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (𝟙 (single A)) (singleUnitMap A)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) (ComplexShape.up ℤ) ≫
        singleMul A) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ DerivedCategory.Q.map (singleMul A))
      (derivedTensor_map_singleUnitMap_comp_toTensor A)).trans ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp (HomologicalComplex.mapBifunctorMap
      (C₁ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (C₂ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (D := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (𝟙 (single A)) (singleUnitMap A)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
      (ComplexShape.up ℤ)) (singleMul A)).symm)))
  have := isIso_mapBifunctorMap_singleUnitMap_comp_singleMul A
  rw [key]
  exact IsIso.comp_isIso' (isIso_toTensor_single_unit A)
    (DerivedCategory.Q.mapIso (asIso (HomologicalComplex.mapBifunctorMap
      (C₁ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (C₂ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (D := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (𝟙 (single A)) (singleUnitMap A)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf) (ComplexShape.up ℤ) ≫
        singleMul A))).isIso_hom

/-- **A section of the derived multiplication** `A ⟶ A ⊗^L A`: the inverse of the derived unit
law followed by the unit in the second factor. -/
def derivedMulSection :
    (DerivedCategory.Q.obj (single A) :
        DerivedCategory (Stacks.SheafOfModules.StructureSheafModules Y.sheaf)) ⟶
      ((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj
      (DerivedCategory.Q.obj (single A))).obj (DerivedCategory.Q.obj (single A)) :=
  haveI := isIso_derivedTensor_map_singleUnitMap_comp_derivedMul A
  inv (((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj
        (DerivedCategory.Q.obj (single A))).map (DerivedCategory.Q.map (singleUnitMap A)) ≫
      derivedMul A) ≫
    ((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj
        (DerivedCategory.Q.obj (single A))).map (DerivedCategory.Q.map (singleUnitMap A))

/-- The derived multiplication is a split epimorphism, split by `derivedMulSection`. -/
theorem derivedMulSection_comp_derivedMul : derivedMulSection A ≫ derivedMul A = 𝟙 _ := by
  have := isIso_derivedTensor_map_singleUnitMap_comp_derivedMul A
  exact (Category.assoc _ _ _).trans (IsIso.inv_hom_id _)

/-! ### Endomorphisms commuting with the multiplication -/

variable {A} in
/-- On complexes: an endomorphism `g` of `A` commuting with the multiplication in the first
factor commutes with `A[0] ⊗ A[0] ⟶ A[0]`. -/
theorem mapBifunctorMap_single_comp_singleMul (g : moduleOfAlgebra A ⟶ moduleOfAlgebra A)
    (hg : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map g).app
      (moduleOfAlgebra A) ≫ mul A = mul A ≫ g) :
    HomologicalComplex.mapBifunctorMap
      (C₁ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (C₂ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (D := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      ((CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).map g)
      (𝟙 (single A))
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
      (ComplexShape.up ℤ) ≫ singleMul A =
      singleMul A ≫
        ((CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).map g) := by
  have := mapBifunctorMap_single_map_comp_singleMul A g (𝟙 (moduleOfAlgebra A))
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, hg] at this
  refine this.trans ?_
  rw [singleMul, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- Naturality of the canonical map to the total tensor complex in the first factor. -/
theorem derivedTensor_map_single_app_comp_toTensor (g : moduleOfAlgebra A ⟶ moduleOfAlgebra A) :
    ((Stacks.SheafOfModules.derivedTensor Y.sheaf).map
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor
        (SheafOfModules.{u} Y.ringCatSheaf) 0).map g))).app
        (DerivedCategory.Q.obj (single A)) ≫ (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite Y.sheaf)).toTensor (single A) (single A) =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite Y.sheaf)).toTensor (single A) (single A) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      (C₁ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (C₂ := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      (D := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
          ((CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).map g)
          (𝟙 (single A))
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
          (ComplexShape.up ℤ)) := by
  have hnat := (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite Y.sheaf)).toTensor_naturality
        ((CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).map g)
        (𝟙 (single A))
  refine Eq.trans ?_ hnat
  have h0 : ((Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite Y.sheaf)).tensor.obj (DerivedCategory.Q.obj (single A))).map
      (DerivedCategory.Q.map (𝟙 (single A))) = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact congrArg (_ ≫ ·) ((Category.id_comp _).symm.trans (congrArg (· ≫ _) h0.symm))

variable {A} in
/-- **An endomorphism of `A` commuting with the multiplication commutes with the derived
multiplication** in the first factor. -/
theorem derivedTensor_map_single_app_comp_derivedMul (g : moduleOfAlgebra A ⟶ moduleOfAlgebra A)
    (hg : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map g).app
      (moduleOfAlgebra A) ≫ mul A = mul A ≫ g) :
    ((Stacks.SheafOfModules.derivedTensor Y.sheaf).map
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor
        (SheafOfModules.{u} Y.ringCatSheaf) 0).map g))).app
        (DerivedCategory.Q.obj (single A)) ≫ derivedMul A =
      derivedMul A ≫ DerivedCategory.Q.map
        ((CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf) 0).map g) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ DerivedCategory.Q.map (singleMul A))
    (derivedTensor_map_single_app_comp_toTensor A g)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) ((DerivedCategory.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Q.map (mapBifunctorMap_single_comp_singleMul g hg)).trans
          (DerivedCategory.Q.map_comp _ _)))).trans (Category.assoc _ _ _).symm)))

/-- Conjugating by an isomorphism and cancelling. -/
theorem inv_comp_conjugate_comp {C : Type*} [Category C] {P Q Z : C} (i : P ⟶ Q) [IsIso i]
    (x : Q ⟶ Q) (t : P ⟶ Z) : inv i ≫ (((i ≫ x) ≫ inv i) ≫ t) = x ≫ inv i ≫ t := by
  simp

variable {A} in
/-- The derived unit law commutes with an endomorphism of `A` commuting with the multiplication. -/
theorem derivedTensor_map_single_app_comp_unitLaw
    (g : moduleOfAlgebra A ⟶ moduleOfAlgebra A)
    (hg : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map g).app
      (moduleOfAlgebra A) ≫ mul A = mul A ≫ g) :
    ((Stacks.SheafOfModules.derivedTensor Y.sheaf).map
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor
        (SheafOfModules.{u} Y.ringCatSheaf) 0).map g))).app
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
          (SheafOfModules.{u} Y.ringCatSheaf) 0).obj
          (SheafOfModules.unit Y.ringCatSheaf))) ≫
          (((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj
          (DerivedCategory.Q.obj (single A))).map
            (DerivedCategory.Q.map (singleUnitMap A)) ≫ derivedMul A) =
          (((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj
          (DerivedCategory.Q.obj (single A))).map (DerivedCategory.Q.map (singleUnitMap A)) ≫
            derivedMul A) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf)
        0).map g) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ derivedMul A)
    (((Stacks.SheafOfModules.derivedTensor Y.sheaf).map
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor
        (SheafOfModules.{u} Y.ringCatSheaf) 0).map g))).naturality
        (DerivedCategory.Q.map (singleUnitMap A))).symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj
          (DerivedCategory.Q.obj (single A))).map (DerivedCategory.Q.map (singleUnitMap A)) ≫ ·)
      (derivedTensor_map_single_app_comp_derivedMul g hg)).trans (Category.assoc _ _ _).symm)))

variable {A} in
/-- The section of the derived multiplication commutes with an endomorphism of `A` commuting with
the multiplication, acting on the first factor. -/
theorem derivedMulSection_comp_derivedTensor_map_single_app
    (g : moduleOfAlgebra A ⟶ moduleOfAlgebra A)
    (hg : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map g).app
      (moduleOfAlgebra A) ≫ mul A = mul A ≫ g) :
    derivedMulSection A ≫ ((Stacks.SheafOfModules.derivedTensor Y.sheaf).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor
          (SheafOfModules.{u} Y.ringCatSheaf) 0).map g))).app
          (DerivedCategory.Q.obj (single A)) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (SheafOfModules.{u} Y.ringCatSheaf)
        0).map g) ≫ derivedMulSection A := by
  have := isIso_derivedTensor_map_singleUnitMap_comp_derivedMul A
  have h2 := (IsIso.eq_comp_inv (((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj
          (DerivedCategory.Q.obj (single A))).map (DerivedCategory.Q.map (singleUnitMap A)) ≫
            derivedMul A)).mpr
    (derivedTensor_map_single_app_comp_unitLaw g hg)
  have hτ := ((Stacks.SheafOfModules.derivedTensor Y.sheaf).map
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor
        (SheafOfModules.{u} Y.ringCatSheaf) 0).map g))).naturality
        (DerivedCategory.Q.map (singleUnitMap A))
  unfold derivedMulSection
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hτ).trans ?_)
  rw [h2]
  exact inv_comp_conjugate_comp _ _ _

end Stacks.RelativeSpec.AlgebraSheaf

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

/-- `L pr₁^*` on morphisms, `L pr₁^*K|_W ⟶ L pr₁^*L|_W` for `φ : K ⟶ L`, read in the module
category of `D(𝒪_W)` that `D.derivedPullbackProj` lands in. -/
def derivedPullbackProjMap {K L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)} (φ : K ⟶ L) :
    D.derivedPullbackProj K ⟶ D.derivedPullbackProj L :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    D.proj.toLRSHom.toShHom).map φ

/-- The map that `ζ` defines, as the transpose under Stacks 08DI of `μ ≫ ζ`, with `μ` the
derived multiplication of `Δ_*𝒪_X`. -/
theorem diagonalAction_eq {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    D.diagonalAction K ζ = (Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf
      D.diagonalObject D.diagonalObject (D.derivedPullbackProj K)).symm
        (D.diagonalAlgebra.derivedMul ≫ ζ) := by
  unfold diagonalAction
  congr 1

/-- The transpose of the map that `ζ` defines is `μ ≫ ζ`. -/
theorem derivedSheafHomTensorEquiv_diagonalAction_apply
    {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject D.diagonalObject
      (D.derivedPullbackProj K) (D.diagonalAction K ζ) = D.diagonalAlgebra.derivedMul ≫ ζ :=
  (congrArg (Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject
    D.diagonalObject (D.derivedPullbackProj K)) (D.diagonalAction_eq ζ)).trans
    (AddEquiv.apply_symm_apply _ _)

/-- **The map that `ξ` defines is natural in `K`.** For `φ : K ⟶ L`, the map defined by
`ζ ≫ L pr₁^*φ` is the map defined by `ζ` followed by `R SheafHom(Δ_*𝒪_X, L pr₁^*φ)`. -/
theorem diagonalAction_comp_derivedPullbackProjMap
    {K L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (φ : K ⟶ L) (ζ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    D.diagonalAction L (ζ ≫ D.derivedPullbackProjMap φ) =
      D.diagonalAction K ζ ≫
        ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj (op D.diagonalObject)).map
          (D.derivedPullbackProjMap φ) := by
  apply (Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject
    D.diagonalObject (D.derivedPullbackProj L)).injective
  refine (D.derivedSheafHomTensorEquiv_diagonalAction_apply
    (ζ ≫ D.derivedPullbackProjMap φ)).trans ?_
  refine Eq.trans ?_ (Stacks.SheafOfModules.derivedSheafHomTensorEquiv_naturality_target
    D.W.sheaf _ _ _ _).symm
  refine Eq.trans ?_ (congrArg (· ≫ D.derivedPullbackProjMap φ)
    (D.derivedSheafHomTensorEquiv_diagonalAction_apply ζ)).symm
  exact (Category.assoc _ _ _).symm

/-- **The left inverse of the diagonal action**: a map `Δ_*𝒪_X ⟶ R SheafHom(Δ_*𝒪_X, E)` is sent to
its transpose `Δ_*𝒪_X ⊗^L Δ_*𝒪_X ⟶ E` under Stacks 08DI precomposed with the section of the
derived multiplication. -/
def diagonalActionRetraction {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (ψ : D.diagonalObject ⟶
      ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj (op D.diagonalObject)).obj
        (D.derivedPullbackProj K)) :
    D.diagonalObject ⟶ D.derivedPullbackProj K :=
  D.diagonalAlgebra.derivedMulSection ≫
    Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject D.diagonalObject
      (D.derivedPullbackProj K) ψ

/-- `diagonalActionRetraction` is a left inverse of the diagonal action. -/
theorem diagonalActionRetraction_diagonalAction
    {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    D.diagonalActionRetraction (D.diagonalAction K ζ) = ζ := by
  unfold diagonalActionRetraction
  rw [D.derivedSheafHomTensorEquiv_diagonalAction_apply ζ]
  rw [← Category.assoc, D.diagonalAlgebra.derivedMulSection_comp_derivedMul, Category.id_comp]

/-- **The diagonal action is injective**: a map `ζ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` is determined by the
map it defines. -/
theorem diagonalAction_injective (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    Function.Injective (D.diagonalAction K) :=
  Function.LeftInverse.injective D.diagonalActionRetraction_diagonalAction

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
