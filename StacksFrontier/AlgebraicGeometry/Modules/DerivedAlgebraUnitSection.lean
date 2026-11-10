module

public import StacksFrontier.AlgebraicGeometry.Modules.DerivedAlgebraMultiplication
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorUnitors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom

/-!
# A section of the derived multiplication of a sheaf of algebras

Let `A` be a sheaf of commutative `𝒪_X`-algebras on a scheme `X`. The composite
`A ≅ A ⊗^L 𝒪_X ⟶ A ⊗^L A ⟶ A` of the inverse right unit constraint, the unit `𝒪_X ⟶ A` in the
right factor and the derived multiplication is an isomorphism, and the first two maps are
natural in the left factor `A`.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.derivedUnitSection` — the map `A ⟶ A ⊗^L A`, `a ↦ a ⊗ 1`.

## Main results

* `HomologicalComplex.mapBifunctorSingleIso_hom_naturality_right` — `Tot(F(M[0], N[0])) ≅
  F(M, N)[0]` is natural in `N`.
* `Stacks.RelativeSpec.AlgebraSheaf.inv_comp_map_unitModuleMap_comp_mul` — `A ≅ A ⊗ 𝒪_X ⟶ A ⊗ A
  ⟶ A` is the identity of the sheaf of modules `A`.
* `Stacks.RelativeSpec.AlgebraSheaf.derivedUnitSection_naturality` — naturality in the left
  factor, against every endomorphism of `A` in `D(𝒪_X)`.
* `Stacks.RelativeSpec.AlgebraSheaf.isIso_derivedUnitSection_comp_derivedMul` — the composite
  with the derived multiplication is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open MonoidalCategory

universe u

namespace HomologicalComplex

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ M : C₁, (F.obj M).Additive] (M : C₁) {N N' : C₂}
  (g : N ⟶ N')
  [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
    ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ)]
  [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
    ((CochainComplex.singleFunctor C₂ 0).obj N') F (ComplexShape.up ℤ)]

omit [HasZeroObject D] [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
    ((CochainComplex.singleFunctor C₂ 0).obj N') F (ComplexShape.up ℤ)] in
/-- `Tot(F(M[0], N[0]))⁰ ≅ F(M, N)` on the summand `(0, 0)`. -/
theorem ι_mapBifunctorSingleXZeroIso_hom (h) :
    ιMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
        ((CochainComplex.singleFunctor C₂ 0).obj N) F (ComplexShape.up ℤ) 0 0 0 h ≫
      (mapBifunctorSingleXZeroIso F M N).hom =
    (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 M).hom).app _ ≫
      (F.obj M).map (singleObjXSelf (ComplexShape.up ℤ) 0 N).hom := by
  simp [mapBifunctorSingleXZeroIso]

omit [HasMapBifunctor ((CochainComplex.singleFunctor C₁ 0).obj M)
    ((CochainComplex.singleFunctor C₂ 0).obj N') F (ComplexShape.up ℤ)] in
/-- The degree-zero component of `Tot(F(M[0], N[0])) ≅ F(M, N)[0]`. -/
theorem mapBifunctorSingleIso_hom_f_zero_comp_singleObjXSelf :
    (mapBifunctorSingleIso F M N).hom.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 _).hom =
      (mapBifunctorSingleXZeroIso F M N).hom :=
  Category.comp_id _

/-- `Tot(F(M[0], N[0])) ≅ F(M, N)[0]` is natural in `N`. -/
theorem mapBifunctorSingleIso_hom_naturality_right :
    mapBifunctorMap (𝟙 ((CochainComplex.singleFunctor C₁ 0).obj M))
        ((CochainComplex.singleFunctor C₂ 0).map g) F (ComplexShape.up ℤ) ≫
      (mapBifunctorSingleIso F M N').hom =
    (mapBifunctorSingleIso F M N).hom ≫
      (CochainComplex.singleFunctor D 0).map ((F.obj M).map g) := by
  refine HomologicalComplex.hom_ext _ _ (fun k => ?_)
  by_cases hk : k = 0
  · subst hk
    refine mapBifunctor.hom_ext fun i j hij => ?_
    by_cases hi : i = 0
    · subst hi
      have hj : j = 0 := by simpa using hij
      subst hj
      rw [← cancel_mono (singleObjXSelf (ComplexShape.up ℤ) 0 ((F.obj M).obj N')).hom]
      rw [comp_f, comp_f, ι_mapBifunctorMap_assoc]
      simp only [Category.assoc]
      have e1 : ((CochainComplex.singleFunctor D 0).map ((F.obj M).map g)).f 0 ≫
          (singleObjXSelf (ComplexShape.up ℤ) 0 ((F.obj M).obj N')).hom =
          (singleObjXSelf (ComplexShape.up ℤ) 0 ((F.obj M).obj N)).hom ≫ (F.obj M).map g := by
        simp [CochainComplex.singleFunctor, single_map_f_self]
      have e2 : ((CochainComplex.singleFunctor C₂ 0).map g).f 0 =
          (singleObjXSelf (ComplexShape.up ℤ) 0 N).hom ≫ g ≫
            (singleObjXSelf (ComplexShape.up ℤ) 0 N').inv := by
        simp [CochainComplex.singleFunctor, single_map_f_self]
      rw [e1, reassoc_of% (mapBifunctorSingleIso_hom_f_zero_comp_singleObjXSelf F M (N := N)),
        mapBifunctorSingleIso_hom_f_zero_comp_singleObjXSelf, ι_mapBifunctorSingleXZeroIso_hom,
        reassoc_of% (ι_mapBifunctorSingleXZeroIso_hom F M (N := N)), e2]
      simp only [id_f]
      rw [F.map_id, NatTrans.id_app, Category.id_comp]
      have h := (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 M).hom).naturality
        ((singleObjXSelf (ComplexShape.up ℤ) 0 N).hom ≫ g ≫
          (singleObjXSelf (ComplexShape.up ℤ) 0 N').inv)
      exact Eq.trans ((reassoc_of% h) ((F.obj M).map (singleObjXSelf (ComplexShape.up ℤ) 0 N').hom))
        (by simp)
    · exact (isZero_obj_obj_single_obj_X F M N i j (Or.inl hi)).eq_of_src _ _
  · exact (isZero_single_obj_X _ 0 _ k hk).eq_of_tgt _ _

end HomologicalComplex

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry.RingedSite

universe v w d

variable {X : AlgebraicGeometry.RingedSite.{u, v, w}} {_ : HasSheafify X.J AddCommGrpCat.{w}}
  {_ : X.J.WEqualsLocallyBijective AddCommGrpCat.{w}}
  {_ : HasDerivedCategory.{d} (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X)}
  {_ : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive}
  {_ : ∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive}
  {_ : ∀ (K L : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)}
  (T : DerivedTensorProduct.{u, v, w, d} X)

/-- The canonical map after a map in the right factor out of a K-flat complex is the right
comparison followed by the ordinary total tensor of that map. -/
theorem map_comp_toTensor_comp_eq_comparisonRight
    {K L L' M : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, v, w} X) ℤ} (g : L ⟶ L')
    (hL : IsKFlat X.O L)
    (m : HomologicalComplex.mapBifunctor K L' (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ) ⟶ M) :
    (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
        T.toTensor K L' ≫ DerivedCategory.Q.map m =
      (T.comparisonRight K L hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 K) g
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) ≫ m) := by
  have h := T.toTensor_naturality (𝟙 K) g
  rw [DerivedCategory.Q.map_id, T.tensor.map_id, NatTrans.id_app, Category.id_comp] at h
  rw [reassoc_of% h, T.toTensor_eq_comparisonRight K L hL]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun t => _ ≫ t) (DerivedCategory.Q.map_comp _ _).symm)

end Stacks.SheafOfModules.DerivedTensorProduct

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}} (A : AlgebraSheaf X)

/-- `A ⟶ A ⊗ 𝒪_X ⟶ A ⊗ A ⟶ A`, the inverse right unit constraint, the unit in the right
factor and the multiplication, is the identity: `a ↦ a ⊗ 1 ↦ a · 1 = a`. -/
theorem inv_comp_map_unitModuleMap_comp_mul :
    ((Stacks.SheafOfModules.sheafTensorUnitNatIso X.sheaf).app (moduleOfAlgebra A)).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (moduleOfAlgebra A)).map
          (unitModuleMap A) ≫ mul A = 𝟙 _ := by
  apply (SheafOfModules.fullyFaithfulForget _).map_injective
  refine PresheafOfModules.hom_ext ?_
  intro V
  refine ModuleCat.hom_ext ?_
  refine LinearMap.ext (fun x => ?_)
  have h1 := Stacks.SheafOfModules.tensorSheafUnitRightIso_inv_app X.sheaf.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property (moduleOfAlgebra A) V x
  replace h1 := (congrArg (fun i => i.inv.val.app V x)
    (SheafOfModules.rightUnitor_sheafTensor_eq_iso X.sheaf (moduleOfAlgebra A))).trans h1
  have h2 := Stacks.SheafOfModules.sheafify_map_toSheafify_apply X.sheaf.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property
          (@MonoidalCategoryStruct.whiskerLeft
            (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) _ _
            (moduleOfAlgebra A).val _ _ (unitModuleMap A).val) V (x ⊗ₜ (1 : X.sheaf.obj.obj V))
  refine (congrArg (fun z => (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
    (moduleOfAlgebra A)).map (unitModuleMap A) ≫ mul A).val.app V z) h1).trans ?_
  refine (congrArg (fun z => (mul A).val.app V z) h2).trans ?_
  have h3 := congrArg (fun k => k.app V) (sheafificationHomEquiv_mul A)
  refine (congrArg (fun k => ModuleCat.Hom.hom k
    (((@MonoidalCategoryStruct.whiskerLeft
            (PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) _ _
            (moduleOfAlgebra A).val _ _ (unitModuleMap A).val).app V).hom
      (x ⊗ₜ (1 : X.sheaf.obj.obj V)))) h3).trans ?_
  change (ModuleCat.Hom.hom ((presheafMul A).app V))
      (x ⊗ₜ[X.sheaf.obj.obj V] ((unitModuleMap A).val.app V).hom (1 : X.sheaf.obj.obj V)) = x
  refine (PresheafOfModules.ofBilinear_tmul (bilinearMul A) V x _).trans ?_
  refine (congrArg (fun y => (bilinearMul A).app V x y) (unitModuleMap_one A V)).trans ?_
  exact mul_one (show A.right.obj.obj V from x)

section

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

/-- `A ⊗ 𝒪_X ⟶ A ⊗ A ⟶ A` is an isomorphism. -/
theorem isIso_map_unitModuleMap_comp_mul :
    IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (moduleOfAlgebra A)).map
          (unitModuleMap A) ≫ mul A) := by
  have h : IsIso (((Stacks.SheafOfModules.sheafTensorUnitNatIso X.sheaf).app
      (moduleOfAlgebra A)).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
          (moduleOfAlgebra A)).map (unitModuleMap A) ≫ mul A) :=
    (congrArg IsIso (inv_comp_map_unitModuleMap_comp_mul A)).mpr (IsIso.id _)
  exact @IsIso.of_isIso_comp_left _ _ _ _ _
    ((Stacks.SheafOfModules.sheafTensorUnitNatIso X.sheaf).app (moduleOfAlgebra A)).inv _ _ h

end

section Derived

attribute [local instance] HasDerivedCategory.standard
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- `A` as an object of `D(𝒪_X)`, in degree zero. -/
abbrev derivedObject : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf) :=
  DerivedCategory.Q.obj (single A)

/-- The unit `𝒪_X ⟶ A` of a sheaf of algebras, as a map in `D(𝒪_X)`. -/
abbrev derivedUnit :
    Stacks.DerivedTensor.RingedSite.unitObject (Stacks.SheafOfModules.ringedSite X.sheaf) ⟶
      derivedObject A :=
  DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map (unitModuleMap A))

/-- **The section `A ⟶ A ⊗^L A`, `a ↦ a ⊗ 1`**: the inverse right unit constraint followed by
the unit of `A` in the right factor. -/
def derivedUnitSection :
    derivedObject A ⟶
      ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj (derivedObject A)).obj
        (derivedObject A) :=
  ((Stacks.SheafOfModules.derivedTensorAsSiteDatum X.sheaf).rightUnitIso
      (Stacks.SheafOfModules.ringedSite X.sheaf) (derivedObject A)).inv ≫
    ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj (derivedObject A)).map (derivedUnit A)

/-- `a ↦ a ⊗ 1` is natural in the left factor, against every endomorphism of `A` in
`D(𝒪_X)`. -/
theorem derivedUnitSection_naturality (c : derivedObject A ⟶ derivedObject A) :
    derivedUnitSection A ≫ ((Stacks.SheafOfModules.derivedTensor X.sheaf).map c).app _ =
      c ≫ derivedUnitSection A := by
  have hρ := Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_naturality
    (Stacks.SheafOfModules.ringedSite X.sheaf)
    (Stacks.SheafOfModules.derivedTensorAsSiteDatum X.sheaf) c
  have hρ' : ((Stacks.SheafOfModules.derivedTensorAsSiteDatum X.sheaf).rightUnitIso
        (Stacks.SheafOfModules.ringedSite X.sheaf) (derivedObject A)).inv ≫
        ((Stacks.SheafOfModules.derivedTensor X.sheaf).map c).app
          (Stacks.DerivedTensor.RingedSite.unitObject (Stacks.SheafOfModules.ringedSite X.sheaf)) =
      c ≫ ((Stacks.SheafOfModules.derivedTensorAsSiteDatum X.sheaf).rightUnitIso
        (Stacks.SheafOfModules.ringedSite X.sheaf) (derivedObject A)).inv :=
    (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 hρ).trans (Category.assoc _ _ _))
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => ((Stacks.SheafOfModules.derivedTensorAsSiteDatum X.sheaf).rightUnitIso
      (Stacks.SheafOfModules.ringedSite X.sheaf) (derivedObject A)).inv ≫ t)
    (((Stacks.SheafOfModules.derivedTensor X.sheaf).map c).naturality (derivedUnit A))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ _) hρ').trans ?_
  exact Category.assoc _ _ _

section

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

/-- `A ⊗^L 𝒪_X ⟶ A ⊗^L A ⟶ A`, unfolded: the unit in the right factor, the canonical map to the
ordinary total tensor complex, and the multiplication of complexes. -/
theorem map_derivedUnit_comp_derivedMul_eq :
    ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj (derivedObject A)).map (derivedUnit A) ≫
        derivedMul A =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (Stacks.SheafOfModules.ringedSite X.sheaf)).tensor.obj
          (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
              (moduleOfAlgebra A)))).map
        (DerivedCategory.Q.map
          (((CochainComplex.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).map
              (unitModuleMap A) :
            ((HomologicalComplex.single
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
                (ComplexShape.up ℤ) 0).obj
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) ⟶
              ((CochainComplex.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
                (moduleOfAlgebra A))))) ≫
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (Stacks.SheafOfModules.ringedSite X.sheaf)).toTensor
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
          (moduleOfAlgebra A))
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
          (moduleOfAlgebra A)) ≫
      DerivedCategory.Q.map (singleMul A) := rfl

/-- Since `𝒪_X[0]` is K-flat, the canonical map out of `A ⊗^L 𝒪_X` is the right comparison
isomorphism. -/
theorem toTensor_comp_singleMul_eq_comparisonRight :
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (Stacks.SheafOfModules.ringedSite X.sheaf)).tensor.obj
          (DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
              (moduleOfAlgebra A)))).map
        (DerivedCategory.Q.map
          (((CochainComplex.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).map
              (unitModuleMap A) :
            ((HomologicalComplex.single
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
                (ComplexShape.up ℤ) 0).obj
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) ⟶
              ((CochainComplex.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
                (moduleOfAlgebra A))))) ≫
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (Stacks.SheafOfModules.ringedSite X.sheaf)).toTensor
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
          (moduleOfAlgebra A))
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
          (moduleOfAlgebra A)) ≫
      DerivedCategory.Q.map (singleMul A) =
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (Stacks.SheafOfModules.ringedSite X.sheaf)).comparisonRight
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
          (moduleOfAlgebra A))
        ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
            (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))
        (Stacks.SheafOfModules.isKFlat_single_unit X.sheaf)).hom ≫
      DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap
          (𝟙 ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
            (moduleOfAlgebra A)))
          (((CochainComplex.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).map
              (unitModuleMap A) :
            ((HomologicalComplex.single
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
                (ComplexShape.up ℤ) 0).obj
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) ⟶
              ((CochainComplex.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
                (moduleOfAlgebra A))))
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
          (ComplexShape.up ℤ) ≫ singleMul A) :=
  Stacks.SheafOfModules.DerivedTensorProduct.map_comp_toTensor_comp_eq_comparisonRight
    (X := Stacks.SheafOfModules.ringedSite X.sheaf)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf))
    (K := ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
      (moduleOfAlgebra A)))
    (L := ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))))
    (L' := ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
      (moduleOfAlgebra A)))
    (M := single A)
    ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).map
      (unitModuleMap A))
    (Stacks.SheafOfModules.isKFlat_single_unit X.sheaf) (singleMul A)

/-- `Tot(A[0] ⊗ 𝒪_X[0]) ⟶ Tot(A[0] ⊗ A[0]) ⟶ A[0]` is an isomorphism of complexes. -/
theorem isIso_mapBifunctorMap_unitModuleMap_comp_singleMul :
    IsIso (HomologicalComplex.mapBifunctorMap
          (𝟙 ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
            (moduleOfAlgebra A)))
          (((CochainComplex.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).map
              (unitModuleMap A) :
            ((HomologicalComplex.single
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
                (ComplexShape.up ℤ) 0).obj
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) ⟶
              ((CochainComplex.singleFunctor
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).obj
                (moduleOfAlgebra A))))
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
          (ComplexShape.up ℤ) ≫ singleMul A) := by
  have h3 := HomologicalComplex.mapBifunctorSingleIso_hom_naturality_right
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) (moduleOfAlgebra A)
    (unitModuleMap A)
  have e : singleMul A = (HomologicalComplex.mapBifunctorSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (moduleOfAlgebra A) (moduleOfAlgebra A)).hom ≫
        (CochainComplex.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) 0).map
          (mul A) := rfl
  have := isIso_map_unitModuleMap_comp_mul A
  rw [e, ← Category.assoc, h3, Category.assoc, ← Functor.map_comp]
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (Functor.map_isIso _ _)

/-- **`A ⟶ A ⊗^L A ⟶ A`, `a ↦ a ⊗ 1 ↦ a`, is an isomorphism.** -/
theorem isIso_derivedUnitSection_comp_derivedMul :
    IsIso (derivedUnitSection A ≫ derivedMul A) :=
  (congrArg IsIso ((Category.assoc _ _ _).trans (congrArg (fun t =>
      ((Stacks.SheafOfModules.derivedTensorAsSiteDatum X.sheaf).rightUnitIso
        (Stacks.SheafOfModules.ringedSite X.sheaf) (derivedObject A)).inv ≫ t)
      ((map_derivedUnit_comp_derivedMul_eq A).trans
        (toTensor_comp_singleMul_eq_comparisonRight A))))).mpr
    (IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' (Iso.isIso_hom _)
      (@Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Q _
        (isIso_mapBifunctorMap_unitModuleMap_comp_singleMul A))))

end

end Derived

end Stacks.RelativeSpec.AlgebraSheaf
