module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorUnitors
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorUnitDerived

/-!
# The copower unit identification is the monoidal left unitor

Let `S` be a simplicial-site situation. The unit identification
`CategoryTheory.SimplicialSiteSituation.unitTensorIso`, `ℤ ⊗_ℤ - ≅ 𝟭` on abelian sheaves over
the total site, is a composite of six copower and sheafification identifications. This file
proves that it is the left unitor of the monoidal structure
`SheafOfModules.monoidalCategorySheafTensor` on sheaves of modules over the constant sheaf of
rings `ℤ`, conjugated by the equivalence of abelian sheaves with those modules and by the
identification `CategoryTheory.SimplicialSiteSituation.totalIntegerModuleIsoUnit` of the
constant integer sheaf with the structure sheaf.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.monoidalUnitLeftIsoAux`: the left unitor
  `𝒪 ⊗_𝒪 ℱ ≅ ℱ` of `Mod(ℤ)`, conjugated to abelian sheaves.

## Main results

* `CategoryTheory.SimplicialSiteSituation.unitTensorIsoAux_eq_monoidalUnitLeftIso` and
  `unitTensorIso_hom_app_eq`: the copower unit identification is the monoidal left unitor.

## References

* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

universe u

namespace AddCommGrpCat

/-- The comparison of the free abelian group on a type with the free module over the integers on
it carries the generator labelled by `y` to the summand of `1` labelled by `y`. -/
theorem freeIsoFreeIntModule_hom_app_of (Y : Type u) (y : Y) :
    AddCommGrpCat.Hom.hom (AddCommGrpCat.freeIsoFreeIntModule.{u}.hom.app Y)
        (FreeAbelianGroup.of y) = Finsupp.single y 1 :=
  congrArg (fun f => f y) (CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
    AddCommGrpCat.adj AddCommGrpCat.freeIntModuleAdj Y)

/-- The comparison of the free module over the integers with the free abelian group carries the
summand of `1` labelled by `y` to the generator labelled by `y`. -/
theorem freeIsoFreeIntModule_inv_app_single (Y : Type u) (y : Y) :
    AddCommGrpCat.Hom.hom (AddCommGrpCat.freeIsoFreeIntModule.{u}.inv.app Y)
        (Finsupp.single y 1) = FreeAbelianGroup.of y := by
  have hc : AddCommGrpCat.Hom.hom (AddCommGrpCat.freeIsoFreeIntModule.{u}.hom.app Y ≫
        AddCommGrpCat.freeIsoFreeIntModule.{u}.inv.app Y) (FreeAbelianGroup.of y) =
      FreeAbelianGroup.of y :=
    congrArg
      (fun k : AddCommGrpCat.free.{u}.obj Y ⟶ AddCommGrpCat.free.{u}.obj Y =>
        AddCommGrpCat.Hom.hom k (FreeAbelianGroup.of y))
      (Iso.hom_inv_id_app AddCommGrpCat.freeIsoFreeIntModule.{u} Y)
  refine Eq.trans ?_ hc
  exact congrArg
    (fun k : (AddCommGrpCat.freeIntModule.{u}.obj Y : Type u) =>
      AddCommGrpCat.Hom.hom (AddCommGrpCat.freeIsoFreeIntModule.{u}.inv.app Y) k)
    (freeIsoFreeIntModule_hom_app_of Y y).symm

end AddCommGrpCat

namespace CategoryTheory.Equivalence

/-- An equivalence carries a morphism conjugated by its unit back to the morphism itself: for
`a : e F X ⟶ Z` and `b : Z ⟶ e F Y`, the composite
`η_X ≫ e⁻¹ a ≫ e⁻¹ b ≫ η_Y⁻¹` has image `a ≫ b` under `e F`. -/
theorem functor_map_unitIso_conj {C D : Type*} [Category C] [Category D] (e : C ≌ D)
    {X Y : C} {Z : D} (a : e.functor.obj X ⟶ Z) (b : Z ⟶ e.functor.obj Y) :
    e.functor.map (((e.unitIso.app X).hom ≫ e.inverse.map a) ≫
      (e.inverse.map b ≫ (e.unitIso.app Y).inv)) = a ≫ b := by
  simp only [Functor.id_obj, Functor.comp_obj, Iso.app_hom, Iso.app_inv, Category.assoc,
    Functor.map_comp, fun_inv_map, counitInv_functor_comp, Category.comp_id,
    Iso.inv_hom_id_app_assoc, functor_unit_comp_assoc]

end CategoryTheory.Equivalence

namespace PresheafOfModules

open CategoryTheory

variable {C : Type u} [Category.{u} C]

/-- The presentation of the free presheaf of modules over the constant integers as a free abelian
presheaf carries the generator labelled by a section `x` of `E` to the basis element of `x`. -/
theorem freeObjToFreeAbIso_hom_app_freeMk (E : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ) (x : E.obj X) :
    AddCommGrpCat.Hom.hom ((freeObjToFreeAbIso (C := C) E).hom.app X)
        (ModuleCat.freeMk (R := ((intRingPresheaf C).obj X : Type u)) x) =
      (FreeAbelianGroup.of x : (((E ⋙ AddCommGrpCat.free.{u}).obj X : AddCommGrpCat.{u}) :
        Type u)) := by
  change AddCommGrpCat.Hom.hom (AddCommGrpCat.freeIsoFreeIntModule.{u}.inv.app (E.obj X))
      (Finsupp.single x (1 : ULift.{u} ℤ)) = _
  exact AddCommGrpCat.freeIsoFreeIntModule_inv_app_single (E.obj X) x

end PresheafOfModules

namespace CategoryTheory.SimplicialSiteSituation

open Stacks.DerivedTensor.AbelianSheaves Stacks.SheafOfModules.Tensor PresheafOfModules

/-- The unit exhibiting the tensor product of two sheaves of modules over the constant integers
on the total site as the sheafification of the objectwise tensor product of their underlying
presheaves. -/
noncomputable abbrev tensorSheafificationUnitInt (S : SimplicialSiteSituation.{u})
    (F G : SheafOfModules.{u} (intRings S.totalTopology)) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (intRings S.totalTopology).obj)).unit.app (PresheafOfModules.tensorObj F.val G.val)

/-- The tensor product of two maps of sheaves of modules over the constant integers commutes with
the sheafification units of `tensorSheafificationUnitInt`. -/
theorem tensorSheaf_map_unit_int (S : SimplicialSiteSituation.{u})
    {F G F' G' : SheafOfModules.{u} (intRings S.totalTopology)} (f : F ⟶ F') (g : G ⟶ G')
    (U : S.totalCategoryᵒᵖ) (z : (PresheafOfModules.tensorObj F.val G.val).obj U) :
    Hom.app ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (intRingSheaf S.totalTopology))).map ((f, g) : (F, G) ⟶ (F', G'))).val U
      (Hom.app (tensorSheafificationUnitInt S F G) U z) =
    Hom.app (tensorSheafificationUnitInt S F' G') U
      (Hom.app (PresheafOfModules.tensorHom f.val g.val) U z) := by
  rw [Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map]
  exact (congrArg (fun k => Hom.app k U z)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (intRings S.totalTopology).obj)).unit.naturality
      (PresheafOfModules.tensorHom f.val g.val))).symm

/-- `tensorSheaf_map_unit_int` for the action of the tensor product on a map of the first
variable alone, in the curried spelling `((sheafTensor O).map f).app G`. -/
theorem tensorSheaf_mapLeft_unit_int (S : SimplicialSiteSituation.{u})
    {F F' : SheafOfModules.{u} (intRings S.totalTopology)} (f : F ⟶ F')
    (G : SheafOfModules.{u} (intRings S.totalTopology))
    (U : S.totalCategoryᵒᵖ) (z : (PresheafOfModules.tensorObj F.val G.val).obj U) :
    Hom.app (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (intRingSheaf S.totalTopology)).map f).app G).val U
      (Hom.app (tensorSheafificationUnitInt S F G) U z) =
    Hom.app (tensorSheafificationUnitInt S F' G) U
      (Hom.app (PresheafOfModules.tensorHom f.val (𝟙 G.val)) U z) :=
  (congrArg (fun k => Hom.app k U z)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (intRings S.totalTopology).obj)).unit.naturality
      (PresheafOfModules.tensorHom f.val (𝟙 G.val)))).symm

variable (S : SimplicialSiteSituation.{u})

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-! ### The generator of the constant integer sheaf -/

/-- The identification of the free abelian presheaf on a point with the constant integer presheaf
carries the basis element to `1`. -/
theorem pointFreeAbIso_hom_app_of (X : S.totalCategoryᵒᵖ) :
    AddCommGrpCat.Hom.hom ((pointFreeAbIso S).hom.app X)
        (FreeAbelianGroup.of (PUnit.unit : PUnit.{u+1})) = ULift.up 1 := by
  change AddCommGrpCat.Hom.hom (freeUnitIntegerIso'.{u}).hom
      (AddCommGrpCat.Hom.hom ((freeAbPresheafConstIso' S.totalCategory).hom.app X)
        (FreeAbelianGroup.of (PUnit.unit : PUnit.{u+1}))) = _
  change ((FreeAbelianGroup.uniqueEquiv PUnit.{u + 1}).trans AddEquiv.ulift.symm)
    (FreeAbelianGroup.of PUnit.unit) = _
  simp [FreeAbelianGroup.uniqueEquiv, FreeAbelianGroup.lift_apply_of]
  rfl

/-! ### The presheaf-level tail of the copower chain -/

/-- Sheafifying a map of presheaves of abelian groups commutes with the sheafification units, read
on a section. -/
private theorem sheafifyMap_toSheafify_app_apply {P Q : S.totalCategoryᵒᵖ ⥤ Ab.{u}} (η : P ⟶ Q)
    (V : S.totalCategoryᵒᵖ) (x : P.obj V) :
    AddCommGrpCat.Hom.hom ((sheafifyMap S.totalTopology η).app V)
        (AddCommGrpCat.Hom.hom ((toSheafify S.totalTopology P).app V) x) =
      AddCommGrpCat.Hom.hom ((toSheafify S.totalTopology Q).app V)
        (AddCommGrpCat.Hom.hom (η.app V) x) :=
  congrArg (fun k => AddCommGrpCat.Hom.hom (NatTrans.app k V) x)
    (toSheafify_naturality S.totalTopology η).symm

/-- The five presheaf-level steps of `unitTensorIsoAux`, inverted and composed: a morphism from
the sheaf being resolved to the objectwise tensor product of the free presheaf of modules on a
point with it. -/
def chainTail (F : Sheaf S.totalTopology Ab.{u}) :
    F.obj ⟶ (toPresheaf (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).obj
      (tensorObj (freeObj (pointPresheaf S)) (barRestrict S F)) :=
  (copowerPointIso S F.obj).inv ≫
    ((copowerPresheaf (pointPresheaf S)).mapIso (barCounitIso S F)).inv ≫
      (freeTensorCopowerIso (pointPresheaf S) (intPresheaf S) (barRestrict S F)).inv

/-- `chainTail` tensors a section with the generator of the free presheaf of modules on a
point. -/
theorem chainTail_app (F : Sheaf S.totalTopology Ab.{u}) (V : S.totalCategoryᵒᵖ)
    (x : F.obj.obj V) :
    AddCommGrpCat.Hom.hom ((chainTail S F).app V) x =
      ((ModuleCat.freeMk (R := ((intPresheaf S ⋙ forget₂ CommRingCat RingCat).obj V : Type u))
            (PUnit.unit : PUnit.{u+1}) ⊗ₜ[((intPresheaf S ⋙
              forget₂ CommRingCat RingCat).obj V : Type u)]
          (AddCommGrpCat.Hom.hom ((barCounitIso S F).inv.app V) x :
            ((barRestrict S F).obj V : Type u)) :
        ((tensorObj (freeObj (pointPresheaf S)) (barRestrict S F)).obj V : Type u))) := by
  change AddCommGrpCat.Hom.hom
      ((freeTensorCopowerIso (pointPresheaf S) (intPresheaf S) (barRestrict S F)).inv.app V)
      (AddCommGrpCat.Hom.hom
        ((copowerPresheafMap (pointPresheaf S) (barCounitIso S F).inv).app V)
        (AddCommGrpCat.Hom.hom ((copowerPointIso S F.obj).inv.app V) x)) = _
  rw [show AddCommGrpCat.Hom.hom ((copowerPointIso S F.obj).inv.app V) x
        = Finsupp.single (PUnit.unit : PUnit.{u+1}) x from rfl,
    copowerPresheafMap_app_single]
  exact freeTensorCopowerIsoApp_inv_single (pointPresheaf S) (intPresheaf S)
    (barRestrict S F) V _ _

/-- The inverse of the sheafification counit at a sheaf is the sheafification unit. -/
theorem sheafToPresheaf_counit_inv (F : Sheaf S.totalTopology Ab.{u}) :
    (sheafToPresheaf S.totalTopology Ab.{u}).map
        (@asIso _ _ _ _ _
          (isIso_sheafificationAdjunction_counit (J := S.totalTopology) (D := Ab.{u}) F)).inv =
      toSheafify S.totalTopology F.obj := by
  have h : toSheafify S.totalTopology F.obj ≫
      (sheafToPresheaf S.totalTopology Ab.{u}).map
        ((sheafificationAdjunction S.totalTopology Ab.{u}).counit.app F) = 𝟙 F.obj :=
    (sheafificationAdjunction S.totalTopology Ab.{u}).right_triangle_components F
  exact ((Iso.comp_hom_eq_id ((sheafToPresheaf S.totalTopology Ab.{u}).mapIso
    (@asIso _ _ _ _ _ (isIso_sheafificationAdjunction_counit (J := S.totalTopology)
      (D := Ab.{u}) F)))).mp h).symm

/-! ### The monoidal left unitor, conjugated -/

/-- The left unitor `𝒪 ⊗_𝒪 ℱ ≅ ℱ` of the monoidal structure
`SheafOfModules.monoidalCategorySheafTensor` on `Mod(ℤ)`, with the constant integer sheaf
identified with the structure sheaf, carried across the equivalence of abelian sheaves with
sheaves of modules over the constant sheaf of rings `ℤ`. -/
def monoidalUnitLeftIsoAux (F : Sheaf S.totalTopology Ab.{u}) :
    (moduleEquivalence S.totalTopology).functor.obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (intRingSheaf S.totalTopology)))).obj
          ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S),
            barModule S F)) ≅ F :=
  (moduleEquivalence S.totalTopology).functor.mapIso
      (((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).mapIso
          (totalIntegerModuleIsoUnit S)).app (barModule S F) ≪≫
        @MonoidalCategoryStruct.leftUnitor _ _
          (SheafOfModules.monoidalCategorySheafTensor
            (intRingSheaf S.totalTopology)).toMonoidalCategoryStruct (barModule S F)) ≪≫
    (moduleEquivalence S.totalTopology).counitIso.app F

/-- The inverse of the monoidal left unitor tensors a section with the unit section `1`. -/
theorem monoidalLeftUnitor_inv_app (F : Sheaf S.totalTopology Ab.{u}) (V : S.totalCategoryᵒᵖ)
    (x : (barModule S F).val.obj V) :
    Hom.app (@MonoidalCategoryStruct.leftUnitor _ _
        (SheafOfModules.monoidalCategorySheafTensor
          (intRingSheaf S.totalTopology)).toMonoidalCategoryStruct
        (barModule S F)).inv.val V x =
      Hom.app (tensorSheafificationUnitInt S
          (SheafOfModules.unit (intRings S.totalTopology)) (barModule S F)) V
        ((1 : (intRings S.totalTopology).obj.obj V) ⊗ₜ x) := by
  have h1 := congrArg Iso.inv (SheafOfModules.leftUnitor_sheafTensor_eq_iso
    (intRingSheaf S.totalTopology) (barModule S F))
  refine Eq.trans (congrArg (fun m => Hom.app (SheafOfModules.Hom.val m) V x) h1) ?_
  exact Stacks.SheafOfModules.tensorSheafUnitLeftIso_inv_app (intRingSheaf S.totalTopology).obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (intRingSheaf S.totalTopology)).property
    (barModule S F) V x

/-! ### The two presentations of the constant integer sheaf as a module -/

/-- The comparison of the two presentations of the constant integer sheaf as a sheaf of modules
over the constant sheaf of rings `ℤ`: the sheafification of the free presheaf of modules on a
point, and the structure sheaf. -/
def pointUnitComparison :
    (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
        (freeObj (pointPresheaf S)) ⟶
      SheafOfModules.unit (intRings S.totalTopology) :=
  (pointIntegerModuleIso S).inv ≫ (totalIntegerModuleIsoUnit S).hom

/-- `pointUnitComparison`, read on abelian sheaves: the two equivalence units cancel and only the
two presentations of the constant integer sheaf are left. -/
theorem functor_map_pointUnitComparison :
    (moduleEquivalence S.totalTopology).functor.map (pointUnitComparison S) =
      (pointIntegerIso S).hom ≫ (intSheafIsoConstantSheaf S.totalTopology).hom :=
  CategoryTheory.Equivalence.functor_map_unitIso_conj (moduleEquivalence S.totalTopology)
    (pointIntegerIso S).hom (intSheafIsoConstantSheaf S.totalTopology).hom

/-- The scalars of the constant sheaf of rings `ℤ` carry `1` to `1`. -/
theorem intSheafScalars_app_one (V : S.totalCategoryᵒᵖ) :
    AddCommGrpCat.Hom.hom ((intSheafScalars S.totalTopology).app V) (1 : ULift.{u} ℤ) =
      (1 : ((intRings S.totalTopology).obj.obj V : Type u)) := by
  change RingCat.Hom.hom ((intRingSheafScalars S.totalTopology).app V) (1 : ULift.{u} ℤ) = 1
  exact map_one _

/-- The identification of the constant sheaf `ℤ` with the structure sheaf is the sheafification
of the scalars. -/
theorem toSheafify_comp_intSheafIsoConstantSheaf :
    toSheafify S.totalTopology
          ((Functor.const S.totalCategoryᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ≫
        (sheafToPresheaf S.totalTopology Ab.{u}).map
          (intSheafIsoConstantSheaf S.totalTopology).hom =
      intSheafScalars S.totalTopology := by
  have h := ((sheafificationAdjunction S.totalTopology Ab.{u}).homEquiv
      ((Functor.const S.totalCategoryᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
      (intSheaf S.totalTopology)).apply_symm_apply (intSheafScalars S.totalTopology)
  rwa [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h

/-- The presentation of the constant integer sheaf as a sheafified free presheaf of modules on a
point carries the generator to `1`, read on abelian sheaves. -/
theorem pointIntegerIso_hom_app_unit_freeMk (V : S.totalCategoryᵒᵖ) :
    AddCommGrpCat.Hom.hom
        (((sheafToPresheaf S.totalTopology Ab.{u}).map (pointIntegerIso S).hom).app V)
        (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
            (freeObj (pointPresheaf S))) V
          (ModuleCat.freeMk
            (R := ((intPresheaf S ⋙ forget₂ CommRingCat RingCat).obj V : Type u))
            (PUnit.unit : PUnit.{u+1}))) =
      AddCommGrpCat.Hom.hom
        ((toSheafify S.totalTopology
          ((Functor.const S.totalCategoryᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app V)
        (1 : ULift.{u} ℤ) := by
  change AddCommGrpCat.Hom.hom ((sheafifyMap S.totalTopology (pointFreeAbIso S).hom).app V)
      (AddCommGrpCat.Hom.hom
        ((sheafifyMap S.totalTopology
          (freeObjToFreeAbIso (C := S.totalCategory) (pointPresheaf S)).hom).app V)
        (AddCommGrpCat.Hom.hom ((toSheafify S.totalTopology
            ((toPresheaf (intRingPresheaf S.totalCategory)).obj
              (freeObj (pointPresheaf S)))).app V)
          (ModuleCat.freeMk
            (R := ((intPresheaf S ⋙ forget₂ CommRingCat RingCat).obj V : Type u))
            (PUnit.unit : PUnit.{u+1})))) = _
  erw [sheafifyMap_toSheafify_app_apply S
      (freeObjToFreeAbIso (C := S.totalCategory) (pointPresheaf S)).hom V,
    freeObjToFreeAbIso_hom_app_freeMk, sheafifyMap_toSheafify_app_apply,
    pointFreeAbIso_hom_app_of]
  rfl

/-- The comparison of the two presentations of the constant integer sheaf carries the generator
of the free presheaf of modules on a point to the unit section `1`. -/
theorem pointUnitComparison_app_unit_freeMk (V : S.totalCategoryᵒᵖ) :
    Hom.app (pointUnitComparison S).val V
        (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
          (freeObj (pointPresheaf S))) V (ModuleCat.freeMk
            (R := ((intPresheaf S ⋙ forget₂ CommRingCat RingCat).obj V : Type u))
            (PUnit.unit : PUnit.{u+1}))) =
      (1 : ((intRings S.totalTopology).obj.obj V : Type u)) := by
  refine Eq.trans (congrArg (fun k => AddCommGrpCat.Hom.hom
    (NatTrans.app ((sheafToPresheaf S.totalTopology Ab.{u}).map k) V)
    (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
      (freeObj (pointPresheaf S))) V (ModuleCat.freeMk
            (R := ((intPresheaf S ⋙ forget₂ CommRingCat RingCat).obj V : Type u))
            (PUnit.unit : PUnit.{u+1})))) (functor_map_pointUnitComparison S)) ?_
  refine Eq.trans (congrArg (AddCommGrpCat.Hom.hom
    (((sheafToPresheaf S.totalTopology Ab.{u}).map
      (intSheafIsoConstantSheaf S.totalTopology).hom).app V))
    (pointIntegerIso_hom_app_unit_freeMk S V)) ?_
  refine Eq.trans (congrArg (fun k => AddCommGrpCat.Hom.hom (NatTrans.app k V)
    (1 : ULift.{u} ℤ)) (toSheafify_comp_intSheafIsoConstantSheaf S)) ?_
  exact intSheafScalars_app_one S V

/-! ### The five presheaf-level steps, sheafified -/

/-- The sheafification of `chainTail`, read on a section: the four inverted steps of
`unitTensorIsoAux` that live over the sheafification of the tensor product presheaf carry a
section to the sheafification-unit image of its tensor with the generator. -/
theorem chainTailSheafify (F : Sheaf S.totalTopology Ab.{u}) (V : S.totalCategoryᵒᵖ)
    (x : F.obj.obj V) :
    AddCommGrpCat.Hom.hom ((sheafifyMap S.totalTopology
        (freeTensorCopowerIso (pointPresheaf S) (intPresheaf S) (barRestrict S F)).inv).app V)
        (AddCommGrpCat.Hom.hom ((sheafifyMap S.totalTopology
            ((copowerPresheaf (pointPresheaf S)).map (barCounitIso S F).inv)).app V)
          (AddCommGrpCat.Hom.hom ((sheafifyMap S.totalTopology (copowerPointIso S F.obj).inv).app V)
            (AddCommGrpCat.Hom.hom
              (((sheafToPresheaf S.totalTopology Ab.{u}).map
                (@asIso _ _ _ _ _ (isIso_sheafificationAdjunction_counit
            (J := S.totalTopology) (D := Ab.{u}) F)).inv).app V) x))) =
      Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
          (tensorObj (freeObj (pointPresheaf S)) (barRestrict S F))) V
        ((ModuleCat.freeMk
              (R := ((intPresheaf S ⋙ forget₂ CommRingCat RingCat).obj V : Type u))
              (PUnit.unit : PUnit.{u+1}) ⊗ₜ[((intPresheaf S ⋙
                forget₂ CommRingCat RingCat).obj V : Type u)]
            (AddCommGrpCat.Hom.hom ((barCounitIso S F).inv.app V) x :
              ((barRestrict S F).obj V : Type u)) :
          ((tensorObj (freeObj (pointPresheaf S)) (barRestrict S F)).obj V : Type u))) := by
  erw [sheafToPresheaf_counit_inv, sheafifyMap_toSheafify_app_apply,
    sheafifyMap_toSheafify_app_apply, sheafifyMap_toSheafify_app_apply]
  exact congrArg (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
    (tensorObj (freeObj (pointPresheaf S)) (barRestrict S F))) V) (chainTail_app S F V x)

/-! ### The mixed tensor comparison, inverted, on sections -/

/-- The mixed tensor comparison of Stacks 0GMW, inverted, on the sheafification-unit image of a
pure tensor: it sheafifies the left factor. -/
theorem tensorSheafifySecondIso_inv_app_unit_tmul (F : Sheaf S.totalTopology Ab.{u})
    (V : S.totalCategoryᵒᵖ) (w : ((freeObj (pointPresheaf S)).obj V : Type u))
    (y : ((barRestrict S F).obj V : Type u)) :
    Hom.app (tensorSheafifySecondIso.{u, u, u, u, u} S.totalTopology (intUnit S)
          (freeObj (pointPresheaf S)) (barModule S F)).inv.val V
        (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
          (tensorObj (freeObj (pointPresheaf S)) (barRestrict S F))) V (w ⊗ₜ y)) =
      Hom.app (tensorSheafificationUnitInt S
          ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
            (freeObj (pointPresheaf S))) (barModule S F)) V
        (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
          (freeObj (pointPresheaf S))) V w ⊗ₜ y) := by
  refine Eq.trans (congrArg (fun k => Hom.app (SheafOfModules.Hom.val k) V
    (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
      (tensorObj (freeObj (pointPresheaf S)) (barRestrict S F))) V (w ⊗ₜ y)))
    (tensorSheafifySecondIso_inv.{u, u, u, u, u} S.totalTopology (intUnit S)
      (freeObj (pointPresheaf S)) (barModule S F))) ?_
  refine Eq.trans (congrArg
    (Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (intRingSheaf S.totalTopology)))).map
      (CategoryTheory.Prod.mkHom
        (𝟙 ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
          (freeObj (pointPresheaf S))))
        (sheafifyRestrictSheafIso.{u, u, u, u} S.totalTopology (intUnit S)
          (barModule S F)).hom)).val V)
    (tensorSheafifyComparison_unit_tmul.{u, u, u, u, u} S.totalTopology (intUnit S)
      (freeObj (pointPresheaf S)) (barRestrict S F) V w y)) ?_
  refine Eq.trans (tensorSheaf_map_unit_int S
    (𝟙 ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
      (freeObj (pointPresheaf S))))
    (sheafifyRestrictSheafIso.{u, u, u, u} S.totalTopology (intUnit S) (barModule S F)).hom
    V _) ?_
  exact congrArg (fun t => Hom.app (tensorSheafificationUnitInt S
      ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
        (freeObj (pointPresheaf S))) (barModule S F)) V
      (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
        (freeObj (pointPresheaf S))) V w ⊗ₜ t))
    (sheafifyRestrictSheafIso_unit_apply.{u, u, u, u} S.totalTopology (intUnit S)
      (barModule S F) V y)

/-- `pointTensorIso`, inverted. -/
theorem pointTensorIso_inv (F : Sheaf S.totalTopology Ab.{u}) :
    (pointTensorIso S F).inv =
      (tensorSheafifySecondIso.{u, u, u, u, u} S.totalTopology (intUnit S)
          (freeObj (pointPresheaf S)) (barModule S F)).inv ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (intRingSheaf S.totalTopology)))).map
          (CategoryTheory.Prod.mkHom (pointIntegerModuleIso S).inv (𝟙 (barModule S F))) :=
  rfl

/-- `pointTensorIso`, inverted, on the sheafification-unit image of a pure tensor. -/
theorem pointTensorIso_inv_app_unit_tmul (F : Sheaf S.totalTopology Ab.{u})
    (V : S.totalCategoryᵒᵖ) (w : ((freeObj (pointPresheaf S)).obj V : Type u))
    (y : ((barRestrict S F).obj V : Type u)) :
    Hom.app (pointTensorIso S F).inv.val V
        (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
          (tensorObj (freeObj (pointPresheaf S)) (barRestrict S F))) V (w ⊗ₜ y)) =
      Hom.app (tensorSheafificationUnitInt S
          ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
          (barModule S F)) V
        (Hom.app (pointIntegerModuleIso S).inv.val V
          (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
            (freeObj (pointPresheaf S))) V w) ⊗ₜ y) := by
  refine Eq.trans (congrArg (fun k => Hom.app (SheafOfModules.Hom.val k) V
    (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
      (tensorObj (freeObj (pointPresheaf S)) (barRestrict S F))) V (w ⊗ₜ y)))
    (pointTensorIso_inv S F)) ?_
  refine Eq.trans (congrArg
    (Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (intRingSheaf S.totalTopology)))).map
      (CategoryTheory.Prod.mkHom (pointIntegerModuleIso S).inv (𝟙 (barModule S F)))).val V)
    (tensorSheafifySecondIso_inv_app_unit_tmul S F V w y)) ?_
  exact tensorSheaf_map_unit_int S
    (pointIntegerModuleIso S).inv (𝟙 (barModule S F)) V _

/-! ### The two inverses, and the identification -/

/-- The inverse of the copower unit identification tensors a section with the image of the
generator of the free presheaf of modules on a point. -/
theorem unitTensorIsoAux_inv_app (F : Sheaf S.totalTopology Ab.{u}) (V : S.totalCategoryᵒᵖ)
    (x : F.obj.obj V) :
    AddCommGrpCat.Hom.hom
        (((sheafToPresheaf S.totalTopology Ab.{u}).map (unitTensorIsoAux S F).inv).app V) x =
      Hom.app (tensorSheafificationUnitInt S
          ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
          (barModule S F)) V
        (Hom.app (pointIntegerModuleIso S).inv.val V
          (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
            (freeObj (pointPresheaf S))) V
          (ModuleCat.freeMk
            (R := ((intPresheaf S ⋙ forget₂ CommRingCat RingCat).obj V : Type u))
            (PUnit.unit : PUnit.{u+1}))) ⊗ₜ
          (AddCommGrpCat.Hom.hom ((barCounitIso S F).inv.app V) x :
            ((barRestrict S F).obj V : Type u))) := by
  change Hom.app (pointTensorIso S F).inv.val V
      (AddCommGrpCat.Hom.hom ((sheafifyMap S.totalTopology
          (freeTensorCopowerIso (pointPresheaf S) (intPresheaf S) (barRestrict S F)).inv).app V)
        (AddCommGrpCat.Hom.hom ((sheafifyMap S.totalTopology
            ((copowerPresheaf (pointPresheaf S)).map (barCounitIso S F).inv)).app V)
          (AddCommGrpCat.Hom.hom ((sheafifyMap S.totalTopology (copowerPointIso S F.obj).inv).app V)
            (AddCommGrpCat.Hom.hom
              (((sheafToPresheaf S.totalTopology Ab.{u}).map
                (@asIso _ _ _ _ _ (isIso_sheafificationAdjunction_counit
            (J := S.totalTopology) (D := Ab.{u}) F)).inv).app V) x)))) = _
  refine Eq.trans (congrArg (Hom.app (pointTensorIso S F).inv.val V)
    (chainTailSheafify S F V x)) ?_
  exact pointTensorIso_inv_app_unit_tmul S F V _ _

/-- The inverse of the conjugated monoidal left unitor tensors a section with the unit section
`1`. -/
theorem monoidalUnitLeftIsoAux_inv_app (F : Sheaf S.totalTopology Ab.{u})
    (V : S.totalCategoryᵒᵖ) (x : F.obj.obj V) :
    AddCommGrpCat.Hom.hom
        (((sheafToPresheaf S.totalTopology Ab.{u}).map
          (monoidalUnitLeftIsoAux S F).inv).app V) x =
      Hom.app (tensorSheafificationUnitInt S
          ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
          (barModule S F)) V
        (Hom.app (totalIntegerModuleIsoUnit S).inv.val V
            (1 : ((intRings S.totalTopology).obj.obj V : Type u)) ⊗ₜ
          (AddCommGrpCat.Hom.hom ((barCounitIso S F).inv.app V) x :
            ((barRestrict S F).obj V : Type u))) := by
  change Hom.app (((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
        (totalIntegerModuleIsoUnit S).inv).app (barModule S F)).val V
      (Hom.app (@MonoidalCategoryStruct.leftUnitor _ _
          (SheafOfModules.monoidalCategorySheafTensor
            (intRingSheaf S.totalTopology)).toMonoidalCategoryStruct
          (barModule S F)).inv.val V
        (AddCommGrpCat.Hom.hom ((barCounitIso S F).inv.app V) x)) = _
  refine Eq.trans (congrArg (Hom.app
      (((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
      (totalIntegerModuleIsoUnit S).inv).app (barModule S F)).val V)
    (monoidalLeftUnitor_inv_app S F V _)) ?_
  exact tensorSheaf_mapLeft_unit_int S
    (totalIntegerModuleIsoUnit S).inv (barModule S F) V _

/-- The image of the generator under the first presentation of the constant integer sheaf is the
image of `1` under the second. -/
theorem pointIntegerModuleIso_inv_app_unit_freeMk (V : S.totalCategoryᵒᵖ) :
    Hom.app (pointIntegerModuleIso S).inv.val V
        (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
            (freeObj (pointPresheaf S))) V
          (ModuleCat.freeMk
            (R := ((intPresheaf S ⋙ forget₂ CommRingCat RingCat).obj V : Type u))
            (PUnit.unit : PUnit.{u+1}))) =
      Hom.app (totalIntegerModuleIsoUnit S).inv.val V
        (1 : ((intRings S.totalTopology).obj.obj V : Type u)) := by
  have hc : Hom.app (((totalIntegerModuleIsoUnit S).hom ≫
          (totalIntegerModuleIsoUnit S).inv)).val V
        (Hom.app (pointIntegerModuleIso S).inv.val V
          (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
            (freeObj (pointPresheaf S))) V
          (ModuleCat.freeMk
            (R := ((intPresheaf S ⋙ forget₂ CommRingCat RingCat).obj V : Type u))
            (PUnit.unit : PUnit.{u+1})))) =
      Hom.app (pointIntegerModuleIso S).inv.val V
        (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
            (freeObj (pointPresheaf S))) V
          (ModuleCat.freeMk
            (R := ((intPresheaf S ⋙ forget₂ CommRingCat RingCat).obj V : Type u))
            (PUnit.unit : PUnit.{u+1}))) :=
    congrArg (fun k : (moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S) ⟶
        (moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S) =>
      Hom.app (SheafOfModules.Hom.val k) V
        (Hom.app (pointIntegerModuleIso S).inv.val V
          (Hom.app (moduleSheafificationUnit.{u, u, u, u} S.totalTopology (intUnit S)
            (freeObj (pointPresheaf S))) V
          (ModuleCat.freeMk
            (R := ((intPresheaf S ⋙ forget₂ CommRingCat RingCat).obj V : Type u))
            (PUnit.unit : PUnit.{u+1})))))
      (totalIntegerModuleIsoUnit S).hom_inv_id
  refine Eq.trans hc.symm ?_
  exact congrArg (Hom.app (totalIntegerModuleIsoUnit S).inv.val V)
    (pointUnitComparison_app_unit_freeMk S V)

/-- The copower unit identification `ℤ ⊗_ℤ F ≅ F` is the monoidal left unitor of `Mod(ℤ)`,
conjugated by the equivalence of abelian sheaves with sheaves of modules over the constant sheaf
of rings `ℤ` and by the identification of the constant integer sheaf with the structure sheaf. -/
theorem unitTensorIsoAux_eq_monoidalUnitLeftIso (F : Sheaf S.totalTopology Ab.{u}) :
    unitTensorIsoAux S F = monoidalUnitLeftIsoAux S F := by
  have hinv : (unitTensorIsoAux S F).inv = (monoidalUnitLeftIsoAux S F).inv := by
    apply (sheafToPresheaf S.totalTopology Ab.{u}).map_injective
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext x
    refine Eq.trans (unitTensorIsoAux_inv_app S F V x) ?_
    refine Eq.trans ?_ (monoidalUnitLeftIsoAux_inv_app S F V x).symm
    exact congrArg (fun t => Hom.app (tensorSheafificationUnitInt S
        ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
        (barModule S F)) V
        (t ⊗ₜ (AddCommGrpCat.Hom.hom ((barCounitIso S F).inv.app V) x :
          ((barRestrict S F).obj V : Type u))))
      (pointIntegerModuleIso_inv_app_unit_freeMk S V)
  exact Iso.ext ((Iso.inv_eq_inv _ _).mp hinv)

/-- The unit identification `ℤ ⊗_ℤ - ≅ 𝟭` is the monoidal left unitor of `Mod(ℤ)`, at each
abelian sheaf. -/
theorem unitTensorIso_hom_app_eq (F : Sheaf S.totalTopology Ab.{u}) :
    (unitTensorIso S).hom.app F = (monoidalUnitLeftIsoAux S F).hom :=
  congrArg Iso.hom (unitTensorIsoAux_eq_monoidalUnitLeftIso S F)

end CategoryTheory.SimplicialSiteSituation

end
