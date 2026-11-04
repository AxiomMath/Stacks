module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsBaseChangeData
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsThickeningSequence

public import StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorBaseChange.CartesianSquare

/-!
# The direct image to `W` of `𝓕_A ⊗_A M`: the projection formula on sections

The projection formula at the structure sheaf, computed on sections, and its compatibility with
composition (`adjunctionTensorMap_unitObj_comp_reductionMapGen`, `adjunctionTensorMap_comp_eq`);
and the compatibility of the first tensor factors along the base
(`firstFactor_unitObj_naturality`, `tensorBaseChangeFirstIso_comp_naturality`).

See `StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorBaseChange` for the overview.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Prod TensorProduct

universe u

namespace Deformation.Artin.SectionsSheaf

/-! ### The projection formula at the structure sheaf, on sections -/

section Sections

open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.AlgebraicGeometry.AffineBaseChange

variable {W X X' : Scheme.{u}} (p : X ⟶ W) (β : X' ⟶ X) (F : W.Modules)

/-- The projection-formula map of `Stacks.AlgebraicGeometry.ProjectionFormula`, written as the
abstract `CategoryTheory.adjunctionTensorMap` of `p^* ⊣ p_*`. -/
theorem adjunctionTensorMap_eq_projectionFormulaMap (G : X.Modules) :
    adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction p)
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
        (comparisonNatTrans p.toLRSHom.toShHom) G F =
      Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap p G F :=
  ((Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_eq p G F).trans rfl).symm

/-- **The projection-formula map on pure tensors**: `x ⊗ y ↦ x ⊗ p^♯ y`. This is
`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_unit_tmul` in the
`CategoryTheory.adjunctionTensorMap` spelling. -/
theorem adjunctionTensorMap_val_app_tensorSheafUnit (G : X.Modules)
    (V : (TopologicalSpace.Opens W.carrier)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward p).obj G).val.obj V) (y : F.val.obj V) :
    PresheafOfModules.Hom.app (adjunctionTensorMap
        (Scheme.Modules.pullbackPushforwardAdjunction p)
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
        (comparisonNatTrans p.toLRSHom.toShHom) G F).val V
      (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := W.toRingedSpace.sheaf.obj)
              ((Scheme.Modules.pushforward p).obj G).val F.val)) V (x ⊗ₜ y)) =
    PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := X.toRingedSpace.sheaf.obj) G.val
              ((Scheme.Modules.pullback p).obj F).val))
        ((opensMap p.toLRSHom.toShHom).op.obj V)
        (x ⊗ₜ pullbackUnit p.toLRSHom.toShHom F V y) :=
  (congrArg (fun θ : (Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).obj
        ((Scheme.Modules.pushforward p).obj G, F) ⟶
        (Scheme.Modules.pushforward p).obj
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj
              (G, (Scheme.Modules.pullback p).obj F)) =>
      PresheafOfModules.Hom.app θ.val V
        (PresheafOfModules.Hom.app
          ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf).obj)).unit.app
              (PresheafOfModules.tensorObj (O := W.toRingedSpace.sheaf.obj)
                ((Scheme.Modules.pushforward p).obj G).val F.val)) V (x ⊗ₜ y)))
    (adjunctionTensorMap_eq_projectionFormulaMap p F G)).trans
  (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_unit_tmul p G F V x y)

/-- The comparison of the inverse images along two equal morphisms, at a reflexivity proof, is the
identity. -/
private theorem pullbackCongr_rfl_hom_app {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app M = 𝟙 _ :=
  rfl

/-- **The composition law of inverse images on the units**: the comparison
`β^* p^* 𝓕 ≅ (β ≫ p)^* 𝓕` carries the iterated pullback-unit image of a section of `𝓕` to its
pullback-unit image along `β ≫ p`. -/
theorem baseChangeSheafIsoGen_hom_val_app_unit (U : W.Opens) (y : F.val.obj (op U)) :
    PresheafOfModules.Hom.app (baseChangeSheafIsoGen p (β ≫ p) F β rfl).hom.val
        (op ((β ≫ p) ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction β).unit.app
          ((Scheme.Modules.pullback p).obj F)).val.app (op (p ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).val.app (op U) y)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (β ≫ p)).unit.app F).val.app (op U) y := by
  have key : (Scheme.Modules.pullbackComp β p).inv.app F ≫
      (baseChangeSheafIsoGen p (β ≫ p) F β rfl).hom = 𝟙 _ := by
    show (Scheme.Modules.pullbackComp β p).inv.app F ≫
      ((Scheme.Modules.pullbackComp β p).hom.app F ≫
        (Scheme.Modules.pullbackCongr (rfl : β ≫ p = β ≫ p)).hom.app F) = 𝟙 _
    rw [pullbackCongr_rfl_hom_app, Category.comp_id, Iso.inv_hom_id_app]
  rw [← Scheme.Modules.pullbackComp_inv_unit β p F U y]
  exact congrArg (fun φ => PresheafOfModules.Hom.app φ.val (op ((β ≫ p) ⁻¹ᵁ U))
    (((Scheme.Modules.pullbackPushforwardAdjunction (β ≫ p)).unit.app F).val.app (op U) y)) key

/-- **The canonical reduction on a product with a pulled-back section**: along `β`, the section
`r · p^♯ y` of `p^* 𝓕` goes to `β^♯ r · (β ≫ p)^♯ y`. -/
theorem reductionMapGen_val_app_smul (V : (TopologicalSpace.Opens W.carrier)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward p).obj (unitObj X)).val.obj V)
    (y : F.val.obj V) :
    PresheafOfModules.Hom.app ((Scheme.Modules.pushforward p).map
        (reductionMapGen p (β ≫ p) F β rfl)).val V
        (PresheafOfModules.Hom.app ((Scheme.Modules.pushforward p).map
          (tensorSheafUnitLeftIso X.toRingedSpace ((Scheme.Modules.pullback p).obj F)).hom).val V
          (PresheafOfModules.Hom.app
            ((PresheafOfModules.sheafificationAdjunction
                  (R := Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)
                  (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf).obj)).unit.app
                (PresheafOfModules.tensorObj (O := X.toRingedSpace.sheaf.obj) (unitObj X).val
                  ((Scheme.Modules.pullback p).obj F).val))
            ((opensMap p.toLRSHom.toShHom).op.obj V)
            (x ⊗ₜ pullbackUnit p.toLRSHom.toShHom F V y))) =
      HSMul.hSMul (α := (structureRingSheaf X'.toRingedSpace).obj.obj
            ((opensMap (β ≫ p).toLRSHom.toShHom).op.obj V))
        (sharp β.toLRSHom.toShHom ((opensMap p.toLRSHom.toShHom).op.obj V) x)
        (pullbackUnit (β ≫ p).toLRSHom.toShHom F V y) := by
  refine (congrArg (fun z => PresheafOfModules.Hom.app ((Scheme.Modules.pushforward p).map
      (reductionMapGen p (β ≫ p) F β rfl)).val V z)
    (tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul X.toRingedSpace
      ((Scheme.Modules.pullback p).obj F) ((opensMap p.toLRSHom.toShHom).op.obj V) x
      (pullbackUnit p.toLRSHom.toShHom F V y))).trans ?_
  refine (congrArg (fun z => PresheafOfModules.Hom.app
      (baseChangeSheafIsoGen p (β ≫ p) F β rfl).hom.val
      ((opensMap β.toLRSHom.toShHom).op.obj ((opensMap p.toLRSHom.toShHom).op.obj V)) z)
    (pullbackUnit_smul β.toLRSHom.toShHom ((Scheme.Modules.pullback p).obj F)
      ((opensMap p.toLRSHom.toShHom).op.obj V) x (pullbackUnit p.toLRSHom.toShHom F V y))).trans ?_
  refine ((PresheafOfModules.Hom.app (baseChangeSheafIsoGen p (β ≫ p) F β rfl).hom.val
      ((opensMap β.toLRSHom.toShHom).op.obj ((opensMap p.toLRSHom.toShHom).op.obj V))).hom.map_smul
      _ _).trans ?_
  exact congrArg (fun z : ((pullbackFunctor (β ≫ p).toLRSHom.toShHom).obj F).val.obj
          ((opensMap (β ≫ p).toLRSHom.toShHom).op.obj V) =>
        HSMul.hSMul (α := (structureRingSheaf X'.toRingedSpace).obj.obj
            ((opensMap (β ≫ p).toLRSHom.toShHom).op.obj V))
        (sharp β.toLRSHom.toShHom ((opensMap p.toLRSHom.toShHom).op.obj V) x) z)
    (baseChangeSheafIsoGen_hom_val_app_unit p β F V.unop y)

/-- The projection-formula map along `q`, after a map `f` into `q_* G` in the first factor, on pure
tensors: `x ⊗ y ↦ f x ⊗ q^♯ y`. -/
private theorem adjunctionTensorMap_map_prod_id_val_app {Y : Scheme.{u}} (q : Y ⟶ W)
    {H : W.Modules} (G : Y.Modules) (f : H ⟶ (Scheme.Modules.pushforward q).obj G)
    (V : (TopologicalSpace.Opens W.carrier)ᵒᵖ) (x : H.val.obj V) (y : F.val.obj V) :
    PresheafOfModules.Hom.app ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map (f ×ₘ 𝟙 F) ≫
        adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction q)
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩))
          (comparisonNatTrans q.toLRSHom.toShHom) G F).val V
      (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := W.toRingedSpace.sheaf.obj) H.val F.val)) V
        (x ⊗ₜ y)) =
      PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSpace.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSpace.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := Y.toRingedSpace.sheaf.obj) G.val
              ((Scheme.Modules.pullback q).obj F).val))
        ((opensMap q.toLRSHom.toShHom).op.obj V)
        (PresheafOfModules.Hom.app f.val V x ⊗ₜ pullbackUnit q.toLRSHom.toShHom F V y) :=
  (congrArg (fun z => PresheafOfModules.Hom.app
      (adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction q)
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩))
          (comparisonNatTrans q.toLRSHom.toShHom) G F).val V z)
    (tensorSheaf_map_unit_tmul W.toRingedSpace f (𝟙 F) V x y)).trans
  (adjunctionTensorMap_val_app_tensorSheafUnit q F G V _ y)

/-- **The projection-formula map along `β ≫ p` at the structure sheaf, after `β^♯`, on pure
tensors**: `x ⊗ y ↦ β^♯ x · (β ≫ p)^♯ y`. -/
theorem adjunctionTensorMap_structureUnitHom_val_app (V : (TopologicalSpace.Opens W.carrier)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward p).obj (unitObj X)).val.obj V)
    (y : F.val.obj V) :
    PresheafOfModules.Hom.app ((Scheme.Modules.pushforward (β ≫ p)).map
        (tensorSheafUnitLeftIso X'.toRingedSpace
          ((Scheme.Modules.pullback (β ≫ p)).obj F)).hom).val V
      (PresheafOfModules.Hom.app (adjunctionTensorMap
          (Scheme.Modules.pullbackPushforwardAdjunction (β ≫ p))
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
          (comparisonNatTrans (β ≫ p).toLRSHom.toShHom) (unitObj X') F).val V
        (PresheafOfModules.Hom.app ((Functor.uncurry.obj
                (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            ((Scheme.Modules.pushforward p).map (structureUnitHom β) ×ₘ 𝟙 F)).val V
          (PresheafOfModules.Hom.app
            ((PresheafOfModules.sheafificationAdjunction
                  (R := Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf)
                  (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf).obj)).unit.app
                (PresheafOfModules.tensorObj (O := W.toRingedSpace.sheaf.obj)
                  ((Scheme.Modules.pushforward p).obj (unitObj X)).val F.val)) V
            (x ⊗ₜ y)))) =
      HSMul.hSMul (α := (structureRingSheaf X'.toRingedSpace).obj.obj
            ((opensMap (β ≫ p).toLRSHom.toShHom).op.obj V))
        (sharp β.toLRSHom.toShHom ((opensMap p.toLRSHom.toShHom).op.obj V) x)
        (pullbackUnit (β ≫ p).toLRSHom.toShHom F V y) := by
  refine (congrArg (fun z => PresheafOfModules.Hom.app ((Scheme.Modules.pushforward (β ≫ p)).map
        (tensorSheafUnitLeftIso X'.toRingedSpace
          ((Scheme.Modules.pullback (β ≫ p)).obj F)).hom).val V z)
    (adjunctionTensorMap_map_prod_id_val_app F (β ≫ p) (unitObj X')
      ((Scheme.Modules.pushforward p).map (structureUnitHom β)) V x y)).trans ?_
  exact tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul X'.toRingedSpace
    ((Scheme.Modules.pullback (β ≫ p)).obj F) ((opensMap (β ≫ p).toLRSHom.toShHom).op.obj V)
    (sharp β.toLRSHom.toShHom ((opensMap p.toLRSHom.toShHom).op.obj V) x)
    (pullbackUnit (β ≫ p).toLRSHom.toShHom F V y)

/-- **The projection formula at the structure sheaf is compatible with restriction along `β`.**
For `β : X' → X` and `p : X → W`, `β^♯` followed by the projection-formula map along `β ≫ p` and
the left unitor is the projection-formula map along `p` and the left unitor, followed by the
direct image of the canonical reduction `p^* 𝓕 ⟶ β_* (β ≫ p)^* 𝓕`. Both sides are morphisms out
of a tensor product of sheaves, and both carry `x ⊗ y` to `β^♯ x · (β ≫ p)^♯ y`. -/
theorem adjunctionTensorMap_unitObj_comp_reductionMapGen :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((Scheme.Modules.pushforward p).map (structureUnitHom β) ×ₘ 𝟙 F) ≫
      adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction (β ≫ p))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
        (comparisonNatTrans (β ≫ p).toLRSHom.toShHom) (unitObj X') F ≫
      (Scheme.Modules.pushforward (β ≫ p)).map
        (tensorSheafUnitLeftIso X'.toRingedSpace ((Scheme.Modules.pullback (β ≫ p)).obj F)).hom =
    adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction p)
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
        (comparisonNatTrans p.toLRSHom.toShHom) (unitObj X) F ≫
      (Scheme.Modules.pushforward p).map
        (tensorSheafUnitLeftIso X.toRingedSpace ((Scheme.Modules.pullback p).obj F)).hom ≫
      (Scheme.Modules.pushforward p).map (reductionMapGen p (β ≫ p) F β rfl) :=
  PresheafOfModules.sheafification_hom_ext (PresheafOfModules.tensorObj_hom_ext fun V x y =>
    (adjunctionTensorMap_structureUnitHom_val_app p β F V x y).trans
      ((congrArg (fun z => PresheafOfModules.Hom.app ((Scheme.Modules.pushforward p).map
          (reductionMapGen p (β ≫ p) F β rfl)).val V
          (PresheafOfModules.Hom.app ((Scheme.Modules.pushforward p).map
            (tensorSheafUnitLeftIso X.toRingedSpace
              ((Scheme.Modules.pullback p).obj F)).hom).val V z))
        (adjunctionTensorMap_val_app_tensorSheafUnit p F (unitObj X) V x y)).trans
        (reductionMapGen_val_app_smul p β F V x y)).symm)

/-- The right-hand side of `adjunctionTensorMap_comp_eq` on a pure tensor. -/
theorem adjunctionTensorMap_comp_val_app (G : X'.Modules)
    (V : (TopologicalSpace.Opens W.carrier)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward (β ≫ p)).obj G).val.obj V) (y : F.val.obj V) :
    PresheafOfModules.Hom.app ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).map
          (𝟙 G ×ₘ (baseChangeSheafIsoGen p (β ≫ p) F β rfl).hom)).val
        ((opensMap β.toLRSHom.toShHom).op.obj ((opensMap p.toLRSHom.toShHom).op.obj V))
      (PresheafOfModules.Hom.app
          (adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction β)
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
            (comparisonNatTrans β.toLRSHom.toShHom) G ((Scheme.Modules.pullback p).obj F)).val
          ((opensMap p.toLRSHom.toShHom).op.obj V)
        (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf).obj)).unit.app
              (PresheafOfModules.tensorObj (O := X.toRingedSpace.sheaf.obj)
                ((Scheme.Modules.pushforward β).obj G).val ((Scheme.Modules.pullback p).obj F).val))
          ((opensMap p.toLRSHom.toShHom).op.obj V)
          (x ⊗ₜ pullbackUnit p.toLRSHom.toShHom F V y))) =
      PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf X'.toRingedSpace.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X'.toRingedSpace.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := X'.toRingedSpace.sheaf.obj) G.val
              ((Scheme.Modules.pullback (β ≫ p)).obj F).val))
        ((opensMap (β ≫ p).toLRSHom.toShHom).op.obj V)
        (x ⊗ₜ pullbackUnit (β ≫ p).toLRSHom.toShHom F V y) := by
  refine (congrArg (fun z => PresheafOfModules.Hom.app
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).map
          (𝟙 G ×ₘ (baseChangeSheafIsoGen p (β ≫ p) F β rfl).hom)).val
        ((opensMap β.toLRSHom.toShHom).op.obj ((opensMap p.toLRSHom.toShHom).op.obj V)) z)
    (adjunctionTensorMap_val_app_tensorSheafUnit β ((Scheme.Modules.pullback p).obj F) G
      ((opensMap p.toLRSHom.toShHom).op.obj V) x (pullbackUnit p.toLRSHom.toShHom F V y))).trans ?_
  refine (tensorSheaf_map_unit_tmul X'.toRingedSpace (𝟙 G)
      (baseChangeSheafIsoGen p (β ≫ p) F β rfl).hom
      ((opensMap β.toLRSHom.toShHom).op.obj ((opensMap p.toLRSHom.toShHom).op.obj V))
      x (pullbackUnit β.toLRSHom.toShHom ((Scheme.Modules.pullback p).obj F)
        ((opensMap p.toLRSHom.toShHom).op.obj V) (pullbackUnit p.toLRSHom.toShHom F V y))).trans ?_
  exact congrArg (fun z : ((pullbackFunctor (β ≫ p).toLRSHom.toShHom).obj F).val.obj
        ((opensMap (β ≫ p).toLRSHom.toShHom).op.obj V) =>
      PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X'.toRingedSpace.sheaf)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X'.toRingedSpace.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj (O := X'.toRingedSpace.sheaf.obj) G.val
            ((Scheme.Modules.pullback (β ≫ p)).obj F).val))
        ((opensMap (β ≫ p).toLRSHom.toShHom).op.obj V) (x ⊗ₜ z))
    (baseChangeSheafIsoGen_hom_val_app_unit p β F V.unop y)

/-- The right-hand side of `adjunctionTensorMap_comp_eq` on a pure tensor, as a composite. -/
theorem adjunctionTensorMap_comp_val_app' (G : X'.Modules)
    (V : (TopologicalSpace.Opens W.carrier)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pushforward β).obj G)).val.obj V)
    (y : F.val.obj V) :
    PresheafOfModules.Hom.app (adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction p)
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
          (comparisonNatTrans p.toLRSHom.toShHom) ((Scheme.Modules.pushforward β).obj G) F ≫
        (Scheme.Modules.pushforward p).map
          (adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction β)
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
              (comparisonNatTrans β.toLRSHom.toShHom) G ((Scheme.Modules.pullback p).obj F)) ≫
        (Scheme.Modules.pushforward p).map ((Scheme.Modules.pushforward β).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).map
            (𝟙 G ×ₘ (baseChangeSheafIsoGen p (β ≫ p) F β rfl).hom))) ≫
        (Scheme.Modules.pushforwardComp β p).hom.app
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).obj
              (G, (Scheme.Modules.pullback (β ≫ p)).obj F))).val V
      (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := W.toRingedSpace.sheaf.obj)
              ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pushforward β).obj G)).val
              F.val)) V
        (x ⊗ₜ y)) =
      PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf X'.toRingedSpace.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X'.toRingedSpace.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := X'.toRingedSpace.sheaf.obj) G.val
              ((Scheme.Modules.pullback (β ≫ p)).obj F).val))
        ((opensMap (β ≫ p).toLRSHom.toShHom).op.obj V)
        (x ⊗ₜ pullbackUnit (β ≫ p).toLRSHom.toShHom F V y) :=
  (congrArg (fun z => PresheafOfModules.Hom.app
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).map
          (𝟙 G ×ₘ (baseChangeSheafIsoGen p (β ≫ p) F β rfl).hom)).val
        ((opensMap β.toLRSHom.toShHom).op.obj ((opensMap p.toLRSHom.toShHom).op.obj V))
      (PresheafOfModules.Hom.app
          (adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction β)
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
            (comparisonNatTrans β.toLRSHom.toShHom) G ((Scheme.Modules.pullback p).obj F)).val
          ((opensMap p.toLRSHom.toShHom).op.obj V) z))
    (adjunctionTensorMap_val_app_tensorSheafUnit p F ((Scheme.Modules.pushforward β).obj G)
      V x y)).trans
  (adjunctionTensorMap_comp_val_app p β F G V x y)

/-- The left-hand side of `adjunctionTensorMap_comp_eq` on a pure tensor. -/
theorem adjunctionTensorMap_pushforwardComp_val_app (G : X'.Modules)
    (V : (TopologicalSpace.Opens W.carrier)ᵒᵖ)
    (x : ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pushforward β).obj G)).val.obj V)
    (y : F.val.obj V) :
    PresheafOfModules.Hom.app ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          ((Scheme.Modules.pushforwardComp β p).hom.app G ×ₘ 𝟙 F) ≫
        adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction (β ≫ p))
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
          (comparisonNatTrans (β ≫ p).toLRSHom.toShHom) G F).val V
      (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf W.toRingedSpace.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := W.toRingedSpace.sheaf.obj)
              ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pushforward β).obj G)).val
              F.val)) V
        (x ⊗ₜ y)) =
      PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf X'.toRingedSpace.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X'.toRingedSpace.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := X'.toRingedSpace.sheaf.obj) G.val
              ((Scheme.Modules.pullback (β ≫ p)).obj F).val))
        ((opensMap (β ≫ p).toLRSHom.toShHom).op.obj V)
        (x ⊗ₜ pullbackUnit (β ≫ p).toLRSHom.toShHom F V y) :=
  adjunctionTensorMap_map_prod_id_val_app F (β ≫ p) G
    ((Scheme.Modules.pushforwardComp β p).hom.app G) V x y

/-- **The projection formula along a composite.** For `β : X' → X` and `p : X → W`, the
projection-formula map along `β ≫ p`, read through `(β ≫ p)_* ≅ p_* β_*`, is the
projection-formula map along `p` at `β_* G`, followed by the direct image along `p` of the
projection-formula map along `β` and of the comparison `β^* p^* 𝓕 ≅ (β ≫ p)^* 𝓕` in the second
factor. Both sides carry `x ⊗ y` to `x ⊗ (β ≫ p)^♯ y`. -/
theorem adjunctionTensorMap_comp_eq (G : X'.Modules) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          ((Scheme.Modules.pushforwardComp β p).hom.app G ×ₘ 𝟙 F) ≫
        adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction (β ≫ p))
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
          (comparisonNatTrans (β ≫ p).toLRSHom.toShHom) G F =
      adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction p)
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩))
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
          (comparisonNatTrans p.toLRSHom.toShHom) ((Scheme.Modules.pushforward β).obj G) F ≫
        (Scheme.Modules.pushforward p).map
          (adjunctionTensorMap (Scheme.Modules.pullbackPushforwardAdjunction β)
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
              (comparisonNatTrans β.toLRSHom.toShHom) G ((Scheme.Modules.pullback p).obj F)) ≫
        (Scheme.Modules.pushforward p).map ((Scheme.Modules.pushforward β).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).map
            (𝟙 G ×ₘ (baseChangeSheafIsoGen p (β ≫ p) F β rfl).hom))) ≫
        (Scheme.Modules.pushforwardComp β p).hom.app
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).obj
              (G, (Scheme.Modules.pullback (β ≫ p)).obj F)) :=
  PresheafOfModules.sheafification_hom_ext (PresheafOfModules.tensorObj_hom_ext fun V x y =>
    (adjunctionTensorMap_pushforwardComp_val_app p β F G V x y).trans
      (adjunctionTensorMap_comp_val_app' p β F G V x y).symm)

end Sections

/-! ### The first tensor factor at the structure sheaf -/

section FirstFactor

open RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.AffineBaseChange

variable {Λ A : CommRingCat.{u}} (φ : Λ ⟶ A) {W X : Scheme.{u}} {g : W ⟶ Spec Λ}
  {π : X ⟶ Spec A} {p : X ⟶ W}

/-- **The adjoint transpose of the first tensor factor at `M = A`**, followed by `π^* Ã ≅ 𝒪_X`:
the inverse of [Stacks, Tag 01I9] followed by the direct image of `π^♯` and the identification of
the two composite direct images around the square. -/
theorem homEquiv_baseChangeNatTrans_unitObj (w : π ≫ Spec.map φ = p ≫ g) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((Scheme.Modules.pullback g).map (tildePushforwardIso φ (ModuleCat.of A A)).inv ≫
          (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
            ((tilde.functor A).obj (ModuleCat.of A A)) ≫
          (Scheme.Modules.pushforward p).map (pullbackUnitIso π).hom) =
      (tildePushforwardIso φ (ModuleCat.of A A)).inv ≫
        (Scheme.Modules.pushforward (Spec.map φ)).map (structureUnitHom π) ≫
          (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom.app
            (unitObj X) := by
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_baseChangeNatTrans]
  have hnat : (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom.app
          ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj (ModuleCat.of A A))) ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pushforward p).map (pullbackUnitIso π).hom) =
      (Scheme.Modules.pushforward (Spec.map φ)).map
          ((Scheme.Modules.pushforward π).map (pullbackUnitIso π).hom) ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom.app
          (unitObj X) :=
    ((Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom.naturality
      (pullbackUnitIso π).hom).symm
  have hunit : (Scheme.Modules.pushforward (Spec.map φ)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app
            ((tilde.functor A).obj (ModuleCat.of A A))) ≫
        (Scheme.Modules.pushforward (Spec.map φ)).map
          ((Scheme.Modules.pushforward π).map (pullbackUnitIso π).hom) =
      (Scheme.Modules.pushforward (Spec.map φ)).map (structureUnitHom π) :=
    (Functor.map_comp _ _ _).symm.trans
      (congrArg (fun z => (Scheme.Modules.pushforward (Spec.map φ)).map z)
        (unit_comp_map_pullbackUnitIso π))
  exact congrArg (fun z => (tildePushforwardIso φ (ModuleCat.of A A)).inv ≫ z)
    ((congrArg (fun z => (Scheme.Modules.pushforward (Spec.map φ)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app
            ((tilde.functor A).obj (ModuleCat.of A A))) ≫ z) hnat).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫
          (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom.app
            (unitObj X)) hunit)))

/-- The identification of the two composite direct images around a commutative square is the
identity on global sections. -/
theorem pushforwardSquareIso_hom_app_app_top {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g₀ : S' ⟶ S} (w₀ : g' ≫ f = f' ≫ g₀) (K : X'.Modules)
    (z : Γ(K, ⊤)) :
    Scheme.Modules.Hom.app
      ((Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w₀).hom.app K) ⊤ z =
      z := by
  simp only [Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  exact congrArg (fun φ : K.presheaf.obj (op ⊤) ⟶ K.presheaf.obj (op ⊤) => φ z)
    ((K.presheaf.congr_map (Subsingleton.elim _ (𝟙 _))).trans (K.presheaf.map_id _))

/-- `homEquiv_baseChangeNatTrans_unitObj` on the global section `a` of `Ã`: it is `π^♯ a`. -/
theorem homEquiv_baseChangeNatTrans_unitObj_app_top (w : π ≫ Spec.map φ = p ≫ g) (a : A) :
    ((tildePushforwardIso φ (ModuleCat.of A A)).inv ≫
        (Scheme.Modules.pushforward (Spec.map φ)).map (structureUnitHom π) ≫
          (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom.app
            (unitObj X)).val.app (op ⊤)
        ((tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A)) ⊤).hom a) =
      π.appTop ((tilde.toOpen (ModuleCat.of A A) ⊤).hom a) :=
  (pushforwardSquareIso_hom_app_app_top w (unitObj X) _).trans
    ((congrArg (fun z => ((structureUnitHom π).val.app (op ⊤)) z)
      (pushforwardTildeIso_inv_app_toOpen φ (ModuleCat.of A A) a)).trans
      (structureUnitHom_val_app_top π _))

/-- **The first tensor factor at the structure sheaf is natural in the base.** For a ring map
`ψ : A → A'`, a morphism `β : X' → X` over `Spec ψ`, and the two cartesian squares over `Spec φ`
and `Spec (φ ≫ ψ)`, the first tensor factor of `A'`, after `A → A'` and `π'^* Ã' ≅ 𝒪_{X'}`, is the
first tensor factor of `A`, after `π^* Ã ≅ 𝒪_X` and `β^♯`. Both are maps out of `g^*(A|_Λ)~`,
and their adjoint transposes send the global section `a` to `π'^♯ (ψ a) = β^♯ (π^♯ a)`. -/
theorem firstFactor_unitObj_naturality {A' : CommRingCat.{u}} (ψ : A ⟶ A') {X' : Scheme.{u}}
    {π' : X' ⟶ Spec A'} (β : X' ⟶ X) (w : π ≫ Spec.map φ = p ≫ g)
    (w' : π' ≫ Spec.map (φ ≫ ψ) = (β ≫ p) ≫ g) (hβπ : β ≫ π = π' ≫ Spec.map ψ)
    (v : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A) ⟶
      (ModuleCat.restrictScalars (φ ≫ ψ).hom).obj (ModuleCat.of A' A'))
    (hv : ∀ a, v.hom a = ψ a) :
    (Scheme.Modules.pullback g).map ((tilde.functor Λ).map v) ≫
        ((Scheme.Modules.pullback g).map (tildePushforwardIso (φ ≫ ψ) (ModuleCat.of A' A')).inv ≫
          (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w').app
            ((tilde.functor A').obj (ModuleCat.of A' A')) ≫
          (Scheme.Modules.pushforward (β ≫ p)).map (pullbackUnitIso π').hom) =
      ((Scheme.Modules.pullback g).map (tildePushforwardIso φ (ModuleCat.of A A)).inv ≫
          (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
            ((tilde.functor A).obj (ModuleCat.of A A)) ≫
          (Scheme.Modules.pushforward p).map (pullbackUnitIso π).hom) ≫
        (Scheme.Modules.pushforward p).map (structureUnitHom β) := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective ?_
  refine ((Adjunction.homEquiv_naturality_left _ _ _).trans
    (congrArg (fun z => (tilde.functor Λ).map v ≫ z)
      (homEquiv_baseChangeNatTrans_unitObj (φ ≫ ψ) w'))).trans ?_
  refine Eq.trans ?_ ((Adjunction.homEquiv_naturality_right _ _ _).trans
    (congrArg (fun z => z ≫ (Scheme.Modules.pushforward g).map
        ((Scheme.Modules.pushforward p).map (structureUnitHom β)))
      (homEquiv_baseChangeNatTrans_unitObj φ w))).symm
  refine ((tilde.adjunction (R := Λ)).homEquiv _ _).injective ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  have hsq : β.appTop (π.appTop ((tilde.toOpen (ModuleCat.of A A) ⊤).hom a)) =
      π'.appTop ((Spec.map ψ).appTop ((tilde.toOpen (ModuleCat.of A A) ⊤).hom a)) := by
    have e := congrArg
      (fun f : X' ⟶ Spec A => f.appTop ((tilde.toOpen (ModuleCat.of A A) ⊤).hom a)) hβπ
    simp only [Scheme.Hom.comp_appTop] at e
    exact e
  refine ((congrArg (fun z => ((tildePushforwardIso (φ ≫ ψ) (ModuleCat.of A' A')).inv ≫
        (Scheme.Modules.pushforward (Spec.map (φ ≫ ψ))).map (structureUnitHom π') ≫
          (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w').hom.app
            (unitObj X')).val.app (op ⊤) z)
      (tilde_functor_map_val_app_toOpen v a)).trans
    (homEquiv_baseChangeNatTrans_unitObj_app_top (φ ≫ ψ) w' (v.hom a))).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => ((structureUnitHom β).val.app (op ⊤)) z)
    (homEquiv_baseChangeNatTrans_unitObj_app_top φ w a)).symm
  refine Eq.trans ?_ (structureUnitHom_val_app_top β _).symm
  refine Eq.trans ?_ hsq.symm
  exact congrArg (fun z => π'.appTop z)
    ((congrArg (fun b => (tilde.toOpen (ModuleCat.of A' A') ⊤).hom b) (hv a)).trans
      (appTop_specMap_toOpen ψ a).symm)

/-- A composite of morphisms of modules, on sections. -/
theorem modulesHom_comp_app_apply {Y : Scheme.{u}} {M N K : Y.Modules} (f : M ⟶ N) (k : N ⟶ K)
    (U : Y.Opens) (z : Γ(M, U)) :
    Scheme.Modules.Hom.app (f ≫ k) U z =
      Scheme.Modules.Hom.app k U (Scheme.Modules.Hom.app f U z) :=
  rfl

/-- **The base-change morphism on pullback-unit images of global sections**: for a commutative
square `g' ≫ f = f' ≫ g₀`, the base-change morphism `g₀^* f_* N ⟶ f'_* g'^* N` carries the
pullback along `g₀` of a global section of `f_* N` to its pullback along `g'`. -/
theorem baseChangeNatTrans_app_unit_app_top {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g₀ : S' ⟶ S} (w₀ : g' ≫ f = f' ≫ g₀) (N : X.Modules)
    (z : Γ((Scheme.Modules.pushforward f).obj N, ⊤)) :
    Scheme.Modules.Hom.app
        ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w₀).app N) ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g₀).unit.app
          ((Scheme.Modules.pushforward f).obj N)) ⊤ z) =
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app N) ⊤
        z : Γ((Scheme.Modules.pullback g').obj N, ⊤)) := by
  have e := congrArg (fun k : (Scheme.Modules.pushforward f).obj N ⟶
      (Scheme.Modules.pushforward g₀).obj
        ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj N)) =>
      Scheme.Modules.Hom.app k ⊤ z) (unit_comp_pushforward_baseChangeNatTrans w₀ N)
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at e
  exact e.trans (pushforwardSquareIso_hom_app_app_top w₀ _ _)

/-- **The first tensor factor on pullback-unit images of global sections**: the comparison
`g^*(N|_Λ)~ ⟶ p_* π^* Ñ` carries the pullback along `g` of the global section `n` of `(N|_Λ)~`
to the pullback along `π` of the global section `n` of `Ñ`. -/
theorem firstFactor_app_unit_app_top (w : π ≫ Spec.map φ = p ≫ g) (N : ModuleCat.{u} A)
    (n : N) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map (tildePushforwardIso φ N).inv ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
          ((tilde.functor A).obj N)) ⊤
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((tilde.functor Λ).obj ((ModuleCat.restrictScalars φ.hom).obj N))) ⊤
        ((tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj N) ⊤).hom n)) =
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app
        ((tilde.functor A).obj N)) ⊤ ((tilde.toOpen N ⊤).hom n) :
      Γ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj N), ⊤)) := by
  have e₁ : Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map
        (tildePushforwardIso φ N).inv) ⊤
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((tilde.functor Λ).obj ((ModuleCat.restrictScalars φ.hom).obj N))) ⊤
        ((tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj N) ⊤).hom n)) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pushforward (Spec.map φ)).obj ((tilde.functor A).obj N))) ⊤
        (Scheme.Modules.Hom.app (tildePushforwardIso φ N).inv ⊤
          ((tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj N) ⊤).hom n)) :=
    Scheme.Modules.unit_app_val_app_naturality g (tildePushforwardIso φ N).inv ⊤
      ((tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj N) ⊤).hom n)
  have e₃ : Scheme.Modules.Hom.app (tildePushforwardIso φ N).inv ⊤
        ((tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj N) ⊤).hom n) =
      ((tilde.toOpen N ⊤).hom n : Γ((tilde.functor A).obj N, ⊤)) :=
    pushforwardTildeIso_inv_app_toOpen φ N n
  refine (modulesHom_comp_app_apply _ _ ⊤ _).trans ?_
  rw [e₁, baseChangeNatTrans_app_unit_app_top w, e₃]

/-- The adjoint transpose along `~ ⊣ Γ`, on elements. -/
theorem tilde_adjunction_homEquiv_apply {R : CommRingCat.{u}} {M : ModuleCat.{u} R}
    {N : (Spec R).Modules} (f : (tilde.functor R).obj M ⟶ N) (m : M) :
    (tilde.adjunction.homEquiv M N f).hom m = f.val.app (op ⊤) ((tilde.toOpen M ⊤).hom m) :=
  rfl

/-- The adjoint transpose along `g^* ⊣ g_*`, on global sections. -/
theorem homEquiv_val_app_top {W Y : Scheme.{u}} (g : W ⟶ Y) {N : Y.Modules} {K : W.Modules}
    (f : (Scheme.Modules.pullback g).obj N ⟶ K) (z : N.val.obj (op ⊤)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ f).val.app (op ⊤) z =
      f.val.app (op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).val.app (op ⊤) z) :=
  congrArg (fun k : N ⟶ (Scheme.Modules.pushforward g).obj K => k.val.app (op ⊤) z)
    (Adjunction.homEquiv_unit _ _ _ f)

/-- **The first tensor factor along a composite of base rings.** For `Λ → A' → A`, a cartesian
square over `Spec A' → Spec Λ` and one over `Spec A → Spec A'`, the first tensor factor of the
pasted square, after the identity `(M|_{A'})|_Λ = M|_Λ`, is the first tensor factor of the outer
square at `M|_{A'}` followed by the direct image of the first tensor factor of the inner square.
Both are maps out of a pullback of an associated sheaf, and on the pullback of the global section
`m` both give the pullback of `m` along `π`. -/
theorem tensorBaseChangeFirstIso_comp_naturality {A' : CommRingCat.{u}} (φ₀ : Λ ⟶ A')
    (φ₁ : A' ⟶ A) {X' : Scheme.{u}} {π' : X' ⟶ Spec A'} {p' : X' ⟶ W}
    (h₀ : IsPullback π' p' (Spec.map φ₀) g) {i : X ⟶ X'} (hsq : IsPullback π i (Spec.map φ₁) π')
    (h' : IsPullback π (i ≫ p') (Spec.map (φ₀ ≫ φ₁)) g) (M : ModuleCat.{u} A) :
    (Scheme.Modules.pullback g).map ((tilde.functor Λ).map
        (ModuleCat.restrictScalarsComp'App φ₀.hom φ₁.hom (φ₀ ≫ φ₁).hom rfl M).inv) ≫
      (tensorBaseChangeFirstIso (φ₀ ≫ φ₁) h' M).hom =
    (tensorBaseChangeFirstIso φ₀ h₀ ((ModuleCat.restrictScalars φ₁.hom).obj M)).hom ≫
      (Scheme.Modules.pushforward p').map
        ((Scheme.Modules.pullback π').map (tildePushforwardIso φ₁ M).inv ≫
          (affineBaseChangeIsoGen φ₁ π' π i hsq ((tilde.functor A).obj M)).hom) ≫
      (Scheme.Modules.pushforwardComp i p').hom.app
        ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M)) := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective ?_
  refine ((tilde.adjunction (R := Λ)).homEquiv _ _).injective ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  refine (tilde_adjunction_homEquiv_apply _ m).trans ?_
  refine Eq.trans ?_ (tilde_adjunction_homEquiv_apply _ m).symm
  refine (homEquiv_val_app_top g _ _).trans ?_
  refine Eq.trans ?_ (homEquiv_val_app_top g _ _).symm
  refine (congrArg (fun z => Scheme.Modules.Hom.app
      (tensorBaseChangeFirstIso (φ₀ ≫ φ₁) h' M).hom ⊤ z)
    (Scheme.Modules.unit_app_val_app_naturality g
      ((tilde.functor Λ).map
        (ModuleCat.restrictScalarsComp'App φ₀.hom φ₁.hom (φ₀ ≫ φ₁).hom rfl M).inv) ⊤
      ((tilde.toOpen ((ModuleCat.restrictScalars φ₀.hom).obj
        ((ModuleCat.restrictScalars φ₁.hom).obj M)) ⊤).hom m))).trans ?_
  refine (congrArg (fun z => Scheme.Modules.Hom.app
      (tensorBaseChangeFirstIso (φ₀ ≫ φ₁) h' M).hom ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((tilde.functor Λ).obj ((ModuleCat.restrictScalars (φ₀ ≫ φ₁).hom).obj M))) ⊤ z))
    (tilde_functor_map_val_app_toOpen
      (ModuleCat.restrictScalarsComp'App φ₀.hom φ₁.hom (φ₀ ≫ φ₁).hom rfl M).inv m)).trans ?_
  refine (firstFactor_app_unit_app_top (φ₀ ≫ φ₁) h'.w M m).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => Scheme.Modules.Hom.app
      ((Scheme.Modules.pushforwardComp i p').hom.app
        ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M))) ⊤
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullback π').map (tildePushforwardIso φ₁ M).inv ≫
          (affineBaseChangeIsoGen φ₁ π' π i hsq ((tilde.functor A).obj M)).hom) ⊤ z))
    (firstFactor_app_unit_app_top φ₀ h₀.w ((ModuleCat.restrictScalars φ₁.hom).obj M) m)).symm
  exact (firstFactor_app_unit_app_top φ₁ hsq.w M m).symm

end FirstFactor

end Deformation.Artin.SectionsSheaf

end
