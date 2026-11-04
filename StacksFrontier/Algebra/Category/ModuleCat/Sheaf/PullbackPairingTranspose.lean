module

public import
  StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackRestrictionUnderlying
public import
  StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.InverseImageCounitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorBilinEquivPairingApp

/-!
# Underlying transposes for pullback of sheaves of modules

The pairing of an adjoint transpose is a transpose for the underlying morphism of topoi.
This evaluates base change of the pairing without an explicit counit. The scalar-extension
unit is kept as a named morphism, so callers can cancel it on sections without identifying
two presentations of an object inside a direct-image functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf MonoidalCategory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
  Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w w' v u v' u'

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

omit [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The unit of inverse image for modules has the underlying topos unit. -/
theorem moduleSheaf_map_inverseImage_unit
    (M : SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((inverseImageAdjDirectImageModules f.toToposHom
          (Tensor.ringSheaf Y.O)).unit.app M) =
      f.toToposHom.adj.unit.app (moduleSheaf (Tensor.ringSheaf Y.O) M) := by
  have hu : (inverseImageAdjDirectImageModules f.toToposHom
      (Tensor.ringSheaf Y.O)).unit.app M =
      toposModulesHomEquiv f.toToposHom (Tensor.ringSheaf Y.O) M
        ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj M) (𝟙 _) := rfl
  refine (congrArg (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map hu).trans ?_
  refine (moduleSheafFunctor_map_toposModulesHomEquiv f.toToposHom
    (Tensor.ringSheaf Y.O) (𝟙 _)).trans ?_
  refine (congrArg (f.toToposHom.adj.homEquiv _ _)
    ((moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
      (Tensor.ringSheaf Y.O))).map_id _)).trans ?_
  exact f.toToposHom.adj.homEquiv_id _

/-- Underlying the composite unit is the transpose of the scalar-extension unit. -/
theorem moduleSheaf_map_pullback_unit
    (M : SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app M) =
      f.toToposHom.adj.unit.app (moduleSheaf (Tensor.ringSheaf Y.O) M) ≫
        f.toToposHom.pushforward.map
          ((moduleSheafFunctor (commRingSheaf X.J (inverseImageStructureCommRing f)
              (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj M))) := by
  refine (congrArg (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
    (Adjunction.comp_unit_app
      (inverseImageAdjDirectImageModules f.toToposHom (Tensor.ringSheaf Y.O))
      (pullbackExtendAdj f) M)).trans ?_
  refine ((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map_comp _ _).trans ?_
  exact congrArg₂ (fun a b ↦ a ≫ b)
    (moduleSheaf_map_inverseImage_unit f M)
    (moduleSheafFunctor_map_directImageModules_map f.toToposHom
      (Tensor.ringSheaf Y.O) _)

/-- Forgetting a module transpose gives the topos transpose of its scalar-extension part. -/
theorem moduleSheaf_map_pullback_transpose
    (M : SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (h : f.pullbackModules.obj M ⟶ N) :
    (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app M ≫ (pushforwardModules f).map h) =
      f.toToposHom.adj.homEquiv _ _
        ((moduleSheafFunctor (commRingSheaf X.J (inverseImageStructureCommRing f)
              (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj M)) ≫
          (moduleSheafFunctor (Tensor.ringSheaf X.O)).map h) := by
  rw [(moduleSheafFunctor (Tensor.ringSheaf Y.O)).map_comp,
    moduleSheaf_map_pullback_unit]
  change (_ ≫ f.toToposHom.pushforward.map _) ≫
    f.toToposHom.pushforward.map _ = _
  rw [moduleSheafFunctor_map_restrictScalars_map]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k ↦ f.toToposHom.adj.unit.app
    (moduleSheaf (Tensor.ringSheaf Y.O) M) ≫ k)
    (f.toToposHom.pushforward.map_comp _ _).symm).trans ?_
  exact (f.toToposHom.adj.homEquiv_unit _ _ _).symm

/-- The pairing of a module transpose is itself a topos transpose. -/
theorem pairing_pullback_transpose
    (A B : SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (M : SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (t : A.val ⊗ B.val ⟶ M.val)
    (h : f.pullbackModules.obj M ⟶ N) :
    pairingOfTensorHom (hO := (Tensor.ringSheaf Y.O).property)
        (t ≫ (((pullbackAdjPushforwardModules f).unit.app M ≫
          (pushforwardModules f).map h).val)) =
      f.toToposHom.adj.homEquiv _ _
        (f.toToposHom.inverseImage.map
            (pairingOfTensorHom (hO := (Tensor.ringSheaf Y.O).property) t) ≫
          ((moduleSheafFunctor (commRingSheaf X.J (inverseImageStructureCommRing f)
              (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj M)) ≫
            (moduleSheafFunctor (Tensor.ringSheaf X.O)).map h)) := by
  refine (pairingOfTensorHom_comp t
    ((pullbackAdjPushforwardModules f).unit.app M ≫
      (pushforwardModules f).map h)).trans ?_
  refine (congrArg (fun k ↦
    pairingOfTensorHom (hO := (Tensor.ringSheaf Y.O).property) t ≫ k)
    (moduleSheaf_map_pullback_transpose f M N h)).trans ?_
  exact (f.toToposHom.adj.homEquiv_naturality_left _ _).symm

/-- The pairing transpose written in unit--direct-image form. -/
theorem pairing_pullback_transpose_unit
    (A B M : SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (t : A.val ⊗ B.val ⟶ M.val)
    (h : f.pullbackModules.obj M ⟶ N) :
    pairingOfTensorHom (hO := (Tensor.ringSheaf Y.O).property)
        (t ≫ (((pullbackAdjPushforwardModules f).unit.app M ≫
          (pushforwardModules f).map h).val)) =
      f.toToposHom.adj.unit.app _ ≫ f.toToposHom.pushforward.map
        (f.toToposHom.inverseImage.map
            (pairingOfTensorHom (hO := (Tensor.ringSheaf Y.O).property) t) ≫
          ((moduleSheafFunctor (commRingSheaf X.J (inverseImageStructureCommRing f)
              (isSheaf_inverseImageStructureCommRing f))).map
            ((pullbackExtendAdj f).unit.app
              ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj M)) ≫
            (moduleSheafFunctor (Tensor.ringSheaf X.O)).map h)) :=
  (pairing_pullback_transpose f A B M N t h).trans
    (f.toToposHom.adj.homEquiv_unit _ _ _)

/-- The underlying scalar-extension unit in the pullback of a module. -/
def scalarUnitMap (M : SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (moduleSheafFunctor (commRingSheaf X.J (inverseImageStructureCommRing f)
      (isSheaf_inverseImageStructureCommRing f))).obj
        ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj M) ⟶
      moduleSheaf (Tensor.ringSheaf X.O) (f.pullbackModules.obj M) :=
  (moduleSheafFunctor (commRingSheaf X.J (inverseImageStructureCommRing f)
    (isSheaf_inverseImageStructureCommRing f))).map
      ((pullbackExtendAdj f).unit.app
        ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj M))

instance scalarUnitMap_isIso [IsIso f.fSharpInverseImage]
    (M : SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) : IsIso (scalarUnitMap f M) := by
  let := isIso_pullbackExtendAdj_unit_app f
    ((inverseImageModules f.toToposHom (Tensor.ringSheaf Y.O)).obj M)
  unfold scalarUnitMap
  exact (moduleSheafFunctor (commRingSheaf X.J (inverseImageStructureCommRing f)
    (isSheaf_inverseImageStructureCommRing f))).map_isIso _

/-- Evaluate the base change of the pairing of a module transpose without leaving a counit. -/
theorem pairingApp_pullbackTensorBilinEquiv_tensorTranspose [IsIso f.fSharpInverseImage]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    (A B M : SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (N : SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (t : A.val ⊗ B.val ⟶ M.val) (h : f.pullbackModules.obj M ⟶ N)
    (W : X.Cᵒᵖ) (a : (f.pullbackModules.obj A).val.obj W)
    (b : (f.pullbackModules.obj B).val.obj W) :
    pairingApp (Tensor.ringSheaf X.O)
      (pullbackTensorBilinEquiv f A B N
        ⟨pairingOfTensorHom (hO := (Tensor.ringSheaf Y.O).property)
          (t ≫ (((pullbackAdjPushforwardModules f).unit.app M ≫
            (pushforwardModules f).map h).val)),
          isBilinearPairing_pairingOfTensorHom
            (hO := (Tensor.ringSheaf Y.O).property) _⟩).1 W a b =
      (sectionsFunctor X.J W).map
        (f.toToposHom.inverseImage.map
            (pairingOfTensorHom (hO := (Tensor.ringSheaf Y.O).property) t) ≫
          (scalarUnitMap f M ≫ (moduleSheafFunctor (Tensor.ringSheaf X.O)).map h))
        (Functor.prodObjMk (P := f.toToposHom.inverseImage ⋙ sectionsFunctor X.J W)
          ((sectionsFunctor X.J W).map (inv (scalarUnitMap f A)) a)
          ((sectionsFunctor X.J W).map (inv (scalarUnitMap f B)) b)) := by
  refine (pairingApp_pullbackTensorBilinEquiv f A B N _ W a b).trans ?_
  exact map_prodComparisonInv_map_comp_counit_prodObjMk f.toToposHom.adj
    (sectionsFunctor X.J W) _ _ _ _ _
    (pairing_pullback_transpose_unit f A B M N t h) _ _

end Stacks.SheafOfModules

end
