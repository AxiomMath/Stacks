module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules

/-!
# The direct image of sheaves of modules along a continuous functor of sites is restriction

Let `G : C ⥤ D` be a continuous functor of sites, `δ : R ⟶ O₂` a morphism of sheaves of rings on
`D` and `ν : O₁ ⟶ G^{-1}R` one on `C`. Restricting scalars along `δ`, transporting sheaves of
modules along the restriction functor `G.sheafPushforwardContinuous` (the construction
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor` of Stacks 03D1 and 03D2) and restricting
scalars along `ν` is Mathlib's `CategoryTheory.SheafOfModules.pushforward` along `G` over the
single morphism of sheaves of rings `O₁ ⟶ G_*O₂` composed of `ν`, the comparison
`Stacks.Sheaves.ToposPullback.restrictionRingIso` and `δ`. The comparison is the identity on
sections.

## Main definitions

* `Stacks.Sheaves.ToposPullback.restrictionPushforwardRingMap`: the morphism of sheaves of rings
  `O₁ ⟶ G_*O₂` composed of `ν`, `restrictionRingIso` and `δ`.
* `Stacks.Sheaves.ToposPullback.pushforwardRestrictionModuleHom` and
  `Stacks.Sheaves.ToposPullback.pushforwardRestrictionModuleHomInv`: the comparison on the
  sections over one object, as a linear map in each direction.

## Main results

* `Stacks.Sheaves.ToposPullback.pushforwardRestrictionModulesIso`: the comparison, as an
  isomorphism of functors.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor Opposite CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K] (R O₂ : Sheaf K RingCat.{ww}) (δ : R ⟶ O₂)
  (O₁ : Sheaf J RingCat.{ww})
  (ν : O₁ ⟶ pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) R)

/-- **The scalar map of the comparison**: the morphism of sheaves of rings `O₁ ⟶ G_*O₂` composed
of `ν`, the identification `restrictionRingIso` of the transported ring structure with the
original one, and the direct image of `δ` along `G`. -/
def restrictionPushforwardRingMap :
    O₁ ⟶ (G.sheafPushforwardContinuous RingCat.{ww} J K).obj O₂ :=
  ν ≫ (restrictionRingIso J K G R).hom ≫
    (G.sheafPushforwardContinuous RingCat.{ww} J K).map δ

/-- **The comparison on the sections over one object**: the identity map of sections, as a
morphism of `O₁(X)`-modules. -/
def pushforwardRestrictionModuleHom (M : SheafOfModules.{ww} O₂) (X : Cᵒᵖ) :
    ((SheafOfModules.restrictScalars ν).obj
        ((pullbackModuleFunctor J (G.sheafPushforwardContinuous (Type ww) J K) R).obj
          ((SheafOfModules.restrictScalars δ).obj M))).val.obj X ⟶
      ((SheafOfModules.pushforward.{ww}
        (restrictionPushforwardRingMap J K G R O₂ δ O₁ ν)).obj M).val.obj X :=
  letI : Module ((pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) R).obj.obj X)
      ((pullbackModuleAb J (G.sheafPushforwardContinuous (Type ww) J K) R
        ((SheafOfModules.restrictScalars δ).obj M)).obj X) :=
    moduleObjModule R ((SheafOfModules.restrictScalars δ).obj M)
      (G.sheafPushforwardContinuous (Type ww) J K ⋙ Sheaf.sectionsFunctor J X)
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (ν.hom.app X).hom).obj (ModuleCat.of
      ((pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) R).obj.obj X)
      ((pullbackModuleAb J (G.sheafPushforwardContinuous (Type ww) J K) R
        ((SheafOfModules.restrictScalars δ).obj M)).obj X)))
    (Y := (ModuleCat.restrictScalars
      ((restrictionPushforwardRingMap J K G R O₂ δ O₁ ν).hom.app X).hom).obj
      (M.val.obj (G.op.obj X)))
    { toFun := id
      map_add' := fun x y ↦ Sheaf.sectionsFunctor_map_moduleAddHom O₂ M (G.op.obj X) x y
      map_smul' := fun r x ↦ (moduleSMulObj_restrictScalars δ M
        (G.sheafPushforwardContinuous (Type ww) J K ⋙ Sheaf.sectionsFunctor J X)
        ((ν.hom.app X) r) x).trans
        (Sheaf.sectionsFunctor_map_moduleSMulHom O₂ M (G.op.obj X) _ x) }

/-- The identity map of sections over one object, as a morphism of `O₁(X)`-modules from the
pushforward to the transported module. -/
def pushforwardRestrictionModuleHomInv (M : SheafOfModules.{ww} O₂) (X : Cᵒᵖ) :
    ((SheafOfModules.pushforward.{ww}
          (restrictionPushforwardRingMap J K G R O₂ δ O₁ ν)).obj M).val.obj X ⟶
      ((SheafOfModules.restrictScalars ν).obj
        ((pullbackModuleFunctor J (G.sheafPushforwardContinuous (Type ww) J K) R).obj
          ((SheafOfModules.restrictScalars δ).obj M))).val.obj X :=
  letI : Module ((pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) R).obj.obj X)
      ((pullbackModuleAb J (G.sheafPushforwardContinuous (Type ww) J K) R
        ((SheafOfModules.restrictScalars δ).obj M)).obj X) :=
    moduleObjModule R ((SheafOfModules.restrictScalars δ).obj M)
      (G.sheafPushforwardContinuous (Type ww) J K ⋙ Sheaf.sectionsFunctor J X)
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (ν.hom.app X).hom).obj (ModuleCat.of
      ((pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) R).obj.obj X)
      ((pullbackModuleAb J (G.sheafPushforwardContinuous (Type ww) J K) R
        ((SheafOfModules.restrictScalars δ).obj M)).obj X)))
    (X := (ModuleCat.restrictScalars
      ((restrictionPushforwardRingMap J K G R O₂ δ O₁ ν).hom.app X).hom).obj
      (M.val.obj (G.op.obj X)))
    { toFun := id
      map_add' := fun x y ↦ (Sheaf.sectionsFunctor_map_moduleAddHom O₂ M (G.op.obj X) x y).symm
      map_smul' := fun r x ↦ ((moduleSMulObj_restrictScalars δ M
        (G.sheafPushforwardContinuous (Type ww) J K ⋙ Sheaf.sectionsFunctor J X)
        ((ν.hom.app X) r) x).trans
        (Sheaf.sectionsFunctor_map_moduleSMulHom O₂ M (G.op.obj X) _ x)).symm }

/-- The comparison on the sections over one object, as an isomorphism. -/
def pushforwardRestrictionModuleObjIso (M : SheafOfModules.{ww} O₂) (X : Cᵒᵖ) :
    ((SheafOfModules.restrictScalars ν).obj
        ((pullbackModuleFunctor J (G.sheafPushforwardContinuous (Type ww) J K) R).obj
          ((SheafOfModules.restrictScalars δ).obj M))).val.obj X ≅
      ((SheafOfModules.pushforward.{ww}
        (restrictionPushforwardRingMap J K G R O₂ δ O₁ ν)).obj M).val.obj X where
  hom := pushforwardRestrictionModuleHom J K G R O₂ δ O₁ ν M X
  inv := pushforwardRestrictionModuleHomInv J K G R O₂ δ O₁ ν M X
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The comparison at one sheaf of modules, as an isomorphism of sheaves of modules. -/
def pushforwardRestrictionModuleSheafIso (M : SheafOfModules.{ww} O₂) :
    (SheafOfModules.restrictScalars ν).obj
        ((pullbackModuleFunctor J (G.sheafPushforwardContinuous (Type ww) J K) R).obj
          ((SheafOfModules.restrictScalars δ).obj M)) ≅
      (SheafOfModules.pushforward.{ww}
        (restrictionPushforwardRingMap J K G R O₂ δ O₁ ν)).obj M :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (pushforwardRestrictionModuleObjIso J K G R O₂ δ O₁ ν M)
      (fun _ _ _ ↦ rfl))

/-- **The direct image of sheaves of modules along a continuous functor of sites, with a
restriction of scalars on each side, is Mathlib's pushforward.** Restricting scalars along
`δ : R ⟶ O₂`, transporting modules along restriction of sheaves of sets, and restricting scalars
along `ν : O₁ ⟶ G^{-1}R` is the pushforward of sheaves of modules along `G` over the single
scalar map `restrictionPushforwardRingMap`. -/
def pushforwardRestrictionModulesIso :
    SheafOfModules.restrictScalars δ ⋙
        pullbackModuleFunctor J (G.sheafPushforwardContinuous (Type ww) J K) R ⋙
          SheafOfModules.restrictScalars ν ≅
      SheafOfModules.pushforward.{ww} (restrictionPushforwardRingMap J K G R O₂ δ O₁ ν) :=
  NatIso.ofComponents (pushforwardRestrictionModuleSheafIso J K G R O₂ δ O₁ ν) (fun _ ↦ rfl)

end Stacks.Sheaves.ToposPullback

end
