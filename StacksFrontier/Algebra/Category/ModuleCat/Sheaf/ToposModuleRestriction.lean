module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of a sheaf of modules along a continuous functor of sites is restriction

Let `G : C ⥤ D` be a continuous functor of sites and `O` a sheaf of rings on `D`. The inverse
image of the morphism of topoi induced by `G` is restriction `G.sheafPushforwardContinuous`,
so the sections over `X` of the inverse image of a sheaf of `O`-modules `F` are, on the nose,
the sections of `F` over `G X` — but carrying the module structure *transported* along the
sections functor rather than the original one. This file identifies the two, as
`Stacks.Sheaves.ToposPullback.restrictionRingIso` does at the level of sheaves of rings.

The comparison is the identity map on sections; the content is that the transported addition
and scalar action agree with the original ones, which is
`Stacks.Sheaves.ToposPullback.sectionsFunctor_map_moduleAddHom` and
`Stacks.Sheaves.ToposPullback.sectionsFunctor_map_moduleSMulHom` evaluated at `G X`. The two
sides live over different (isomorphic) sheaves of rings, so the restriction side is read
through `SheafOfModules.restrictScalars` along `restrictionRingIso`.

## Main definitions

* `Stacks.Sheaves.ToposPullback.restrictionModuleHom`: the comparison on sections over one
  object, as a linear map.
* `Stacks.Sheaves.ToposPullback.restrictionModuleIso`: the comparison as a natural isomorphism
  of functors, `pullbackModuleFunctor` of the restriction functor against
  `SheafOfModules.pushforward (𝟙 _)` followed by restriction of scalars.

## Main results

* `Stacks.Sheaves.ToposPullback.restrictionModules_comp_restrictScalars`: restriction along `G`
  followed by restriction of scalars along `φ` *is* `SheafOfModules.pushforward φ`.

## Implementation notes

The module instance on the inverse-image side is `moduleObjModule`, which is a `letI` inside
`pullbackModuleVal` and so is not found by instance search; every declaration below therefore
names it, and `ModuleCat.ofHom` is given its source and target objects explicitly, exactly as
`Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings` does for `restrictScalarsObj`.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Functor Opposite CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf K RingCat.{ww})

/-- Restriction of sheaves of modules along a continuous functor of sites: the pushforward of
sheaves of modules along `G` with the identity structure map. For `G = Over.forget U` this is
`SheafOfModules.overFunctor`. -/
noncomputable abbrev restrictionModules :
    SheafOfModules.{ww} O ⥤
      SheafOfModules.{ww} ((G.sheafPushforwardContinuous RingCat.{ww} J K).obj O) :=
  SheafOfModules.pushforward (F := G)
    (𝟙 ((G.sheafPushforwardContinuous RingCat.{ww} J K).obj O))

/-- The transported module structure on the sections of the inverse image of `F` over `X` is
the original module structure on the sections of `F` over `G X`: the identity is a linear map
from the former to the latter, the scalars being compared along `restrictionRingIso`. -/
noncomputable def restrictionModuleHom (F : SheafOfModules.{ww} O) (X : Cᵒᵖ) :
    (pullbackModuleObj J (G.sheafPushforwardContinuous (Type ww) J K) O F).val.obj X ⟶
      ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).obj
        ((restrictionModules J K G O).obj F)).val.obj X :=
  letI : Module ((pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O).obj.obj X)
      ((pullbackModuleAb J (G.sheafPushforwardContinuous (Type ww) J K) O F).obj X) :=
    moduleObjModule O F
      (G.sheafPushforwardContinuous (Type ww) J K ⋙ Sheaf.sectionsFunctor J X)
  ModuleCat.ofHom
    (X := ModuleCat.of
      ((pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O).obj.obj X)
      ((pullbackModuleAb J (G.sheafPushforwardContinuous (Type ww) J K) O F).obj X))
    (Y := (ModuleCat.restrictScalars ((restrictionRingIso J K G O).hom.hom.app X).hom).obj
      (((restrictionModules J K G O).obj F).val.obj X))
    { toFun := id
      map_add' := fun x y ↦ sectionsFunctor_map_moduleAddHom O F (G.op.obj X) x y
      map_smul' := fun r x ↦ sectionsFunctor_map_moduleSMulHom O F (G.op.obj X) r x }

/-- The same identity, read as a linear map in the other direction. -/
noncomputable def restrictionModuleHomInv (F : SheafOfModules.{ww} O) (X : Cᵒᵖ) :
    ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).obj
        ((restrictionModules J K G O).obj F)).val.obj X ⟶
      (pullbackModuleObj J (G.sheafPushforwardContinuous (Type ww) J K) O F).val.obj X :=
  letI : Module ((pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O).obj.obj X)
      ((pullbackModuleAb J (G.sheafPushforwardContinuous (Type ww) J K) O F).obj X) :=
    moduleObjModule O F
      (G.sheafPushforwardContinuous (Type ww) J K ⋙ Sheaf.sectionsFunctor J X)
  ModuleCat.ofHom
    (Y := ModuleCat.of
      ((pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O).obj.obj X)
      ((pullbackModuleAb J (G.sheafPushforwardContinuous (Type ww) J K) O F).obj X))
    (X := (ModuleCat.restrictScalars ((restrictionRingIso J K G O).hom.hom.app X).hom).obj
      (((restrictionModules J K G O).obj F).val.obj X))
    { toFun := id
      map_add' := fun x y ↦ (sectionsFunctor_map_moduleAddHom O F (G.op.obj X) x y).symm
      map_smul' := fun r x ↦ (sectionsFunctor_map_moduleSMulHom O F (G.op.obj X) r x).symm }

/-- The comparison of the inverse image with restriction, on the sections over one object. -/
noncomputable def restrictionModuleObjIso (F : SheafOfModules.{ww} O) (X : Cᵒᵖ) :
    (pullbackModuleObj J (G.sheafPushforwardContinuous (Type ww) J K) O F).val.obj X ≅
      ((SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).obj
        ((restrictionModules J K G O).obj F)).val.obj X where
  hom := restrictionModuleHom J K G O F X
  inv := restrictionModuleHomInv J K G O F X
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The comparison of the inverse image with restriction, on one sheaf of modules. -/
noncomputable def restrictionModuleSheafIso (F : SheafOfModules.{ww} O) :
    pullbackModuleObj J (G.sheafPushforwardContinuous (Type ww) J K) O F ≅
      (SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom).obj
        ((restrictionModules J K G O).obj F) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (restrictionModuleObjIso J K G O F) (fun _ _ _ ↦ rfl))

/-- **Stacks 03D2 for a continuous functor of sites.** The inverse image of a sheaf of
`O`-modules along the restriction functor induced by a continuous functor `G` *is* its
restriction along `G`: the sections agree on the nose and the transported module structure
agrees with the original one. The scalars are compared along `restrictionRingIso`. -/
noncomputable def restrictionModuleIso :
    pullbackModuleFunctor J (G.sheafPushforwardContinuous (Type ww) J K) O ≅
      restrictionModules J K G O ⋙
        SheafOfModules.restrictScalars (restrictionRingIso J K G O).hom :=
  NatIso.ofComponents (restrictionModuleSheafIso J K G O) (fun _ ↦ rfl)

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- **Restriction along `G` followed by restriction of scalars along `φ` is the pushforward of
sheaves of modules along `G` and `φ`**, on the nose: `restrictionModules` is
`SheafOfModules.pushforward` along the identity structure map, and a pushforward along `φ` is a
pushforward along the identity followed by restriction of scalars along `φ`.

Stated at plain variables, where `rfl` discharges it cheaply. That is the point of having it: a
consumer whose `J`, `K`, `G` and `O` are large concrete terms — the ringed topoi of Stacks 08PA,
say — can finish an assembled chain of isomorphisms with `eqToIso` of this equation, which is a
syntactic match, instead of asking `whnf` to perform the same two unfoldings underneath those
terms. Composed with `Stacks.Sheaves.RingedToposModules.restrictScalars_comp`, this is what
turns `restrictionModules ⋙ restrictScalars _ ⋙ restrictScalars _` into a single pushforward. -/
theorem restrictionModules_comp_restrictScalars {R : Sheaf J RingCat.{ww}}
    (φ : R ⟶ (G.sheafPushforwardContinuous RingCat.{ww} J K).obj O) :
    restrictionModules J K G O ⋙ SheafOfModules.restrictScalars φ =
      SheafOfModules.pushforward (F := G) φ :=
  rfl

end Stacks.Sheaves.ToposPullback

end
