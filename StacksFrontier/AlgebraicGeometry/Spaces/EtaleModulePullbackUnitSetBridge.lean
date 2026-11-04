module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction

/-!
# The transport half of Stacks 03LW on underlying sheaves of sets

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`. The identification of Stacks 03LW of the pullback of `𝒪_Y`-modules with étale
restriction, `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, is built in two
halves: an extension-of-scalars half, which compares the pullback of Stacks 03D6 with the
inverse image of modules of Stacks 03D2, and a *transport* half
`AlgebraicGeometry.Space.etaleModuleInverseImageIsoRestrictionTransport`, which carries the
inverse image of modules to the transport of modules along restriction of sheaves of sets.

This file proves that the unit of the adjunction of the morphism of small étale topoi of `f`,
followed by the direct image of the comparison of Stacks 03LQ, is the unit of the small étale
restriction adjunction, and identifies, on underlying sheaves of sets, the units of Stacks 03LU and
Stacks 03D7 and the extension-of-scalars half of Stacks 03LW.

## Main results

* `AlgebraicGeometry.Space.smallToposMorphismTypeU_adj_unit_comp_inverseImageIso_app`: the unit
  of the adjunction of the morphism of small étale topoi, followed by the direct image of the
  comparison of Stacks 03LQ, is the unit of the small étale restriction adjunction.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### From the module unit to the set unit -/

section UnitBridge

variable (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-- The unit of the adjunction of the morphism of small étale topoi, followed by the direct image
of the comparison of Stacks 03LQ, is the unit of the small étale restriction adjunction. -/
theorem smallToposMorphismTypeU_adj_unit_comp_inverseImageIso_app
    (P : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    (smallToposMorphismTypeU B S hS f).adj.unit.app P ≫
        (smallToposMorphismTypeU B S hS f).pushforward.map
          ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app P) =
      (smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app P :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ P

/-- On underlying sheaves of sets, the unit of the extension of scalars followed by the restriction
of scalars of the identification of Stacks 03LW is the comparison of Stacks 03LQ. -/
private theorem extendScalarsUnit_comp_etaleRestriction (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map
        (((extendScalarsFSharpAdjunction B S hS f).unit.app
          ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G)) ≫ (SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map
          ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app G)) =
      ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app (moduleSetSheaf B S hS Y G)) :=
  Sheaf.hom_ext_sections fun U x ↦
    ((moduleSheafFunctor_map_hom_app
            (((extendScalarsFSharpAdjunction B S hS f).unit.app
              ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G)) ≫
              (SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map
          ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app G)) U x).trans
        ((modulePullbackIsoEtaleModulePullback_unit_app B S hS f hf G U x).trans
          (moduleSheafFunctor_map_hom_app
            ((etaleModuleInverseImageIsoRestrictionTransport B S hS f hf).hom.app G)
            U x).symm)).trans
      (congrArg (fun m ↦ m.hom.app U x)
        (moduleSheafFunctor_map_etaleModuleInverseImageIsoRestrictionTransport_hom_app
          B S hS f hf G))

/-- The unit of Stacks 03D7 is the unit of the composite of the Stacks 03D3 adjunction with the
extension-of-scalars adjunction. -/
private theorem pullbackAdjPushforwardModules_unit_app_eq (G : Modules.{u, u} B S hS Y.1 Y.2) :
    ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).unit.app G) =
      (((inverseImageAdjDirectImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).comp
          (extendScalarsFSharpAdjunction B S hS f)).unit.app G) :=
  rfl

/-- The unit of the Stacks 03D3 adjunction of modules is the unit of the underlying morphism of
topoi, on underlying sheaves of sets. -/
private theorem moduleSheafFunctor_map_inverseImageAdj_unit (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
      ((inverseImageAdjDirectImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).unit.app G) =
            ((smallToposMorphismTypeU B S hS f).adj.unit.app (moduleSetSheaf B S hS Y G)) :=
  moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app
    (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS Y) G

/-- The direct image of modules in front of the extension-of-scalars unit comes off as the
direct image of sheaves of sets. -/
private theorem moduleSheafFunctor_map_directImage_extendScalarsUnit
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
      ((directImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G))) =
      (smallToposMorphismTypeU B S hS f).pushforward.map ((Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G))) :=
  moduleSheafFunctor_map_directImageModules_map
    (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS Y)
      ((extendScalarsFSharpAdjunction B S hS f).unit.app
      ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G))

/-- On underlying sheaves of sets, the unit of Stacks 03D7 is the unit of the morphism of small
étale topoi followed by the direct image of the extension-of-scalars unit. -/
private theorem moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map ((pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).unit.app G) =
      ((smallToposMorphismTypeU B S hS f).adj.unit.app (moduleSetSheaf B S hS Y G)) ≫
        (smallToposMorphismTypeU B S hS f).pushforward.map
          ((Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G))) :=
  (congrArg _ (pullbackAdjPushforwardModules_unit_app_eq B S hS f G)).trans
    ((congrArg _ (Adjunction.comp_unit_app _ _ G)).trans
      ((Functor.map_comp _ _ _).trans
        (congrArg₂ (· ≫ ·) (moduleSheafFunctor_map_inverseImageAdj_unit B S hS f G)
          (moduleSheafFunctor_map_directImage_extendScalarsUnit B S hS f G))))

/-- On underlying sheaves of sets, the unit of Stacks 03LU is the unit of the morphism of small
étale topoi followed by the direct image of the extension-of-scalars unit. -/
private theorem moduleSheafFunctor_map_modulePullbackAdjunction_unit
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
      ((modulePullbackAdjunction B S hS f).unit.app G) =
      ((smallToposMorphismTypeU B S hS f).adj.unit.app (moduleSetSheaf B S hS Y G)) ≫
        (smallToposMorphismTypeU B S hS f).pushforward.map
          ((Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G))) :=
  (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
    (unit_modulePullbackAdjunction_app B S hS f G)).trans
    (((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map_comp
      ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).unit.app G)
      ((modulePushforwardIso B S hS f).hom.app ((modulePullback B S hS f).obj G))).trans
      ((congrArg (fun m ↦ m ≫ (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforwardIso B S hS f).hom.app ((modulePullback B S hS f).obj G)))
            (moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit B S hS f G)).trans
        ((congrArg (fun m ↦ (((smallToposMorphismTypeU B S hS f).adj.unit.app
          (moduleSetSheaf B S hS Y G)) ≫
        (smallToposMorphismTypeU B S hS f).pushforward.map
          ((Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G)))) ≫ m)
            (moduleSheafFunctor_map_modulePushforwardIso_hom_app B S hS f
              ((modulePullback B S hS f).obj G))).trans
          (Category.comp_id (((smallToposMorphismTypeU B S hS f).adj.unit.app
            (moduleSetSheaf B S hS Y G)) ≫
        (smallToposMorphismTypeU B S hS f).pushforward.map
          ((Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G))))))))

/-- The extension-of-scalars unit followed by the identification of Stacks 03LW, on underlying
sheaves of sets, is the comparison of Stacks 03LQ. -/
private theorem moduleSheafFunctor_map_extendScalarsUnit_comp (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G)) ≫ (Sheaf.moduleSheafFunctor
            (structureRingSheaf B S hS X)).map
            ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app G) =
            ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
            (moduleSetSheaf B S hS Y G)) :=
  (Functor.map_comp _ _ ((SheafOfModules.restrictScalars
    (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map
      ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app G))).symm.trans
    (extendScalarsUnit_comp_etaleRestriction B S hS f hf G)

/-- The same equation with its domain written in the geometric spelling of Stacks 03LQ, and its
codomain left in the module-side spelling. -/
private theorem moduleSheafFunctor_map_extendScalarsUnit_comp_setDomain
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (show (smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y G) ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
      ((etaleModulePullback.{u, u} B S hS f hf).obj G) from
      (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G)) ≫ (Sheaf.moduleSheafFunctor
            (structureRingSheaf B S hS X)).map
            ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app G)) =
            (show (smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y G) ⟶
            (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
            ((etaleModulePullback.{u, u} B S hS f hf).obj G)
            from ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
            (moduleSetSheaf B S hS Y G))) :=
  moduleSheafFunctor_map_extendScalarsUnit_comp B S hS f hf G

/-- The direct image of the comparison of Stacks 03LQ is the direct image of the
extension-of-scalars unit followed by the direct image of Stacks 03LW. -/
private theorem pushforward_map_inverseImageIso_eq (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (smallToposMorphismTypeU B S hS f).pushforward.map
      (show (smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y G) ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
      ((etaleModulePullback.{u, u} B S hS f hf).obj G)
      from ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
      (moduleSetSheaf B S hS Y G))) =
      (smallToposMorphismTypeU B S hS f).pushforward.map
        (show (smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y G) ⟶
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
        ((modulePullback B S hS f).obj G) from (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G))) ≫
            (smallToposMorphismTypeU B S hS f).pushforward.map ((Sheaf.moduleSheafFunctor
            (structureRingSheaf B S hS X)).map
            ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app G)) :=
  (congrArg (smallToposMorphismTypeU B S hS f).pushforward.map
      (moduleSheafFunctor_map_extendScalarsUnit_comp_setDomain B S hS f hf G)).symm.trans
    ((smallToposMorphismTypeU B S hS f).pushforward.map_comp
      (show (smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y G) ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj ((modulePullback B S hS f).obj G)
      from (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G))) ((Sheaf.moduleSheafFunctor
            (structureRingSheaf B S hS X)).map
            ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app G)))

/-- On underlying sheaves of sets, the unit of Stacks 03LU is the unit of the morphism of small
étale topoi followed by the direct image of the extension-of-scalars unit, ascribed to the
geometric spelling of the domain of Stacks 03LQ. -/
private theorem unit_pushforward_extendScalarsUnit (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
      ((modulePullbackAdjunction B S hS f).unit.app G) =
      ((smallToposMorphismTypeU B S hS f).adj.unit.app (moduleSetSheaf B S hS Y G)) ≫
      (smallToposMorphismTypeU B S hS f).pushforward.map
      (show (smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y G) ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj ((modulePullback B S hS f).obj G)
      from (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G))) :=
  moduleSheafFunctor_map_modulePullbackAdjunction_unit B S hS f G

/-- On underlying sheaves of sets, the unit of Stacks 03LU followed by the direct image of Stacks
03LW is the unit of the morphism of small étale topoi followed by the direct image of the
comparison of Stacks 03LQ. -/
private theorem unit_comp_eq_comp_inverseImageIso (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
      ((modulePullbackAdjunction B S hS f).unit.app G) ≫
      (smallToposMorphismTypeU B S hS f).pushforward.map ((Sheaf.moduleSheafFunctor
      (structureRingSheaf B S hS X)).map
      ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app G)) =
      ((smallToposMorphismTypeU B S hS f).adj.unit.app (moduleSetSheaf B S hS Y G)) ≫
      (smallToposMorphismTypeU B S hS f).pushforward.map
      (show (smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y G) ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
      ((etaleModulePullback.{u, u} B S hS f hf).obj G)
      from ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
      (moduleSetSheaf B S hS Y G))) :=
  (congrArg (fun m ↦ m ≫ (smallToposMorphismTypeU B S hS f).pushforward.map
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
    ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app G)))
        (unit_pushforward_extendScalarsUnit B S hS f G)).trans
    ((Category.assoc ((smallToposMorphismTypeU B S hS f).adj.unit.app (moduleSetSheaf B S hS Y G))
      ((smallToposMorphismTypeU B S hS f).pushforward.map
      (show (smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y G) ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj ((modulePullback B S hS f).obj G)
      from (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).map ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj G))))
            ((smallToposMorphismTypeU B S hS f).pushforward.map ((Sheaf.moduleSheafFunctor
            (structureRingSheaf B S hS X)).map
            ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app G)))).trans
      (congrArg (fun m ↦ ((smallToposMorphismTypeU B S hS f).adj.unit.app
        (moduleSetSheaf B S hS Y G)) ≫ m) (pushforward_map_inverseImageIso_eq B S hS f hf G).symm))

/-- `smallToposMorphismTypeU_adj_unit_comp_inverseImageIso_app` at a sheaf of modules, with the
comparison of Stacks 03LQ read with the module-side codomain. -/
private theorem comp_inverseImageIso_eq_setUnit (G : Modules.{u, u} B S hS Y.1 Y.2) :
    ((smallToposMorphismTypeU B S hS f).adj.unit.app (moduleSetSheaf B S hS Y G)) ≫
      (smallToposMorphismTypeU B S hS f).pushforward.map
      (show (smallToposMorphismTypeU B S hS f).inverseImage.obj (moduleSetSheaf B S hS Y G) ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
      ((etaleModulePullback.{u, u} B S hS f hf).obj G)
      from ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
      (moduleSetSheaf B S hS Y G))) = (smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app
        (moduleSetSheaf B S hS Y G) :=
  smallToposMorphismTypeU_adj_unit_comp_inverseImageIso_app B S hS f hf
    (moduleSetSheaf B S hS Y G)

end UnitBridge

end AlgebraicGeometry.Space

end
