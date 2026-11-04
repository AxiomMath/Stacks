module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalDirectImageUnit

/-!
# The unit of Stacks 03LU at the defining ideal sheaf, on sections

For a closed subspace `Z ⊆ X` of an algebraic space with inclusion `i` and defining ideal sheaf
`𝓘`, the unit `𝓘 ⟶ i_*i^*𝓘 = i_*𝒞_{Z/X}` of the adjunction `i^* ⊣ i_*` of Stacks 03LU carries a
local section `x` of `𝓘` to the coefficient map
`AlgebraicGeometry.Space.conormalDirectImageNu` applied to the unit of Stacks 03D3 at `x`.

This is the two-factor description of that unit — the unit of Stacks 03D3 followed by the direct
image of the unit of Stacks 03CZ — read on sections, with the second factor named as the
coefficient map of Stacks 02HP.

## Main results

* `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_definingIdealSheaf_val_app`: the unit of
  Stacks 03LU at the defining ideal sheaf carries a local section `x` to the coefficient map
  applied to the unit of Stacks 03D3 at `x`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction.
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3) and
  [Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), its two factors.
* [Stacks Project, Tag 02HP](https://stacks.math.columbia.edu/tag/02HP), the coefficient map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.RingedToposModules

universe ww ww' vv uu vv' uu'

section RingedToposUnit

variable {Xt : AlgebraicGeometry.RingedTopos.{vv, uu, ww}}
  {Yt : AlgebraicGeometry.RingedTopos.{vv', uu', ww'}}
  [Xt.J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{ww} RingCat.{ww})]
  [Yt.J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [Xt.J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [Yt.J.HasSheafCompose (CategoryTheory.forget RingCat.{ww'})]
  [Xt.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})]
  [Yt.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww'})]
  [CategoryTheory.HasWeakSheafify Xt.J AddCommGrpCat.{ww}]
  [Xt.J.WEqualsLocallyBijective AddCommGrpCat.{ww}]

/-- **The unit of Stacks 03D7 on sections, in its two factors, with the second factor applied
through `ModuleCat.Hom.hom`.**  For a morphism of ringed topoi `g` and a sheaf of modules `M`, the
unit of `pullbackAdjPushforwardModules g` at `M` carries a local section `x` to the image of the
unit of `inverseImageAdjDirectImageModules` at `x` under the direct image of the unit of
`extendRestrictScalarsAdjunction`. -/
theorem pullbackAdjPushforwardModules_unit_app_val_app_hom (g : RingedToposHom Xt Yt)
    (M : SheafOfModules.{ww'} (Stacks.SheafOfModules.Tensor.ringSheaf Yt.O)) (U : Yt.Cᵒᵖ)
    (x : M.val.obj U) :
    ((pullbackAdjPushforwardModules g).unit.app M).val.app U x =
      (((directImageModules g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Yt.O)).map
          ((extendRestrictScalarsAdjunction Xt.J (fSharpCommRing g)
            (inverseImageRingSheaf g.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Yt.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf Xt.O).property).unit.app
              ((inverseImageModules g.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Yt.O)).obj M))).val.app U).hom
        (((inverseImageAdjDirectImageModules g.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Yt.O)).unit.app M).val.app U x) :=
  pullbackAdjPushforwardModules_unit_app_val_app g M U x

end RingedToposUnit

end Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- **The transported and untransported units of Stacks 03D7 agree at the defining ideal
sheaf**, on sections: the unit of `modulePullbackAdjunction` for `subspaceInclusion` and the unit
of `pullbackAdjPushforwardModules` for `subspaceModulesHom` take the same value on a local section
of the defining ideal sheaf. -/
theorem modulePullbackAdjunction_unit_definingIdealSheaf_eq (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules).val.app U x =
      ((pullbackAdjPushforwardModules (subspaceModulesHom B S hS X Z)).unit.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules).val.app U x :=
  (modulePullbackAdjunction_unit_val_app B S hS (subspaceInclusion B S hS X Z)
    (definingIdealSheaf B S hS X Z).toSheafOfModules U x).trans (by rfl)

/-- **The untransported unit of Stacks 03D7 at the defining ideal sheaf, in its two factors**:
the unit of Stacks 03D3 followed by the direct image of the unit of Stacks 03CZ. -/
theorem pullbackAdjPushforwardModules_unit_definingIdealSheaf_val_app
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    ((pullbackAdjPushforwardModules (subspaceModulesHom B S hS X Z)).unit.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules).val.app U x =
      (((directImageModules (subspaceModulesHom B S hS X Z).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).map
          ((extendRestrictScalarsAdjunction
              (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z)).J
              (fSharpCommRing (subspaceModulesHom B S hS X Z))
              (inverseImageRingSheaf (subspaceModulesHom B S hS X Z).toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf
                  (smallEtaleRingedTopos B S hS X).O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z)).O).property).unit.app
            ((inverseImageModules (subspaceModulesHom B S hS X Z).toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules))).val.app U).hom
        (((inverseImageAdjDirectImageModules (subspaceModulesHom B S hS X Z).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).unit.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules).val.app U x) :=
  pullbackAdjPushforwardModules_unit_app_val_app_hom
    (Xt := smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z))
    (Yt := smallEtaleRingedTopos B S hS X)
    (subspaceModulesHom B S hS X Z) (definingIdealSheaf B S hS X Z).toSheafOfModules U x

/-- **The coefficient map of Stacks 02HP is the direct image of the unit of Stacks 03CZ**: on
sections, `AlgebraicGeometry.Space.conormalDirectImageNu` is the direct image along
`AlgebraicGeometry.Space.subspaceModulesHom` of the unit of `extendRestrictScalarsAdjunction` at
the inverse image of the defining ideal sheaf. -/
theorem conormalDirectImageNu_eq_directImageModules_map (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    conormalDirectImageNu B S hS X Z U y =
      (((directImageModules (subspaceModulesHom B S hS X Z).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).map
          ((extendRestrictScalarsAdjunction
              (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z)).J
              (fSharpCommRing (subspaceModulesHom B S hS X Z))
              (inverseImageRingSheaf (subspaceModulesHom B S hS X Z).toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf
                  (smallEtaleRingedTopos B S hS X).O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z)).O).property).unit.app
            ((inverseImageModules (subspaceModulesHom B S hS X Z).toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules))).val.app U).hom y :=
  conormalDirectImageNu_eq B S hS X Z U y

/-- **The unit of the adjunction of Stacks 03LU at the defining ideal sheaf, on sections.**  It
carries a local section `x` of the defining ideal sheaf `𝓘` of a closed subspace `Z ⊆ X` to the
coefficient map `AlgebraicGeometry.Space.conormalDirectImageNu` of Stacks 02HP applied to the
unit of Stacks 03D3 at `x`. -/
theorem modulePullbackAdjunction_unit_definingIdealSheaf_val_app
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules).val.app U x =
      conormalDirectImageNu B S hS X Z U
        (directImageInverseImageIdealUnit B S hS X Z U x) :=
  Eq.trans (modulePullbackAdjunction_unit_definingIdealSheaf_eq B S hS X Z U x)
    (Eq.trans (pullbackAdjPushforwardModules_unit_definingIdealSheaf_val_app B S hS X Z U x)
      (conormalDirectImageNu_eq_directImageModules_map B S hS X Z U
        (directImageInverseImageIdealUnit B S hS X Z U x)).symm)

end AlgebraicGeometry.Space

end
