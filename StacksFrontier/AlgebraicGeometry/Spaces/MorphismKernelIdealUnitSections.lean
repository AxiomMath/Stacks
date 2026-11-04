module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalDirectImageUnitSections
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdealDirectImageUnit

/-!
# The unit of Stacks 03LU at the kernel ideal sheaf, on sections

Let `f : X ⟶ Y` be a morphism of algebraic spaces with kernel ideal sheaf `𝓘_f ⊆ 𝒪_Y`.  This
file factors the unit of the adjunction `f^* ⊣ f_*` of Stacks 03LU at `𝓘_f` into its two
factors on sections: the unit of Stacks 03D3, followed by the coefficient map of Stacks 02HP.

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalDirectImageUnitSections.lean` is the same file for
the inclusion of a bundled `AlgebraicGeometry.Space.ClosedSubspaces`.  **Nothing below uses any
hypothesis on `f`.**

## Main results

* `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_kernelIdealSheaf_val_app`: **the unit
  of Stacks 03LU at the kernel ideal sheaf, on sections, is the coefficient map
  `AlgebraicGeometry.Space.kernelConormalDirectImageNu` applied to the unit of Stacks 03D3.**
  This is the hypothesis `hD` that Equation (0619) turns into a retraction of the first arrow of
  Stacks 05ZA.

## Implementation notes

**The morphism of ringed topoi is kept in the folded spelling throughout.**
`AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom` is the spelling the factorization of
the unit elaborates against; at the written-out spelling the factorization and the coefficient
map are each past the heartbeat budget.  This is the discipline of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalDirectImageUnitSections.lean`, recorded there.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction, and
  [Tag 03D3](https://stacks.math.columbia.edu/tag/03D3) and
  [Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), its two factors.
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7), the transported unit.
* [Stacks Project, Tag 02HP](https://stacks.math.columbia.edu/tag/02HP), the consumer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The transported and untransported units of Stacks 03D7 agree at the kernel ideal sheaf**,
on sections, with the morphism of ringed topoi read through
`AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom`.  Keeping to that spelling is what
makes the join affordable; see the implementation notes. -/
theorem modulePullbackAdjunction_unit_kernelIdealSheaf_eq (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : (kernelIdealSheaf B S hS f).toSheafOfModules.val.obj U) :
    ((modulePullbackAdjunction B S hS f).unit.app
        (kernelIdealSheaf B S hS f).toSheafOfModules).val.app U x =
      ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).unit.app
        (kernelIdealSheaf B S hS f).toSheafOfModules).val.app U x :=
  modulePullbackAdjunction_unit_val_app B S hS f
    (kernelIdealSheaf B S hS f).toSheafOfModules U x

/-- **The untransported unit of Stacks 03D7 at the kernel ideal sheaf, in its two factors**: the
unit of Stacks 03D3 followed by the direct image of the unit of Stacks 03CZ.  This is
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules_unit_app_val_app_hom`
instantiated, with the two ringed topoi handed over explicitly. -/
theorem pullbackAdjPushforwardModules_unit_kernelIdealSheaf_val_app (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : (kernelIdealSheaf B S hS f).toSheafOfModules.val.obj U) :
    ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS f)).unit.app
        (kernelIdealSheaf B S hS f).toSheafOfModules).val.app U x =
      (((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedTopos B S hS Y).O)).map
          ((extendRestrictScalarsAdjunction
              (smallEtaleRingedTopos B S hS X).J
              (fSharpCommRing (smallEtaleRingedToposModulesHom B S hS f))
              (inverseImageRingSheaf (smallEtaleRingedToposModulesHom B S hS f).toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf
                  (smallEtaleRingedTopos B S hS Y).O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedTopos B S hS X).O).property).unit.app
            ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedTopos B S hS Y).O)).obj
              (kernelIdealSheaf B S hS f).toSheafOfModules))).val.app U).hom
        (((inverseImageAdjDirectImageModules
            (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedTopos B S hS Y).O)).unit.app
          (kernelIdealSheaf B S hS f).toSheafOfModules).val.app U x) :=
  pullbackAdjPushforwardModules_unit_app_val_app_hom
    (Xt := smallEtaleRingedTopos B S hS X)
    (Yt := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposModulesHom B S hS f)
    (kernelIdealSheaf B S hS f).toSheafOfModules U x

/-- **The coefficient map of Stacks 02HP is the direct image of the unit of Stacks 03CZ**, in
the spelling the factorization of the unit produces.  This is
`AlgebraicGeometry.Space.kernelConormalDirectImageNu_eq`, whose own statement writes the same
morphism through the abbreviations of
`StacksFrontier/AlgebraicGeometry/Spaces/MorphismKernelIdealDirectImageUnit.lean`. -/
theorem kernelConormalDirectImageNu_eq_directImageModules_map (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    kernelConormalDirectImageNu B S hS f U y =
      (((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedTopos B S hS Y).O)).map
          ((extendRestrictScalarsAdjunction
              (smallEtaleRingedTopos B S hS X).J
              (fSharpCommRing (smallEtaleRingedToposModulesHom B S hS f))
              (inverseImageRingSheaf (smallEtaleRingedToposModulesHom B S hS f).toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf
                  (smallEtaleRingedTopos B S hS Y).O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedTopos B S hS X).O).property).unit.app
            ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedTopos B S hS Y).O)).obj
              (kernelIdealSheaf B S hS f).toSheafOfModules))).val.app U).hom y :=
  kernelConormalDirectImageNu_eq B S hS f U y

/-- **The unit of the adjunction of Stacks 03LU at the kernel ideal sheaf, on sections.**  It
carries a local section `x` of `𝓘_f` to the coefficient map
`AlgebraicGeometry.Space.kernelConormalDirectImageNu` of Stacks 02HP applied to the unit of
Stacks 03D3 at `x`.

The adjunction of Stacks 03LU is the composite of the adjunction of Stacks 03D3 with the
extension/restriction-of-scalars adjunction of Stacks 03CZ, so its unit is the first unit
followed by the direct image of the second; and the direct image of the second, read on
sections, *is* the coefficient map. -/
theorem modulePullbackAdjunction_unit_kernelIdealSheaf_val_app (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : (kernelIdealSheaf B S hS f).toSheafOfModules.val.obj U) :
    ((modulePullbackAdjunction B S hS f).unit.app
        (kernelIdealSheaf B S hS f).toSheafOfModules).val.app U x =
      kernelConormalDirectImageNu B S hS f U
        (directImageInverseImageKernelIdealUnit B S hS f U x) :=
  Eq.trans (modulePullbackAdjunction_unit_kernelIdealSheaf_eq B S hS f U x)
    (Eq.trans (pullbackAdjPushforwardModules_unit_kernelIdealSheaf_val_app B S hS f U x)
      (kernelConormalDirectImageNu_eq_directImageModules_map B S hS f U
        (directImageInverseImageKernelIdealUnit B S hS f U x)).symm)

end AlgebraicGeometry.Space

end
