module

public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdealInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageStructureSharpSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCommRingCounit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleUnit

/-!
# The kernel of `f_*f⁻¹𝒪_Y ⟶ f_*𝒪_X`, presented by `f_*f⁻¹𝓘_f`

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, with kernel ideal sheaf `𝓘_f = ker(f♯) ⊆ 𝒪_Y`.  The kernel of the **inverse-image
form** `f_*(f♯) : f_*f⁻¹𝒪_Y ⟶ f_*𝒪_X` of the structure map — the split surjection that a left
inverse of `f` splits — is presented, on sections, by `f_*f⁻¹𝓘_f`.

## Main definitions

* `AlgebraicGeometry.Space.directImageInverseImageKernelIdeal`: `f_*f⁻¹𝓘_f`, as a sheaf of
  modules over the inverse-image sheaf of rings `f_*f⁻¹𝒪_Y`.
* `AlgebraicGeometry.Space.directImageInverseImageKernelIdealIota`: the inclusion
  `f_*f⁻¹𝓘_f ⟶ f_*f⁻¹𝒪_Y`, read on sections.
* `AlgebraicGeometry.Space.directImageInverseImageKernelIdealSmul`: the action of a section of
  `f_*f⁻¹𝒪_Y` on a section of `f_*f⁻¹𝓘_f`.

## Main results

* `AlgebraicGeometry.Space.injective_directImageInverseImageKernelIdealIota`: the inclusion is
  injective on sections, at an arbitrary morphism.
* `AlgebraicGeometry.Space.directImageInverseImageKernelIdealIota_add`, `…_smul` and `…_map`:
  the inclusion is additive, semilinear and compatible with restriction, at an arbitrary
  morphism.
* `AlgebraicGeometry.Space.ringSheaf_directImageInverseImageStructureSheafOfHom`: the two
  spellings of the sheaf of rings `f_*f⁻¹𝒪_Y` agree.
* `AlgebraicGeometry.Space.directInverseUnitModuleOfHom`: the direct image of the inverse image
  of the unit module is the unit module.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the ideal sheaf as the
  kernel of the structure map.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map of a
  morphism of algebraic spaces in its two forms.
* [Stacks Project, Tag 02HP](https://stacks.math.columbia.edu/tag/02HP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **`f_*f⁻¹𝓘_f`, as a sheaf of modules over `f_*f⁻¹𝒪_Y`.**  The direct image along `f` of the
inverse image along `f` of the kernel ideal sheaf, taken over the inverse-image sheaf of rings
rather than over `𝒪_Y`. -/
noncomputable def directImageInverseImageKernelIdeal (f : X ⟶ Y) :=
  (pushforwardModuleFunctor (smallEtaleRingedToposHom B S hS f).toToposHom
      (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y))).obj
    ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)).obj
      (kernelIdealSheaf B S hS f).toSheafOfModules)

/-- **The sheaf of rings `f_*f⁻¹𝒪_Y` in its two spellings**: the direct image of the
inverse-image sheaf of rings, and the sheaf of rings underlying the sheaf of commutative rings
`AlgebraicGeometry.Space.directImageInverseImageStructureSheaf`. -/
theorem ringSheaf_directImageInverseImageStructureSheafOfHom (f : X ⟶ Y) :
    Stacks.SheafOfModules.Tensor.ringSheaf
        (directImageInverseImageStructureSheaf B S hS f) =
      pushforwardRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
        (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)) := rfl

/-- **The direct image of the inverse image of the unit module is the unit module.** -/
theorem directInverseUnitModuleOfHom (f : X ⟶ Y) :
    (pushforwardModuleFunctor (smallEtaleRingedToposHom B S hS f).toToposHom
          (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y))).obj
        ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)).obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y))) =
      SheafOfModules.unit (pushforwardRingSheaf
        (smallEtaleRingedToposHom B S hS f).toToposHom
        (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))) :=
  Eq.trans
    (congrArg (pushforwardModuleFunctor (smallEtaleRingedToposHom B S hS f).toToposHom
        (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).obj
      (pullbackModuleObj_unit (SmallEtale.topology B S hS X.1)
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
        (structureRingSheaf B S hS Y)))
    (pullbackModuleObj_unit (SmallEtale.topology B S hS Y.1)
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
      (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)))

/-- **The inclusion `f_*f⁻¹𝓘_f ⟶ f_*f⁻¹𝒪_Y`**, as the direct image of the inverse image of the
inclusion of the kernel ideal sheaf.  Its target is the unit module of the inverse-image sheaf
of rings by `AlgebraicGeometry.Space.directInverseUnitModuleOfHom`. -/
noncomputable def directImageInverseImageKernelIdealι (f : X ⟶ Y) :
    directImageInverseImageKernelIdeal B S hS f ⟶
      (pushforwardModuleFunctor (smallEtaleRingedToposHom B S hS f).toToposHom
          (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y))).obj
        ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)).obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y))) :=
  (pushforwardModuleFunctor (smallEtaleRingedToposHom B S hS f).toToposHom
      (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y))).map
    ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)).map (kernelIdealSheaf B S hS f).ι)

/-! ### The presentation of the kernel, sectionwise -/

/-- **The inclusion `f_*f⁻¹𝓘_f ⟶ f_*f⁻¹𝒪_Y` on sections**, with values in the sections of
`f_*f⁻¹𝒪_Y` read as a sheaf of commutative rings. -/
noncomputable def directImageInverseImageKernelIdealIota (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    ToType ((directImageInverseImageStructureSheaf B S hS f).obj.obj U) :=
  ((directImageInverseImageKernelIdealι B S hS f).val.app U).hom y

/-- The action of a section of `f_*f⁻¹𝒪_Y` on a section of `f_*f⁻¹𝓘_f`. -/
noncomputable def directImageInverseImageKernelIdealSmul (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : ToType ((directImageInverseImageStructureSheaf B S hS f).obj.obj U))
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U) :=
  (show ToType ((pushforwardRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
    (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y))).obj.obj U) from a) • y

/-- The inclusion on sections is the first map of
`AlgebraicGeometry.Space.directImageKernelIdealComplex`: restriction of scalars changes neither
the sections nor the map. -/
theorem directImageInverseImageKernelIdealIota_eq (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ToType ((directImageKernelIdealComplex B S hS f).X₁.val.obj U)) :
    directImageInverseImageKernelIdealIota B S hS f U y =
      ((directImageKernelIdealComplex B S hS f).f.val.app U).hom y := rfl

/-- **The inclusion is injective on sections**, at an arbitrary morphism. -/
theorem injective_directImageInverseImageKernelIdealIota (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y z : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U))
    (hyz : directImageInverseImageKernelIdealIota B S hS f U y =
      directImageInverseImageKernelIdealIota B S hS f U z) : y = z :=
  injective_directImageKernelIdeal_f_val_app B S hS f U hyz

/-- The inclusion on sections is additive. -/
theorem directImageInverseImageKernelIdealIota_add (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y z : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    directImageInverseImageKernelIdealIota B S hS f U (y + z) =
      directImageInverseImageKernelIdealIota B S hS f U y +
        directImageInverseImageKernelIdealIota B S hS f U z :=
  map_add ((directImageInverseImageKernelIdealι B S hS f).val.app U).hom y z

/-- **The inclusion on sections is semilinear**, the scalar action on the target being the
multiplication of `f_*f⁻¹𝒪_Y`. -/
theorem directImageInverseImageKernelIdealIota_smul (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : ToType ((directImageInverseImageStructureSheaf B S hS f).obj.obj U))
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    directImageInverseImageKernelIdealIota B S hS f U
        (directImageInverseImageKernelIdealSmul B S hS f U a y) =
      a * directImageInverseImageKernelIdealIota B S hS f U y :=
  Eq.trans
    (map_smul ((directImageInverseImageKernelIdealι B S hS f).val.app U).hom
      (show ToType ((pushforwardRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
        (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y))).obj.obj U) from a) y)
    (pullbackModuleObj_unit_smul (SmallEtale.topology B S hS Y.1)
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
      (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)) U _ _)

/-- The inclusion on sections commutes with restriction. -/
theorem directImageInverseImageKernelIdealIota_map (f : X ⟶ Y)
    {U V : (SmallEtale B S hS Y.1)ᵒᵖ} (h : U ⟶ V)
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    directImageInverseImageKernelIdealIota B S hS f V
        ((directImageInverseImageKernelIdeal B S hS f).val.map h y) =
      ((directImageInverseImageStructureSheaf B S hS f).obj.map h).hom
        (directImageInverseImageKernelIdealIota B S hS f U y) :=
  PresheafOfModules.naturality_apply (directImageInverseImageKernelIdealι B S hS f).val h y

end AlgebraicGeometry.Space

end
