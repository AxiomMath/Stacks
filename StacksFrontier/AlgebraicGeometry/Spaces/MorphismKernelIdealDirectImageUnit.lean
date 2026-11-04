module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageModulesUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceKernelIdealFirstMap
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdealSplitSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge

/-!
# The coefficient map of Stacks 02HP at the kernel ideal sheaf

Let `f : X ⟶ Y` be a morphism of algebraic spaces with kernel ideal sheaf `𝓘_f = ker(f♯) ⊆ 𝒪_Y`.
The unit of the adjunction `f^* ⊣ f_*` of Stacks 03LU at `𝓘_f` is a morphism
`𝓘_f ⟶ f_*f^*𝓘_f`.  Stacks 03LU is the composite of the inverse-image/direct-image adjunction
of Stacks 03D3 with extension and restriction of scalars along `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`
(Stacks 03CZ), so that unit is the first unit `𝓘_f ⟶ f_*f⁻¹𝓘_f` followed by the direct image of
the second, `f⁻¹𝓘_f ⟶ f^*𝓘_f`.

This file names the two factors on sections.  The second is the coefficient map the derivation
of Stacks 02HP consumes — the map `ν` out of the presentation of the kernel of the split
surjection `f_*f⁻¹𝒪_Y ⟶ f_*𝒪_X` of
`StacksFrontier/AlgebraicGeometry/Spaces/MorphismKernelIdealSplitKernel.lean` — and the first is
the one that recognises the derivation on the ideal, because **the ring unit
`η : 𝒪_Y ⟶ f_*f⁻¹𝒪_Y` restricted to `𝓘_f` is the first factor followed by the inclusion
`f_*f⁻¹𝓘_f ⟶ f_*f⁻¹𝒪_Y`**.

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalDirectImageUnit.lean` is the same construction for
the inclusion of a bundled `AlgebraicGeometry.Space.ClosedSubspaces`, through the defining ideal
sheaf of Stacks 03MB.  **Nothing below uses any hypothesis on `f` whatever**: the unit of an
adjunction and its factors exist at an arbitrary morphism.

## Main definitions

* `AlgebraicGeometry.Space.kernelConormalModule`: `f^*𝓘_f`, the source of the first arrow of
  Stacks 05ZA at the kernel ideal sheaf.
* `AlgebraicGeometry.Space.kernelConormalDirectImageNu`: the coefficient map, the second factor
  of the unit of Stacks 03LU on sections, taken over the inverse-image sheaf of rings so that it
  is `f_*f⁻¹𝒪_Y`-semilinear.
* `AlgebraicGeometry.Space.directImageInverseImageKernelIdealUnit`: the first factor on
  sections.

## Main results

* `AlgebraicGeometry.Space.kernelConormalDirectImageNu_add`, `…_smul` and `…_map`: the three
  properties of the coefficient map the derivation needs.
* `AlgebraicGeometry.Space.directImageInverseImageKernelIdealIota_unit`: **the ring and module
  units agree on the kernel ideal sheaf.**  This is the naturality of the unit of Stacks 03D3 at
  the inclusion `𝓘_f ⊆ 𝒪_Y`, together with
  `AlgebraicGeometry.Space.inverseImageAdjDirectImageModules_unit_app_unit_val_app_of_hom`.

## Implementation notes

**The coefficient map is taken over the inverse-image sheaf of rings, not over `𝒪_Y`.**  The
derivation of Stacks 02HP needs its coefficient map to be semilinear over the ring the split
surjection lives on, which is `f_*f⁻¹𝒪_Y`; the direct image of modules of Stacks 03D3 restricts
the scalars along the unit and lands over `𝒪_Y`.  Restriction of scalars changes neither the
sections nor the map, so the two readings are the same function —
`AlgebraicGeometry.Space.kernelConormalDirectImageNu_eq`, `rfl` — but only the unrestricted one
has the linearity, so that is the one the definition is built from.

**Why the agreement of the two units is imported generically.**  Identifying the sections of
`f_*f⁻¹𝒪_Y` with the sections of the direct image of the inverse image of the unit module is
past the heartbeat budget at this instantiation, and free generically; so the content is
`Stacks.Sheaves.RingedToposModules.unit_app_unit_val_app_eq_commRingUnit` and this file only
instantiates it.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction whose
  unit this is, and [Tag 03D3](https://stacks.math.columbia.edu/tag/03D3) and
  [Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), its two factors.
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module.
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

/-- **`f^*𝓘_f`, the conormal module at the kernel ideal sheaf of an arbitrary morphism.**  The
inverse image along `f` of the kernel ideal sheaf; it is the source of
`AlgebraicGeometry.Space.kernelConormalFirstMap`.

At the inclusion of a closed subspace the kernel ideal sheaf is the defining ideal sheaf of
Stacks 03MB (`AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`), so this is the
conormal module of Stacks 04CN (`AlgebraicGeometry.Space.conormalModule_eq`). -/
noncomputable def kernelConormalModule (f : X ⟶ Y) :
    Modules.{u, u} B S hS X.1 X.2 :=
  (modulePullback B S hS f).obj (kernelIdealSheaf B S hS f).toSheafOfModules

/-- The conormal module at the kernel ideal sheaf is the inverse image of that ideal sheaf
along `f`.  This is the defining equation, stated so that consumers may rewrite with it rather
than unfold the definition.

**The definition is a plain `def` and not an `abbrev`, deliberately.**  A reducible definition is
unfolded by `whnf`, and the statements of the derivation of Stacks 02HP that mention these
coefficients are then carried past the heartbeat budget; behind a plain `def` the unfolding
stops.  This is the decision recorded at `AlgebraicGeometry.Space.conormalModule`, for the same
reason. -/
theorem kernelConormalModule_eq (f : X ⟶ Y) :
    kernelConormalModule B S hS f =
      (modulePullback B S hS f).obj (kernelIdealSheaf B S hS f).toSheafOfModules :=
  rfl

/-- `f⁻¹𝓘_f`, the inverse image of the kernel ideal sheaf along `f`. -/
noncomputable abbrev inverseImageKernelIdeal (f : X ⟶ Y) :=
  (inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).obj
    (kernelIdealSheaf B S hS f).toSheafOfModules

/-- The adjunction of Stacks 03CZ along the inverse-image form `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of the
structure map, which is the second factor of the adjunction of Stacks 03LU. -/
noncomputable abbrev kernelExtendRestrictAdjunction (f : X ⟶ Y) :=
  extendRestrictScalarsAdjunction (SmallEtale.topology B S hS X.1)
    (fSharpCommRing (smallEtaleRingedToposModulesHom B S hS f))
    (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).property
    (structureRingSheaf B S hS X).property

/-- `f_*(f^*𝓘_f)` with its scalars restricted along `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` before the direct image
is taken, which is the target the second factor of the unit of Stacks 03LU lands in, and the
spelling in which it is a module over `f_*f⁻¹𝒪_Y`. -/
noncomputable abbrev kernelConormalDirectImageTarget (f : X ⟶ Y) :=
  (pushforwardModuleFunctor (smallEtaleRingedToposHom B S hS f).toToposHom
      (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y))).obj
    ((SheafOfModules.restrictScalars
      (commRingSheafMap (SmallEtale.topology B S hS X.1)
        (fSharpCommRing (smallEtaleRingedToposModulesHom B S hS f))
        (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).property
        (structureRingSheaf B S hS X).property)).obj
      (kernelConormalModule B S hS f))

/-- **The second factor of the unit of Stacks 03LU at the kernel ideal sheaf**: the direct image
along `f` of the unit `f⁻¹𝓘_f ⟶ f^*𝓘_f` of extension and restriction of scalars along `f♯`.
Taken over the inverse-image sheaf of rings, so that it is `f_*f⁻¹𝒪_Y`-linear. -/
noncomputable def kernelConormalDirectImageUnitSecond (f : X ⟶ Y) :=
  (pushforwardModuleFunctor (smallEtaleRingedToposHom B S hS f).toToposHom
      (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y))).map
    ((kernelExtendRestrictAdjunction B S hS f).unit.app
      (inverseImageKernelIdeal B S hS f))

/-- **The coefficient map of Stacks 02HP at the kernel ideal sheaf**: the second factor of the
unit of Stacks 03LU, read on sections. -/
noncomputable def kernelConormalDirectImageNu (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    ToType ((kernelConormalDirectImageTarget B S hS f).val.obj U) :=
  ((kernelConormalDirectImageUnitSecond B S hS f).val.app U).hom y

/-- The coefficient map is the second factor of the unit of Stacks 03LU read over `𝒪_Y`:
restriction of scalars changes neither the sections nor the map. -/
theorem kernelConormalDirectImageNu_eq (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    kernelConormalDirectImageNu B S hS f U y =
      (((directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)).map
          ((kernelExtendRestrictAdjunction B S hS f).unit.app
            (inverseImageKernelIdeal B S hS f))).val.app U).hom y := rfl

/-- The coefficient map is additive. -/
theorem kernelConormalDirectImageNu_add (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y z : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    kernelConormalDirectImageNu B S hS f U (y + z) =
      kernelConormalDirectImageNu B S hS f U y + kernelConormalDirectImageNu B S hS f U z :=
  map_add ((kernelConormalDirectImageUnitSecond B S hS f).val.app U).hom y z

/-- The coefficient map commutes with restriction. -/
theorem kernelConormalDirectImageNu_map (f : X ⟶ Y)
    {U V : (SmallEtale B S hS Y.1)ᵒᵖ} (h : U ⟶ V)
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    kernelConormalDirectImageNu B S hS f V
        ((directImageInverseImageKernelIdeal B S hS f).val.map h y) =
      (kernelConormalDirectImageTarget B S hS f).val.map h
        (kernelConormalDirectImageNu B S hS f U y) :=
  PresheafOfModules.naturality_apply
    (kernelConormalDirectImageUnitSecond B S hS f).val h y

/-- The coefficient map is semilinear over `f_*f⁻¹𝒪_Y`. -/
theorem kernelConormalDirectImageNu_smul (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : ToType ((pushforwardRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
      (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y))).obj.obj U))
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    kernelConormalDirectImageNu B S hS f U
        ((show ToType ((pushforwardRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
          (inverseImageRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y))).obj.obj U) from a) • y) =
      a • kernelConormalDirectImageNu B S hS f U y :=
  map_smul ((kernelConormalDirectImageUnitSecond B S hS f).val.app U).hom a y

/-! ### The first factor of the unit, and the agreement of the ring and module units -/

/-- **The unit of the adjunction of Stacks 03D3 at the kernel ideal sheaf**, on sections:
`𝓘_f(U) ⟶ (f_*f⁻¹𝓘_f)(U)`. -/
noncomputable def directImageInverseImageKernelIdealUnit (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : ToType ((kernelIdealSheaf B S hS f).toSheafOfModules.val.obj U)) :=
  ((inverseImageAdjDirectImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
    (structureRingSheaf B S hS Y)).unit.app
      (kernelIdealSheaf B S hS f).toSheafOfModules).val.app U a

/-- **The unit of Stacks 03D3 at the structure sheaf read as a module over itself is the unit of
the ring-level adjunction of Stacks 00YV**, on sections.  This is
`Stacks.Sheaves.RingedToposModules.unit_app_unit_val_app_eq_commRingUnit`, which is proved
generically: at this instantiation the identification of the sections of `f_*f⁻¹𝒪_Y` with the
sections of the direct image of the inverse image of the unit module is past the heartbeat
budget, while generically it is free. -/
theorem inverseImageAdjDirectImageModules_unit_app_unit_val_app_of_hom (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (b : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj U)) :
    ((inverseImageAdjDirectImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS Y).O)).unit.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedTopos B S hS Y).O))).val.app U b =
      ((commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS f).toToposHom).unit.app
          (smallEtaleRingedTopos B S hS Y).O).hom.app U b :=
  unit_app_unit_val_app_eq_commRingUnit (smallEtaleRingedToposHom B S hS f).toToposHom
    (smallEtaleRingedTopos B S hS Y).O U b

/-- **The ring and module units agree on the kernel ideal sheaf.**  The unit of Stacks 03D3 at
`𝓘_f`, followed by the inclusion `f_*f⁻¹𝓘_f ⟶ f_*f⁻¹𝒪_Y`, is the inclusion `𝓘_f ⊆ 𝒪_Y` followed
by the unit `η : 𝒪_Y ⟶ f_*f⁻¹𝒪_Y` of Stacks 00YV.

This is the naturality of the unit of Stacks 03D3 at the inclusion of the ideal, together with
`AlgebraicGeometry.Space.inverseImageAdjDirectImageModules_unit_app_unit_val_app_of_hom`. -/
theorem directImageInverseImageKernelIdealIota_unit (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : ToType ((kernelIdealSheaf B S hS f).toSheafOfModules.val.obj U)) :
    directImageInverseImageKernelIdealIota B S hS f U
        (directImageInverseImageKernelIdealUnit B S hS f U a) =
      ((commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS f).toToposHom).unit.app
          (smallEtaleRingedTopos B S hS Y).O).hom.app U
            (((kernelIdealSheaf B S hS f).ι.val.app U).hom a) :=
  Eq.trans
    (congrArg (fun m ↦ (m.val.app U).hom a)
        ((inverseImageAdjDirectImageModules
            (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)).unit.naturality
          (kernelIdealSheaf B S hS f).ι)).symm
    (inverseImageAdjDirectImageModules_unit_app_unit_val_app_of_hom B S hS f U _)

end AlgebraicGeometry.Space

end
