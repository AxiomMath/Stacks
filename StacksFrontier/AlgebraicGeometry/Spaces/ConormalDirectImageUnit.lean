module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageModulesUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageIdealKernelBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge

/-!
# The coefficient map of Stacks 02HP for the conormal module

For a closed subspace `Z ⊆ X` with inclusion `i` and defining ideal sheaf `𝓘`, the unit of the
adjunction `i^* ⊣ i_*` of Stacks 03LU at `𝓘` is a morphism `𝓘 ⟶ i_*𝒞_{Z/X}`, the conormal module
being `i^*𝓘`.  Stacks 03LU is the composite of the inverse-image/direct-image adjunction of
Stacks 03D3 with extension and restriction of scalars along `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` (Stacks 03CZ),
so that unit is the first unit `𝓘 ⟶ i_*i⁻¹𝓘` followed by the direct image of the second,
`i⁻¹𝓘 ⟶ i^*𝓘`.

On sections, the second factor is the coefficient map `ν` of Stacks 02HP, and the ring unit
`η : 𝒪_X ⟶ i_*i⁻¹𝒪_X` restricted to `𝓘` is the first factor followed by the inclusion
`i_*i⁻¹𝓘 ⟶ i_*i⁻¹𝒪_X`.

## Main definitions

* `AlgebraicGeometry.Space.conormalDirectImageNu`: the coefficient map, the second factor of the
  unit of Stacks 03LU on sections, taken over the inverse-image sheaf of rings so that it is
  `i_*i⁻¹𝒪_X`-semilinear.
* `AlgebraicGeometry.Space.directImageInverseImageIdealUnit`: the first factor on sections.

## Main results

* `AlgebraicGeometry.Space.conormalDirectImageNu_add`, `…_smul` and `…_map`: the coefficient
  map is additive, semilinear over `i_*i⁻¹𝒪_X` and compatible with restriction.
* `AlgebraicGeometry.Space.directImageInverseImageIdealIota_unit`: **the ring and module units
  agree on the defining ideal sheaf.**

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction whose
  unit this is, and [Tag 03D3](https://stacks.math.columbia.edu/tag/03D3) and
  [Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), its two factors.
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module.
* [Stacks Project, Tag 02HP](https://stacks.math.columbia.edu/tag/02HP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- The morphism of ringed topoi of the inclusion of a closed subspace. -/
noncomputable abbrev subspaceModulesHom :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z))
      (smallEtaleRingedTopos B S hS X) :=
  smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z)

/-- `i⁻¹𝓘`, the inverse image of the defining ideal sheaf along the inclusion. -/
noncomputable abbrev inverseImageDefiningIdeal :=
  (inverseImageModules (subspaceToposHom B S hS X Z) (structureRingSheaf B S hS X)).obj
    (definingIdealSheaf B S hS X Z).toSheafOfModules

/-- The adjunction of Stacks 03CZ along the inverse-image form `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` of the
structure map, which is the second factor of the adjunction of Stacks 03LU. -/
noncomputable abbrev conormalExtendRestrictAdjunction :=
  extendRestrictScalarsAdjunction
    (SmallEtale.topology B S hS (subspaceSpace B S hS Z).1)
    (fSharpCommRing (subspaceModulesHom B S hS X Z))
    (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
      (structureRingSheaf B S hS X)).property
    (structureRingSheaf B S hS (subspaceSpace B S hS Z)).property

/-- `i_*(i^*𝓘)` with its scalars restricted along `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` before the direct image
is taken, a module over `i_*i⁻¹𝒪_X`. -/
noncomputable abbrev conormalDirectImageTarget :=
  (pushforwardModuleFunctor (subspaceToposHom B S hS X Z)
      (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
        (structureRingSheaf B S hS X))).obj
    ((SheafOfModules.restrictScalars
      (commRingSheafMap (SmallEtale.topology B S hS (subspaceSpace B S hS Z).1)
        (fSharpCommRing (subspaceModulesHom B S hS X Z))
        (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
          (structureRingSheaf B S hS X)).property
        (structureRingSheaf B S hS (subspaceSpace B S hS Z)).property)).obj
      (conormalModule B S hS X Z))

/-- **The second factor of the unit of Stacks 03LU at the defining ideal sheaf**: the direct
image along `i` of the unit `i⁻¹𝓘 ⟶ i^*𝓘` of extension and restriction of scalars along `i♯`,
as a morphism of modules over `i_*i⁻¹𝒪_X`. -/
noncomputable def conormalDirectImageUnitSecond :=
  (pushforwardModuleFunctor (subspaceToposHom B S hS X Z)
      (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
        (structureRingSheaf B S hS X))).map
    ((conormalExtendRestrictAdjunction B S hS X Z).unit.app
      (inverseImageDefiningIdeal B S hS X Z))

/-- **The coefficient map of Stacks 02HP for the conormal module**: the second factor of the
unit of Stacks 03LU, read on sections. -/
noncomputable def conormalDirectImageNu (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    ToType ((conormalDirectImageTarget B S hS X Z).val.obj U) :=
  ((conormalDirectImageUnitSecond B S hS X Z).val.app U).hom y

/-- The coefficient map is the second factor of the unit of Stacks 03LU read over `𝒪_X`. -/
theorem conormalDirectImageNu_eq (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    conormalDirectImageNu B S hS X Z U y =
      (((directImageModules (subspaceToposHom B S hS X Z)
            (structureRingSheaf B S hS X)).map
          ((conormalExtendRestrictAdjunction B S hS X Z).unit.app
            (inverseImageDefiningIdeal B S hS X Z))).val.app U).hom y := rfl

/-- The coefficient map is additive. -/
theorem conormalDirectImageNu_add (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y z : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    conormalDirectImageNu B S hS X Z U (y + z) =
      conormalDirectImageNu B S hS X Z U y + conormalDirectImageNu B S hS X Z U z :=
  map_add ((conormalDirectImageUnitSecond B S hS X Z).val.app U).hom y z

/-- The coefficient map commutes with restriction. -/
theorem conormalDirectImageNu_map {U V : (SmallEtale B S hS X.1)ᵒᵖ} (f : U ⟶ V)
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    conormalDirectImageNu B S hS X Z V
        ((directImageInverseImageIdeal B S hS X Z).val.map f y) =
      (conormalDirectImageTarget B S hS X Z).val.map f
        (conormalDirectImageNu B S hS X Z U y) :=
  PresheafOfModules.naturality_apply (conormalDirectImageUnitSecond B S hS X Z).val f y

/-- The coefficient map is semilinear over `i_*i⁻¹𝒪_X`. -/
theorem conormalDirectImageNu_smul (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((pushforwardRingSheaf (subspaceToposHom B S hS X Z)
      (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
        (structureRingSheaf B S hS X))).obj.obj U))
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    conormalDirectImageNu B S hS X Z U
        ((show ToType ((pushforwardRingSheaf (subspaceToposHom B S hS X Z)
          (inverseImageRingSheaf (subspaceToposHom B S hS X Z)
            (structureRingSheaf B S hS X))).obj.obj U) from a) • y) =
      a • conormalDirectImageNu B S hS X Z U y :=
  map_smul ((conormalDirectImageUnitSecond B S hS X Z).val.app U).hom a y

/-! ### The first factor of the unit, and the agreement of the ring and module units -/

/-- **The unit of the adjunction of Stacks 03D3 at the defining ideal sheaf**, on sections:
`𝓘(U) ⟶ (i_*i⁻¹𝓘)(U)`. -/
noncomputable def directImageInverseImageIdealUnit (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U)) :=
  ((inverseImageAdjDirectImageModules (subspaceToposHom B S hS X Z)
    (structureRingSheaf B S hS X)).unit.app
      (definingIdealSheaf B S hS X Z).toSheafOfModules).val.app U a

/-- **The unit of Stacks 03D3 at the structure sheaf read as a module over itself is the unit of
the ring-level adjunction of Stacks 00YV**, on sections. -/
theorem inverseImageAdjDirectImageModules_unit_app_unit_val_app
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (b : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj U)) :
    ((inverseImageAdjDirectImageModules (subspaceToposHom B S hS X Z)
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS X).O)).unit.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
           (smallEtaleRingedTopos B S hS X).O))).val.app U b =
      ((commRingImageAdjunction (subspaceToposHom B S hS X Z)).unit.app
        (smallEtaleRingedTopos B S hS X).O).hom.app U b :=
  unit_app_unit_val_app_eq_commRingUnit (subspaceToposHom B S hS X Z)
    (smallEtaleRingedTopos B S hS X).O U b

/-- **The ring and module units agree on the defining ideal sheaf.**  The unit of Stacks 03D3 at
`𝓘`, followed by the inclusion `i_*i⁻¹𝓘 ⟶ i_*i⁻¹𝒪_X`, is the inclusion `𝓘 ⊆ 𝒪_X` followed by
the unit `η : 𝒪_X ⟶ i_*i⁻¹𝒪_X` of Stacks 00YV. -/
theorem directImageInverseImageIdealIota_unit (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U)) :
    directImageInverseImageIdealIota B S hS X Z U
        (directImageInverseImageIdealUnit B S hS X Z U a) =
      ((commRingImageAdjunction (subspaceToposHom B S hS X Z)).unit.app
        (smallEtaleRingedTopos B S hS X).O).hom.app U
          (((definingIdealSheaf B S hS X Z).ι.val.app U).hom a) :=
  Eq.trans
    (congrArg (fun m ↦ (m.val.app U).hom a)
        ((inverseImageAdjDirectImageModules (subspaceToposHom B S hS X Z)
            (structureRingSheaf B S hS X)).unit.naturality
          (definingIdealSheaf B S hS X Z).ι)).symm
    (inverseImageAdjDirectImageModules_unit_app_unit_val_app B S hS X Z U _)

end AlgebraicGeometry.Space

end
