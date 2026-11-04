module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars

/-!
# The adjunction of Stacks Tag 01SB at the structure sheaf

Let `f : X ⟶ S` be a morphism of schemes.  The first assertion of Stacks Tag 01SB is that, for
`f` affine, the direct image over `f_* 𝒪_X` restricts to an equivalence between the categories of
quasi-coherent modules, and
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`
reduces that to three hypotheses: that the left adjoint preserves quasi-coherence, and that the
unit and the counit of
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackPushforwardAdjunction` are invertible at
quasi-coherent modules.  The first of those is discharged by
`Stacks.AlgebraicGeometry.RestrictEquivalence.isQuasicoherent_pullbackModules`.

This file discharges the other two **at the structure sheaf**, for an arbitrary `f`: no
affineness, no quasi-coherence and no finiteness is assumed anywhere below.  Since the structure
sheaf is quasi-coherent, this is a genuine instance of both hypotheses.

## Main results

* `Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_unit_app_unit`: the unit of the adjunction of
  Tag 01SB is invertible at `f_* 𝒪_X`, regarded as a module over itself.
* `Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_counit_app_unit`: the counit of the adjunction
  of Tag 01SB is invertible at `𝒪_X`.
* `Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_counit_app_pullbackModules`: invertibility of
  the unit at a module `G` gives invertibility of the counit at `f^*G`; this is the triangle
  identity and holds for any adjunction.
* `Stacks.AlgebraicGeometry.QcohUnitCounit.isQuasicoherent_unit_pushforwardRing`: for `f` affine,
  `f_* 𝒪_X` is quasi-coherent as a module over itself.

## Implementation notes

The unit and the counit of `SheafOfModules.pullbackPushforwardAdjunction` have no component
formula: the adjunction is `CategoryTheory.Adjunction.ofIsRightAdjoint`, so both the left adjoint
and the two natural transformations are opaque.  The route taken here does not need one.
Mathlib's `SheafOfModules.pullbackObjUnitToUnit` is by definition the adjoint transpose of
`SheafOfModules.unitToPushforwardObjUnit`, and it is invertible as soon as the functor between
the two sites is final, which `TopologicalSpace.Opens.map f.base` is.  At the morphism of sheaves
of rings used by Tag 01SB — the identity of `f_* 𝒪_X`, spelled so that the continuous functor
between the sites is visible — the transposed map `unitToPushforwardObjUnit` is the identity, by
`rfl`.  So the triangle `η ≫ f_*(pullbackObjUnitToUnit) = 𝟙` exhibits the unit at the structure
sheaf as a composite of invertible maps, and the counit then follows from the triangle identity
of the adjunction together with naturality.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.QcohUnitCounit

open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.AffineQcohEquivalence

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The canonical map of structure sheaves is the identity -/

/-- The canonical morphism `𝒪 ⟶ f_* 𝒪'` of Mathlib, at the morphism of sheaves of rings used by
Stacks Tag 01SB, is the identity.  That morphism is the identity of `f_* 𝒪_X`, and the direct
image of `𝒪_X` over `f_* 𝒪_X` is `f_* 𝒪_X` itself. -/
theorem unitToPushforwardObjUnit_idPushforwardRing :
    SheafOfModules.unitToPushforwardObjUnit (idPushforwardRing f) = 𝟙 _ :=
  rfl

/-- **The triangle computing the unit of Tag 01SB at the structure sheaf.**  The unit at
`f_* 𝒪_X`, followed by the direct image of Mathlib's comparison map `f^*(f_* 𝒪_X) ⟶ 𝒪_X`, is the
identity: the comparison map is by definition the adjoint transpose of
`unitToPushforwardObjUnit`, which is the identity by
`Stacks.AlgebraicGeometry.QcohUnitCounit.unitToPushforwardObjUnit_idPushforwardRing`. -/
theorem unit_app_unit_comp :
    (pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf)) ≫
      (pushforwardModules.{u} f.base X.ringCatSheaf).map
        (SheafOfModules.pullbackObjUnitToUnit (idPushforwardRing f)) = 𝟙 _ :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (idPushforwardRing f)

/-! ### Invertibility of the unit and the counit at the structure sheaf -/

/-- **The unit of the adjunction of Stacks Tag 01SB is invertible at the structure sheaf.**  For
an arbitrary morphism of schemes `f : X ⟶ S`, the unit of the adjunction
`f^* ⊣ f_*` between `f_* 𝒪_X`-modules and `𝒪_X`-modules is invertible at `f_* 𝒪_X` regarded as a
module over itself.  Mathlib's comparison map `f^*(f_* 𝒪_X) ⟶ 𝒪_X` is invertible because
`TopologicalSpace.Opens.map f.base` is a final functor, so the triangle of
`Stacks.AlgebraicGeometry.QcohUnitCounit.unit_app_unit_comp` factors the identity through the
unit. -/
theorem isIso_unit_app_unit :
    IsIso ((pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf))) :=
  @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
    (Functor.map_isIso (pushforwardModules.{u} f.base X.ringCatSheaf)
      (SheafOfModules.pullbackObjUnitToUnit (idPushforwardRing f)))
    (IsIso.id _) (unit_app_unit_comp f)

/-- **Invertibility of the unit at `G` gives invertibility of the counit at `f^*G`.**  This is
the triangle identity of the adjunction and uses nothing about `f` or `G`. -/
theorem isIso_counit_app_pullbackModules
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))
    (h : IsIso ((pullbackPushforwardAdjunction f).unit.app G)) :
    IsIso ((pullbackPushforwardAdjunction f).counit.app ((pullbackModules f).obj G)) :=
  @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ (pullbackModules f)
      ((pullbackPushforwardAdjunction f).unit.app G) h)
    (IsIso.id _)
    ((pullbackPushforwardAdjunction f).left_triangle_components G)

/-- **The counit of the adjunction of Stacks Tag 01SB is invertible at the structure sheaf.**  For
an arbitrary morphism of schemes `f : X ⟶ S`, the counit of the adjunction `f^* ⊣ f_*` between
`f_* 𝒪_X`-modules and `𝒪_X`-modules is invertible at `𝒪_X`.  The counit is invertible at
`f^*(f_* 𝒪_X)` by
`Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_counit_app_pullbackModules` and
`Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_unit_app_unit`, and Mathlib's comparison map
identifies that module with `𝒪_X`; naturality of the counit transports the conclusion. -/
theorem isIso_counit_app_unit :
    IsIso ((pullbackPushforwardAdjunction f).counit.app (SheafOfModules.unit X.ringCatSheaf)) :=
  @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
    (Functor.map_isIso (pushforwardModules.{u} f.base X.ringCatSheaf ⋙ pullbackModules f)
      (SheafOfModules.pullbackObjUnitToUnit (idPushforwardRing f)))
    (@IsIso.comp_isIso _ _ _ _ _ _ _
      (isIso_counit_app_pullbackModules f _ (isIso_unit_app_unit f))
      (Functor.map_isIso (𝟭 (SheafOfModules.{u} X.ringCatSheaf))
        (SheafOfModules.pullbackObjUnitToUnit (idPushforwardRing f))))
    ((pullbackPushforwardAdjunction f).counit.naturality
      (SheafOfModules.pullbackObjUnitToUnit (idPushforwardRing f)))

/-! ### The two modules are quasi-coherent -/

/-- For an affine morphism `f : X ⟶ S`, the sheaf of rings `f_* 𝒪_X` is quasi-coherent as a module
over itself.  This is the second assertion of Stacks Tag 01SB applied to the quasi-coherence of
`f_* 𝒪_X` as an `𝒪_S`-module, which is Tag 02KG. -/
theorem isQuasicoherent_unit_pushforwardRing [IsAffineHom f] :
    (SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf)).IsQuasicoherent :=
  (QcohLimits.affine_isQuasicoherent_restrictScalars_iff f _).mp
    (isQuasicoherent_restrictScalars_pushforwardRing f)

end Stacks.AlgebraicGeometry.QcohUnitCounit

end
