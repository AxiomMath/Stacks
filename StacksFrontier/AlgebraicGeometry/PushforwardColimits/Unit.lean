module

public import StacksFrontier.AlgebraicGeometry.PushforwardColimits.Free

/-!
# The unit and the counit of Stacks Tag 01SB are invertible at free modules

Let `f : X ⟶ S` be an affine morphism of schemes and `A = f_* 𝒪_X`.
`Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_unit_app_unit` proves that the unit of the
adjunction of Stacks Tag 01SB is invertible at `A` regarded as a module over itself, for an
arbitrary morphism `f`.  This file upgrades that to the free `A`-module on an arbitrary type: the
free module is a coproduct of copies of `A`, the left adjoint preserves that coproduct because it
is a left adjoint, and the direct image preserves it because `f` is affine, which is
`Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforwardModules`.

## Main results

* `Stacks.AlgebraicGeometry.PushforwardColimits.isIso_app_of_isColimit`: the general statement
  that a natural transformation which is invertible at the objects of a diagram is invertible at
  the point of a colimit cocone preserved by both of its functors.
* `Stacks.AlgebraicGeometry.PushforwardColimits.isIso_unit_app_free`: **the unit of the
  adjunction of Stacks Tag 01SB is invertible at the free `f_* 𝒪_X`-module on an arbitrary
  type**, for `f` affine.
* `Stacks.AlgebraicGeometry.PushforwardColimits.isIso_counit_app_free`: the counit is invertible
  at the free `𝒪_X`-module on an arbitrary type.

## Implementation notes

The unit of the adjunction has no component formula, so the argument is the formal one:
whiskering the unit by the diagram of copies of `A` gives a natural transformation which is
invertible componentwise, hence invertible, and the induced map of colimit points is the
component of the unit at the coproduct.  That identification is
`CategoryTheory.Limits.IsColimit.hom_ext` applied to the naturality of the unit.

The counit statement is the triangle argument of
`Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_counit_app_unit` with
`SheafOfModules.pullbackObjUnitToUnit` replaced by
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModulesObjFreeIso`, which identifies the
left adjoint of the free `A`-module with the free `𝒪_X`-module.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v₂ u₂ u

noncomputable section

namespace Stacks.AlgebraicGeometry.PushforwardColimits

open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.AffineQcohEquivalence
open Stacks.AlgebraicGeometry.QcohUnitCounit

/-! ### Invertibility of a natural transformation at a preserved colimit -/

/-- If a natural transformation `η : F ⟶ G` is invertible at every object of a diagram `E`, and
both `F` and `G` carry a colimit cocone of `E` to a colimit cocone, then `η` is invertible at the
point of that cocone.  The component of `η` there is the map of colimit points induced by the
whiskering of `η` by `E`, which is invertible because that whiskering is. -/
theorem isIso_app_of_isColimit {K : Type u₂} [Category.{v₂} K] {C D : Type*} [Category C]
    [Category D] {F G : C ⥤ D} (η : F ⟶ G) {E : K ⥤ C} {c : Cocone E}
    (hF : IsColimit (F.mapCocone c)) (hG : IsColimit (G.mapCocone c))
    (h : ∀ k, IsIso (η.app (E.obj k))) : IsIso (η.app c.pt) := by
  have hw : IsIso (Functor.whiskerLeft E η) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun k ↦ h k
  have key : η.app c.pt =
      (hF.coconePointsIsoOfNatIso hG (asIso (Functor.whiskerLeft E η))).hom := by
    refine hF.hom_ext fun k ↦ ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact η.naturality (c.ι.app k)
  rw [key]
  infer_instance

/-! ### The unit at a free module -/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The left adjoint of Stacks Tag 01SB carries `f_* 𝒪_X`, regarded as a module over itself, to a
quasi-coherent `𝒪_X`-module: `SheafOfModules.pullbackObjUnitToUnit` identifies it with the
structure sheaf. -/
theorem isQuasicoherent_pullbackModules_unit :
    ((pullbackModules f).obj
      (SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf))).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (asIso (SheafOfModules.pullbackObjUnitToUnit (idPushforwardRing f))).symm
    (isQuasicoherent_unit X)

/-- **The unit of the adjunction of Stacks Tag 01SB is invertible at a free module.**  For an
affine morphism `f : X ⟶ S` and an arbitrary type `I`, the unit is invertible at the free
`f_* 𝒪_X`-module on `I`.  The free module is the coproduct of copies of `f_* 𝒪_X`, at which the
unit is invertible by
`Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_unit_app_unit`; the left adjoint preserves that
coproduct, and the direct image preserves it because `f` is affine. -/
theorem isIso_unit_app_free [IsAffineHom f] (I : Type u) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.free.{u} (R := pushforwardRing f.base X.ringCatSheaf) I)) := by
  have hE : ∀ k : Discrete I,
      (((Discrete.functor fun _ : I ↦
          SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf)) ⋙
        pullbackModules f).obj k).IsQuasicoherent :=
    fun _ ↦ isQuasicoherent_pullbackModules_unit f
  have _hp2 : PreservesColimit
      ((Discrete.functor fun _ : I ↦
        SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf)) ⋙ pullbackModules f)
      (pushforwardModules.{u} f.base X.ringCatSheaf) :=
    preservesColimit_pushforwardModules f hE
  have hp : PreservesColimit
      (Discrete.functor fun _ : I ↦
        SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf))
      (pullbackModules f ⋙ pushforwardModules.{u} f.base X.ringCatSheaf) :=
    inferInstance
  exact isIso_app_of_isColimit ((pullbackPushforwardAdjunction f).unit)
    (isColimitOfPreserves (𝟭 (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)))
      (SheafOfModules.isColimitFreeCofan I))
    (hp.preserves (SheafOfModules.isColimitFreeCofan I)).some
    fun _ ↦ isIso_unit_app_unit f

/-- **The unit of the adjunction of Stacks Tag 01SB is invertible at a module having a
presentation.**  A presentation exhibits the module as the cokernel of a morphism between free
modules, hence as the point of a colimit cocone over a diagram of free modules; both functors of
the adjunction preserve that colimit — the left adjoint because it is one, the direct image by
`Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforwardModules`, the two free
modules going to quasi-coherent modules by
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules_free` — and the
unit is invertible at both of them by `isIso_unit_app_free`. -/
theorem isIso_unit_app_of_presentation [IsAffineHom f]
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) (P : G.Presentation) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app G) := by
  have hE : ∀ k, ((parallelPair ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
      kernel.ι P.generators.π) 0 ⋙ pullbackModules f).obj k).IsQuasicoherent := by
    intro k
    obtain _ | _ := k
    · exact isQuasicoherent_pullbackModules_free f P.relations.I
    · exact isQuasicoherent_pullbackModules_free f P.generators.I
  have _hp2 : PreservesColimit (parallelPair ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
      kernel.ι P.generators.π) 0 ⋙ pullbackModules f)
      (pushforwardModules.{u} f.base X.ringCatSheaf) :=
    preservesColimit_pushforwardModules f hE
  have hp : PreservesColimit (parallelPair ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
      kernel.ι P.generators.π) 0)
      (pullbackModules f ⋙ pushforwardModules.{u} f.base X.ringCatSheaf) :=
    inferInstance
  have hfree : ∀ k, IsIso ((pullbackPushforwardAdjunction f).unit.app
      ((parallelPair ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
        kernel.ι P.generators.π) 0).obj k)) := by
    intro k
    obtain _ | _ := k
    · exact isIso_unit_app_free f P.relations.I
    · exact isIso_unit_app_free f P.generators.I
  exact isIso_app_of_isColimit ((pullbackPushforwardAdjunction f).unit)
    (isColimitOfPreserves (𝟭 (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)))
      P.isColimit)
    (hp.preserves P.isColimit).some hfree

/-- **The counit of the adjunction of Stacks Tag 01SB is invertible at a free module.**  The
counit is invertible at the image under the left adjoint of the free `f_* 𝒪_X`-module, by
`Stacks.AlgebraicGeometry.QcohUnitCounit.isIso_counit_app_pullbackModules` and
`isIso_unit_app_free`, and
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModulesObjFreeIso` identifies that module
with the free `𝒪_X`-module; naturality of the counit transports the conclusion. -/
theorem isIso_counit_app_free [IsAffineHom f] (I : Type u) :
    IsIso ((pullbackPushforwardAdjunction f).counit.app
      (SheafOfModules.free.{u} (R := X.ringCatSheaf) I)) :=
  @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
    (Functor.map_isIso (pushforwardModules.{u} f.base X.ringCatSheaf ⋙ pullbackModules f)
      (pullbackModulesObjFreeIso f I).hom)
    (@IsIso.comp_isIso _ _ _ _ _ _ _
      (isIso_counit_app_pullbackModules f _ (isIso_unit_app_free f I))
      (Functor.map_isIso (𝟭 (SheafOfModules.{u} X.ringCatSheaf))
        (pullbackModulesObjFreeIso f I).hom))
    ((pullbackPushforwardAdjunction f).counit.naturality (pullbackModulesObjFreeIso f I).hom)

/-- **The counit of the adjunction of Stacks Tag 01SB is invertible at a module having a
presentation.**  This is the argument of `isIso_unit_app_of_presentation` for the counit: the
composite `f_*` then `f^*` preserves the colimit exhibiting the presentation — `f_*` because the
free modules occurring in it are quasi-coherent and `f` is affine, `f^*` because it is a left
adjoint — and the counit is invertible at a free module by `isIso_counit_app_free`. -/
theorem isIso_counit_app_of_presentation [IsAffineHom f] (M : SheafOfModules.{u} X.ringCatSheaf)
    (P : M.Presentation) :
    IsIso ((pullbackPushforwardAdjunction f).counit.app M) := by
  have hE : ∀ k, ((parallelPair ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
      kernel.ι P.generators.π) 0).obj k).IsQuasicoherent := by
    intro k
    obtain _ | _ := k
    · exact isQuasicoherent_free P.relations.I
    · exact isQuasicoherent_free P.generators.I
  have _hp2 : PreservesColimit (parallelPair ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
      kernel.ι P.generators.π) 0) (pushforwardModules.{u} f.base X.ringCatSheaf) :=
    preservesColimit_pushforwardModules f hE
  have hp : PreservesColimit (parallelPair ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
      kernel.ι P.generators.π) 0)
      (pushforwardModules.{u} f.base X.ringCatSheaf ⋙ pullbackModules f) :=
    inferInstance
  have hfree : ∀ k, IsIso ((pullbackPushforwardAdjunction f).counit.app
      ((parallelPair ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
        kernel.ι P.generators.π) 0).obj k)) := by
    intro k
    obtain _ | _ := k
    · exact isIso_counit_app_free f P.relations.I
    · exact isIso_counit_app_free f P.generators.I
  exact isIso_app_of_isColimit ((pullbackPushforwardAdjunction f).counit)
    (hp.preserves P.isColimit).some
    (isColimitOfPreserves (𝟭 (SheafOfModules.{u} X.ringCatSheaf)) P.isColimit) hfree

end Stacks.AlgebraicGeometry.PushforwardColimits

end

end
