module

public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Pullback of an endomorphism of the structure sheaf is computed by the map on functions

Pulling an endomorphism `a : 𝒪_Y ⟶ 𝒪_Y` of the structure sheaf back along `f : X ⟶ Y` and
reading the result through `RingedSpaceModuleAdjunction.modulePullbackObjUnitIso` gives the
endomorphism `b` of `𝒪_X` characterized by

`a ≫ f^♯ = f^♯ ≫ f_* b`,

an equation between morphisms of sheaves of `𝒪_Y`-modules `𝒪_Y ⟶ f_* 𝒪_X` in which `f^♯`, that
is `SheafOfModules.unitToPushforwardObjUnit` of `RingedSpaceModuleAdjunction.structureSheafHom`,
acts on sections as the given map of sheaves of rings.

## Main definitions

* `RingedSpaceModuleAdjunction.pullbackUnitAut`: the automorphism of `𝒪_X` obtained from an
  automorphism of `𝒪_Y` by pullback, conjugated by `modulePullbackObjUnitIso`.

## Main results

* `SheafOfModules.pullback_map_unit_comm_iff`: at a continuous map of ringed sites, the square
  for `pullbackObjUnitToUnit` commutes exactly when the transposed square for
  `unitToPushforwardObjUnit` does.
* `RingedSpaceModuleAdjunction.modulePullback_map_unit_comm_iff`: the same for a morphism of
  ringed spaces, in the `modulePullback` spelling.
* `RingedSpaceModuleAdjunction.pullbackUnitAut_eq_iff`: the same criterion for the conjugated
  automorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u₁ u₂ u

namespace SheafOfModules

variable {C : Type u₁} [Category C] {D : Type u₂} [Category D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [F.IsContinuous J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(pushforward.{u} φ).IsRightAdjoint]

/-- The square expressing that `b` is the pullback of `a` through
`SheafOfModules.pullbackObjUnitToUnit` commutes if and only if the square `a ≫ φ = φ ≫ f_* b`
for `SheafOfModules.unitToPushforwardObjUnit` commutes. -/
theorem pullback_map_unit_comm_iff (a : unit S ⟶ unit S) (b : unit R ⟶ unit R) :
    (pullback.{u} φ).map a ≫ pullbackObjUnitToUnit φ = pullbackObjUnitToUnit φ ≫ b ↔
      a ≫ unitToPushforwardObjUnit φ =
        unitToPushforwardObjUnit φ ≫ (pushforward.{u} φ).map b := by
  rw [← ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).apply_eq_iff_eq,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

end SheafOfModules

namespace RingedSpaceModuleAdjunction

open AlgebraicGeometry SheafOfModules

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- For a morphism of ringed spaces `f`, the endomorphism `b` of `𝒪_X` is the pullback of the
endomorphism `a` of `𝒪_Y` along `f` if and only if `a ≫ f^♯ = f^♯ ≫ f_* b`. -/
theorem modulePullback_map_unit_comm_iff
    (a : SheafOfModules.unit (structureSheafRing Y) ⟶ SheafOfModules.unit (structureSheafRing Y))
    (b : SheafOfModules.unit (structureSheafRing X) ⟶ SheafOfModules.unit (structureSheafRing X)) :
    (modulePullback f).map a ≫ (modulePullbackObjUnitIso f).hom =
        (modulePullbackObjUnitIso f).hom ≫ b ↔
      a ≫ unitToPushforwardObjUnit (structureSheafHom f) =
        unitToPushforwardObjUnit (structureSheafHom f) ≫
          (pushforward.{u} (structureSheafHom f)).map b := by
  have : (opensMap f).Final := CategoryTheory.final_of_representablyFlat _
  exact pullback_map_unit_comm_iff (structureSheafHom f) a b

/-- The automorphism of `𝒪_X` obtained from an automorphism of `𝒪_Y` by pullback along `f`,
conjugated by the identification `f^* 𝒪_Y ≅ 𝒪_X`. -/
def pullbackUnitAut
    (a : SheafOfModules.unit (structureSheafRing Y) ≅ SheafOfModules.unit (structureSheafRing Y)) :
    SheafOfModules.unit (structureSheafRing X) ≅ SheafOfModules.unit (structureSheafRing X) :=
  (modulePullbackObjUnitIso f).symm ≪≫ (modulePullback f).mapIso a ≪≫
    modulePullbackObjUnitIso f

/-- `pullbackUnitAut f a = b` if and only if `a ≫ f^♯ = f^♯ ≫ f_* b`. -/
theorem pullbackUnitAut_eq_iff
    (a : SheafOfModules.unit (structureSheafRing Y) ≅ SheafOfModules.unit (structureSheafRing Y))
    (b : SheafOfModules.unit (structureSheafRing X) ≅ SheafOfModules.unit (structureSheafRing X)) :
    pullbackUnitAut f a = b ↔
      a.hom ≫ unitToPushforwardObjUnit (structureSheafHom f) =
        unitToPushforwardObjUnit (structureSheafHom f) ≫
          (pushforward.{u} (structureSheafHom f)).map b.hom := by
  rw [← modulePullback_map_unit_comm_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ Iso.ext ?_⟩
  · subst h
    simp [pullbackUnitAut]
  · simp only [pullbackUnitAut, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [h, Iso.inv_hom_id_assoc]

end RingedSpaceModuleAdjunction

end
