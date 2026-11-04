module

public import StacksFrontier.AlgebraicGeometry.Descent.CounitFlatBaseChange

/-!
# `𝒪_Y = c_*𝒪_X` under flat base change

For a morphism of schemes `c : X ⟶ Y`, the comparison map `𝒪_Y ⟶ c_*𝒪_X` is an isomorphism if
and only if the unit of `c^* ⊣ c_*` is one at `𝒪_Y`. Invertibility of that unit survives a flat
base change ([Stacks, Tag 02KH] in degree zero), so `𝒪_Y = c_*𝒪_X` does: for a cartesian square
with `g : Y' ⟶ Y` flat and `c` quasi-compact and quasi-separated, `𝒪_{Y'} = c'_*𝒪_{X'}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_unitToPushforwardObjUnit_of_isIso_unit_app_unit`
* `AlgebraicGeometry.Scheme.Hom.isIso_unitToPushforwardObjUnit_of_isPullback`

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (c : X ⟶ Y)

/-- `𝒪_Y = c_*𝒪_X` follows from the invertibility of the unit of `c^* ⊣ c_*` at `𝒪_Y`: the unit
followed by `c_*` of the isomorphism `c^*𝒪_Y ≅ 𝒪_X` is the comparison map. -/
theorem isIso_unitToPushforwardObjUnit_of_isIso_unit_app_unit
    (h : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
      (SheafOfModules.unit Y.ringCatSheaf))) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom) := by
  let : (SheafOfModules.pushforward c.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction c).isRightAdjoint
  have : (TopologicalSpace.Opens.map c.base).Final := Stacks.Topology.final_opensMap _
  let q : (Scheme.Modules.pullback c).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit c.toRingCatSheafHom
  have heq : (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫ (Scheme.Modules.pushforward c).map q =
      SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)
  have : IsIso q := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  rw [← heq]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h (Functor.map_isIso _ q)

/-- **`𝒪_Y = c_*𝒪_X` survives a flat base change**: for a cartesian square with `g` flat and `c`
quasi-compact and quasi-separated, `𝒪_{Y'} = c'_*𝒪_{X'}` ([Stacks, Tag 02KH] in degree zero). -/
theorem isIso_unitToPushforwardObjUnit_of_isPullback {X' Y' : Scheme.{u}} {g : Y' ⟶ Y}
    {g' : X' ⟶ X} {c' : X' ⟶ Y'} (H : IsPullback g' c' c g) [Flat g] [QuasiCompact c]
    [QuasiSeparated c] (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit c'.toRingCatSheafHom) := by
  have hO' : IsIso (C := Y.Modules)
      (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom) := hO
  have hc : IsIso c.toLRSHom.toHom.c := by
    have : ∀ U, IsIso (c.toLRSHom.toHom.c.app U) := fun U => by
      let e := ((Scheme.Modules.toPresheaf Y).mapIso (@asIso _ _ _ _ _ hO')).app U
      exact (ConcreteCategory.isIso_iff_bijective (c.app U.unop)).mpr
        (ConcreteCategory.bijective_of_isIso e.hom)
    exact NatIso.isIso_of_isIso_app _
  exact isIso_unitToPushforwardObjUnit_of_isIso_unit_app_unit c'
    (VectorBundleCodimensionOne.isIso_unit_app_unit_of_isPullback H
      (VectorBundleCodimensionOne.isIso_unit_app_unit_of_isIso_c c hc))

end AlgebraicGeometry.Scheme.Hom
