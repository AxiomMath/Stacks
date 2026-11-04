module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedPullbackMateUnit

/-!
# The unit of `a_X^* ⊣ a_{X,*}` for the morphism of ringed topoi `a_X`

The morphism `a_X : ((Spaces/X)_fppf, 𝒪) ⟶ (X_{spaces,étale}, 𝒪_X)` of Stacks 0DGM is the morphism
of ringed topoi of the morphism of ringed sites `fppfToSpacesEtaleRingedSiteHom`, on the nose. So
the `a_X` half of Stacks 0DGN (6), proved for the site-presented adjunction, holds for the
adjunction `a_X^* ⊣ a_{X,*}` of the morphism of ringed topoi.

## Main results

* `fppfToSpacesEtaleRingedHom_eq_ringedToposHom_bigFppfModuleUnitTopos`: the morphism of ringed
  topoi `a_X` is the morphism of ringed topoi of the morphism of ringed sites `a_X`.
* `isIso_fppfToSpacesEtaleRingedHom_unit_app_iff_bigFppfModuleUnitTopos`: the unit of
  `a_X^* ⊣ a_{X,*}` and that of the site-presented adjunction are invertible at the same modules.
* `isIso_fppfToSpacesEtaleRingedHom_unit_app_bigFppfModuleUnitTopos`: the unit
  `𝓕 ⟶ a_{X,*}a_X^*𝓕` is an isomorphism for a quasi-coherent `𝒪_X`-module `𝓕`.

## References

* [Stacks Project, Tag 0DGM](https://stacks.math.columbia.edu/tag/0DGM)
* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (X : T.Spaces)

/-- The morphism of ringed topoi `a_X` is the morphism of ringed topoi of the morphism of ringed
sites `a_X`. -/
theorem fppfToSpacesEtaleRingedHom_eq_ringedToposHom_bigFppfModuleUnitTopos :
    fppfToSpacesEtaleRingedHom T X = (fppfToSpacesEtaleRingedSiteHom T X).ringedToposHom :=
  rfl

variable {T X} in
/-- The unit of `a_X^* ⊣ a_{X,*}` for the morphism of ringed topoi `a_X` and that of the
site-presented adjunction are invertible at the same modules. -/
theorem isIso_fppfToSpacesEtaleRingedHom_unit_app_iff_bigFppfModuleUnitTopos
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)) :
    IsIso ((fppfToSpacesEtaleRingedHom T X).pullbackAdjPushforwardModules.unit.app F) ↔
      IsIso ((fppfToSpacesEtaleRingedSiteHom T
        X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app F) :=
  Adjunction.isIso_unit_app_iff_of_iso_right _ _
    (fppfToSpacesEtaleRingedSiteHom T X).pushforwardToposIso F

variable {T X} in
/-- **The `a_X` half of Stacks 0DGN (6) for the morphism of ringed topoi `a_X`**: the unit
`𝓕 ⟶ a_{X,*}a_X^*𝓕` is an isomorphism for a quasi-coherent `𝒪_X`-module `𝓕`. -/
theorem isIso_fppfToSpacesEtaleRingedHom_unit_app_bigFppfModuleUnitTopos
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [F.IsQuasicoherentOnSite] :
    IsIso ((fppfToSpacesEtaleRingedHom T X).pullbackAdjPushforwardModules.unit.app F) :=
  (isIso_fppfToSpacesEtaleRingedHom_unit_app_iff_bigFppfModuleUnitTopos F).mpr
    (isIso_unit_app_of_isQuasicoherentOnSite F)

end AlgebraicGeometry.BigFppfSpaceSite
