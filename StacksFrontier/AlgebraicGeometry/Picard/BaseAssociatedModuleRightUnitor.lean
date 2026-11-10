module

public import StacksFrontier.AlgebraicGeometry.Picard.BaseAssociatedModuleCoherenceRightUnitor
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneralUnit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseAssociatedModuleTensor

/-!
# The right unit coherence of the tensor comparison of the associated-module functor

`StacksFrontier/AlgebraicGeometry/Picard/BaseAssociatedModuleCoherenceRightUnitor.lean` carries the
right unit coherence of `𝓕 ↦ 𝓕^a` down to a single equation, recorded there as the hypothesis
`hunit` of
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_rightUnitor_of_unitComparison_eq`:
that the two constructions of the identification `f^*𝒪_S ≅ 𝒪` of Stacks 03LU at
`((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` — Mathlib's `SheafOfModules.pullbackObjUnitToUnit` at
`AlgebraicGeometry.BigFppfOver.baseStructureMap` and
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, built by corepresentability —
agree under `AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule`.

That equation is now available for an arbitrary morphism of ringed sites, as
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral_hom_app_unit`, so this
file reads it at `AlgebraicGeometry.BigFppfOver.baseToZariskiRingedSiteHom` and the coherence
becomes unconditional.  With it the four data that
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor` asks of the object-level
comparisons of `𝓕 ↦ 𝓕^a` are complete: `baseAssociatedModuleTensorIso'_natural`,
`baseAssociatedModuleTensorIso'_braiding`, `baseAssociatedModuleTensorIso'_associator` and the
right unit one below.

## Main results

* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleUnitIso_hom`: **the comparison
  `𝒪_S^a ≅ 𝒪` of Stacks 03LU on the big `τ`-site is the conjugate of the one of Stacks 03EL**,
  which is the equation the conditional coherence took as its hypothesis.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_rightUnitor`: **the object-level
  comparisons of `𝓕 ↦ 𝓕^a` are compatible with the right unit constraint of Tag 01CA**, with no
  hypothesis.

## Implementation notes

The two crossings between the spelling of the general statement and the spelling of the base site
are paid in `private` lemmas rather than inside the proof, for the reason recorded at the head of
`StacksFrontier/AlgebraicGeometry/Picard/BaseAssociatedModuleCoherenceComplete.lean`: each crosses
on its own by `rfl`, and the recursion of a `have` is measured on top of the enclosing
elaboration.
Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules.RingedToposPullback (pullbackUnitComparison)
open Stacks.Sheaves.RingedToposModules (pullbackModulesObjUnitIso)

universe u

namespace AlgebraicGeometry.BigFppfOver

open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Continuity of the inclusion of the small Zariski site, in the shape instance search keys on:
`AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposSiteHom` does not unfold at instance
transparency, so the field is not found at that spelling. -/
local instance isContinuous_baseToZariskiRingedSiteHom_u (τ : SiteKind) :
    (baseToZariskiRingedSiteHom B S hS τ).toRingedToposSiteHom.u.IsContinuous
      (RingedSite.toRingedTopos S.zariskiRingedSite).J
      (RingedSite.toRingedTopos (baseRingedSite B S hS τ)).J :=
  (baseToZariskiRingedSiteHom B S hS τ).toRingedToposSiteHom.isContinuous

private theorem c1 (τ : SiteKind) :
    (baseAssociatedModulePicardUnitIso B S hS τ).hom =
      SheafOfModules.pullbackObjUnitToUnit
        (baseToZariskiRingedSiteHom B S hS τ).toRingedToposSiteHom.fSharpRing := rfl

private theorem c2 (τ : SiteKind) :
    (pullbackModulesIsoBaseAssociatedModule B S hS τ).inv.app (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
          (zariskiStructureIsSheaf S))) =
      (baseToZariskiRingedSiteHom B S hS τ).pullbackModulesToposIsoGeneral.inv.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (RingedSite.toRingedTopos S.zariskiRingedSite).O)) := rfl

private theorem c3 (τ : SiteKind) :
    (pullbackUnitComparison (baseRingedToposModulesHom B S hS τ)).hom =
      (pullbackModulesObjUnitIso
        (baseToZariskiRingedSiteHom B S hS τ).toRingedToposHom.toRingedToposModulesHom).inv := rfl

private theorem cgen (τ : SiteKind) :
    SheafOfModules.pullbackObjUnitToUnit
        (baseToZariskiRingedSiteHom B S hS τ).toRingedToposSiteHom.fSharpRing =
      (baseToZariskiRingedSiteHom B S hS τ).pullbackModulesToposIsoGeneral.inv.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (RingedSite.toRingedTopos S.zariskiRingedSite).O)) ≫
        (pullbackModulesObjUnitIso
          (baseToZariskiRingedSiteHom B S hS τ).toRingedToposHom.toRingedToposModulesHom).inv :=
  ((Iso.inv_comp_eq ((baseToZariskiRingedSiteHom B S hS τ).pullbackModulesToposIsoGeneral.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.toRingedTopos S.zariskiRingedSite).O)))).mpr
    (RingedSite.HomGeneral.pullbackModulesToposIsoGeneral_hom_app_unit
      (baseToZariskiRingedSiteHom B S hS τ)).symm).symm

/-- **The comparison `𝒪_S^a ≅ 𝒪` of Stacks 03LU on the big `τ`-site is the conjugate of the one
of Stacks 03EL**: its forward map is the inverse of
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule` at the unit followed by
the unit comparison of the pullback along `baseRingedToposModulesHom`. This is the hypothesis of
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_rightUnitor_of_unitComparison_eq`. -/
public theorem baseAssociatedModuleUnitIso_hom (τ : SiteKind) :
    (baseAssociatedModulePicardUnitIso B S hS τ).hom =
      (pullbackModulesIsoBaseAssociatedModule B S hS τ).inv.app (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
          (zariskiStructureIsSheaf S))) ≫
        (pullbackUnitComparison (baseRingedToposModulesHom B S hS τ)).hom :=
  (c1 B S hS τ).trans ((cgen B S hS τ).trans
    (congrArg₂ (fun a b => a ≫ b) (c2 B S hS τ).symm (c3 B S hS τ).symm))

/-- **The object-level comparisons of `𝓕 ↦ 𝓕^a` are compatible with the right unit constraint of
Tag 01CA.**  This is the fourth and last of the data that
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor` asks of them, the other
three being `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_natural`,
`baseAssociatedModuleTensorIso'_braiding` and `baseAssociatedModuleTensorIso'_associator`.

It is
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_rightUnitor_of_unitComparison_eq`
with its one hypothesis discharged by
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleUnitIso_hom`. -/
public theorem baseAssociatedModuleTensorIso'_rightUnitor (τ : SiteKind) :
    Stacks.SheafOfModules.TensorPowerTransport.TensorIsoRightUnitor S.presheaf
      (zariskiStructureIsSheaf S) (baseRingedSite B S hS τ).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).2
      (baseAssociatedModule B S hS τ)
      (baseAssociatedModulePicardUnitIso B S hS τ)
      (baseAssociatedModuleTensorIso' B S hS τ) :=
  baseAssociatedModuleTensorIso'_rightUnitor_of_unitComparison_eq B S hS τ
    (baseAssociatedModuleUnitIso_hom B S hS τ)

end AlgebraicGeometry.BigFppfOver

end
