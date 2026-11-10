module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackSections

/-!
# The base change of the Zariski reading through the comparisons of Stacks 04M0

For a morphism `h : T' ⟶ T` of test objects, the base change `τ^*(R_T N) ⟶ R_{T'}(φ^* N)` of the
Zariski reading (`AlgebraicGeometry.Space.zariskiReadingPullbackHom`, in its transposed form) is,
through the identifications of the Zariski readings with the restrictions of the modules read on
the schemes, the comparison `r^*(𝒢|_Zar) ≅ (g^*𝒢)|_Zar` of
`AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso` followed by the restriction of the mate
of `AlgebraicGeometry.Space.representedSquareModulePullbackIso`, as soon as the identification of
the sections of a direct image over Zariski opens is compatible with the conjugate of that
square (the hypothesis of the implication).

## Main results

* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_app_eq_of_sections`: that description.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (h : T' ⟶ T)

set_option maxHeartbeats 400000 in
-- Checking the proof term against the statement, which states the type of the same term, unfolds
-- the categories of modules involved and takes more than the default budget.
/-- The description of the transposed base change of the Zariski reading, as a term whose type
fixes the spelling of the categories of modules. -/
theorem zariskiReadingPullbackHomAppAux : type_of% fun (hH : _)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) =>
  Adjunction.comp_homEquiv_symm_eq_of_equivalenceMate _ (representedReindexEquivalence B S hS T) _
    (Stacks.RingedSpace.pullbackAdjunction (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map h)))
    (representedReindexEquivalence B S hS T') _
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (zariskiReadingIso T) (zariskiReadingIso T')
    (Functor.whiskerRight
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).pushforwardModulesIso.hom
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)) ≫
      zariskiDirectImageNatTrans h)
    (SheafOfModules.pushforwardSquareIso.{u}
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        h.left).toRingCatSheafHom
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
        T'.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
        T.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
        h.left)
      (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B) h.left)
      (_root_.AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso
        (associatedBigEtaleSite B) h.left)) _
    (conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp h)
    hH N _
    (_root_.AlgebraicGeometry.SmallEtale.homEquiv_restrictModulePullbackObjIso_hom
      (associatedBigEtaleSite B) h.left _
      (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T N hN)) :=
  (fun (hH : _)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) =>
  Adjunction.comp_homEquiv_symm_eq_of_equivalenceMate _ (representedReindexEquivalence B S hS T) _
    (Stacks.RingedSpace.pullbackAdjunction (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map h)))
    (representedReindexEquivalence B S hS T') _
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (zariskiReadingIso T) (zariskiReadingIso T')
    (Functor.whiskerRight
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).pushforwardModulesIso.hom
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)) ≫
      zariskiDirectImageNatTrans h)
    (SheafOfModules.pushforwardSquareIso.{u}
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        h.left).toRingCatSheafHom
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
        T'.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) _
        T.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B)
        h.left)
      (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B) h.left)
      (_root_.AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso
        (associatedBigEtaleSite B) h.left)) _
    (conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp h)
    hH N _
    (_root_.AlgebraicGeometry.SmallEtale.homEquiv_restrictModulePullbackObjIso_hom
      (associatedBigEtaleSite B) h.left _
      (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T N hN)) :)

/-- **The base change of the Zariski reading through the comparisons of Stacks 04M0**, granted
the sections comparison `AlgebraicGeometry.Space.zariskiDirectImageNatTrans` against the conjugate
of `representedSquareModulePullbackIso`. -/
theorem zariskiReadingPullbackHom_app_eq_of_sections
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    type_of% (fun hH => zariskiReadingPullbackHomAppAux h hH N hN) :=
  fun hH => zariskiReadingPullbackHomAppAux h hH N hN

end AlgebraicGeometry.Space
