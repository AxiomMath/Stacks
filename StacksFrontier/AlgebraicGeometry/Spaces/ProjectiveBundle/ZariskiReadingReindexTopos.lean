module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackSectionsCompat
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteHomGeneralPushforwardUnderlying

/-!
# The comparison of Stacks 04M0 with its inverse spelled as a direct image

The equivalence `AlgebraicGeometry.Space.representedReindexEquivalence` between modules on the
small étale site of the scheme underlying a test object `U` and on the small étale site of
`yoneda.obj U` has, as inverse, a direct image of modules that is definitionally, but not
syntactically, the direct image `f_*` of sheaves of modules along the morphism of ringed sites `f`
of the comparison.  Here the same equivalence is restated with `f_*` itself as its inverse, so
that `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral` is the comparison
of `f_*` with the direct image along the reindexing at its own type.  The conjugate of
`AlgebraicGeometry.Space.representedSquareModulePullbackIso`, the identification of Zariski
readings and the description of the base change of the Zariski reading are restated through it.

## Main definitions

* `AlgebraicGeometry.Space.representedReindexEquivalenceTopos`: the equivalence with inverse `f_*`.
* `AlgebraicGeometry.Space.representedReindexPushforwardIsoTopos`: the comparison of the direct
  image along the reindexing with `f_*`.
* `AlgebraicGeometry.Space.zariskiReadingIsoTopos`: the Zariski reading as restriction of `f_*`.

## Main results

* `AlgebraicGeometry.Space.conjugateEquiv_representedReindexPullbackIso_hom_topos`.
* `AlgebraicGeometry.Space.conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp_topos`.
* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_app_eq_of_sections_topos`: the description
  of the transposed base change of the Zariski reading, granted the sections comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The morphism of ringed sites of the comparison of Stacks 04M0. -/
abbrev representedReindexRingedSiteHom (U : BigFppfOver B S hS) :=
  Stacks.SheafOfModules.reindexRingedSiteHom (SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U) (representedSchemeCommRingStructureSheaf B S hS U)

/-- The equivalence of Stacks 04M0 with its inverse spelled as the direct image of modules along
the morphism of ringed sites. -/
abbrev representedReindexEquivalenceTopos (U : BigFppfOver B S hS) : @Equivalence
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
        U.left.property).toRingedTopos.O))
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)) _ _ where
  functor := (representedReindexEquivalence B S hS U).functor
  inverse := (representedReindexRingedSiteHom U).toRingedToposSiteHom.pushforwardTopos
  unitIso := (representedReindexEquivalence B S hS U).unitIso
  counitIso := (representedReindexEquivalence B S hS U).counitIso
  functor_unitIso_comp := (representedReindexEquivalence B S hS U).functor_unitIso_comp

/-- The direct image of modules along the reindexing of `U` is the inverse of
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos`. -/
abbrev representedReindexPushforwardIsoTopos (U : BigFppfOver B S hS) :
    pushforwardModules.{u, u, u, u + 1, u, u + 1} (representedReindexHom B S hS U) ≅
      (representedReindexEquivalenceTopos U).inverse :=
  (representedReindexRingedSiteHom U).pushforwardModulesToposIsoGeneral

/-- The conjugate of the identification of the pullback along the reindexing of `U` is the
inverse of `AlgebraicGeometry.Space.representedReindexPushforwardIsoTopos`. -/
theorem conjugateEquiv_representedReindexPullbackIso_hom_topos (U : BigFppfOver B S hS) :
    conjugateEquiv (representedReindexEquivalenceTopos U).toAdjunction
      (pullbackAdjPushforwardModules (representedReindexHom B S hS U))
      (representedReindexPullbackIso B S hS U).hom =
    (representedReindexPushforwardIsoTopos U).inv :=
  conjugateEquiv_representedReindexPullbackIso_hom B S hS U

variable {T T' : BigFppfOver B S hS} (h : T' ⟶ T)

set_option maxHeartbeats 400000 in
-- Checking the proof term against the statement, which states the type of the same term, unfolds
-- the categories of modules involved and takes more than the default budget.
/-- The conjugate of `representedSquareModulePullbackIso` through the equivalences
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos`, as a term whose type fixes the
spelling of the categories of modules. -/
theorem conjugateEquivRepresentedSquareToposAux : type_of%
  (Adjunction.conjugateEquiv_factorizationIso_hom_equivalence
    (pullbackAdjPushforwardModules (representedSquareHom B S hS h))
    (pullbackAdjPushforwardModules (representedSchemeBaseChangeHom B S hS h))
    (pullbackAdjPushforwardModules (representedReindexHom B S hS T'))
    (pullbackAdjPushforwardModules (representedReindexHom B S hS T))
    (pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)))
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
      h.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
    (representedReindexEquivalenceTopos T) (representedReindexEquivalenceTopos T')
    (representedSchemeRoutePullbackCompIso B S hS h)
    (representedSpaceRoutePullbackCompIso B S hS h (relativelyRepresentable_yoneda_map B S hS h))
    (pushforwardModulesCompIso (representedReindexHom B S hS T')
      (representedSchemeBaseChangeHom B S hS h) (representedSquareHom B S hS h) (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS h))
    (pushforwardModulesCompIso
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h))
      (representedReindexHom B S hS T) (representedSquareHom B S hS h)
      (representedSquareDirectImageIso B S hS h (relativelyRepresentable_yoneda_map B S hS h))
      (fSharpSetComp_representedSquareDirectImageIso B S hS h
        (relativelyRepresentable_yoneda_map B S hS h)))
    (representedSchemeBaseChangePullbackIso B S hS h)
    (representedReindexPullbackIso B S hS T') (representedReindexPullbackIso B S hS T)
    (representedSchemeBaseChangePushforwardIso B S hS h)
    (representedReindexPushforwardIsoTopos T') (representedReindexPushforwardIsoTopos T)
    (conjugateEquiv_representedSchemeRoutePullbackCompIso_hom B S hS h)
    (conjugateEquiv_representedSpaceRoutePullbackCompIso_hom B S hS h
      (relativelyRepresentable_yoneda_map B S hS h))
    (conjugateEquiv_pullbackModulesBaseChangeIso_hom B S hS h)
    (conjugateEquiv_representedReindexPullbackIso_hom_topos T')
    (conjugateEquiv_representedReindexPullbackIso_hom_topos T)) :=
  (Adjunction.conjugateEquiv_factorizationIso_hom_equivalence
    (pullbackAdjPushforwardModules (representedSquareHom B S hS h))
    (pullbackAdjPushforwardModules (representedSchemeBaseChangeHom B S hS h))
    (pullbackAdjPushforwardModules (representedReindexHom B S hS T'))
    (pullbackAdjPushforwardModules (representedReindexHom B S hS T))
    (pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)))
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
      h.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
    (representedReindexEquivalenceTopos T) (representedReindexEquivalenceTopos T')
    (representedSchemeRoutePullbackCompIso B S hS h)
    (representedSpaceRoutePullbackCompIso B S hS h (relativelyRepresentable_yoneda_map B S hS h))
    (pushforwardModulesCompIso (representedReindexHom B S hS T')
      (representedSchemeBaseChangeHom B S hS h) (representedSquareHom B S hS h) (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS h))
    (pushforwardModulesCompIso
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h))
      (representedReindexHom B S hS T) (representedSquareHom B S hS h)
      (representedSquareDirectImageIso B S hS h (relativelyRepresentable_yoneda_map B S hS h))
      (fSharpSetComp_representedSquareDirectImageIso B S hS h
        (relativelyRepresentable_yoneda_map B S hS h)))
    (representedSchemeBaseChangePullbackIso B S hS h)
    (representedReindexPullbackIso B S hS T') (representedReindexPullbackIso B S hS T)
    (representedSchemeBaseChangePushforwardIso B S hS h)
    (representedReindexPushforwardIsoTopos T') (representedReindexPushforwardIsoTopos T)
    (conjugateEquiv_representedSchemeRoutePullbackCompIso_hom B S hS h)
    (conjugateEquiv_representedSpaceRoutePullbackCompIso_hom B S hS h
      (relativelyRepresentable_yoneda_map B S hS h))
    (conjugateEquiv_pullbackModulesBaseChangeIso_hom B S hS h)
    (conjugateEquiv_representedReindexPullbackIso_hom_topos T')
    (conjugateEquiv_representedReindexPullbackIso_hom_topos T) :)

/-- **The conjugate of `representedSquareModulePullbackIso`** through the equivalences
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos` is the composite of the comparisons
of direct images round the square of `h`. -/
theorem conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp_topos :
    type_of% (conjugateEquivRepresentedSquareToposAux h) :=
  conjugateEquivRepresentedSquareToposAux h

/-- The Zariski reading, through `AlgebraicGeometry.Space.representedReindexEquivalenceTopos`, is
restriction of modules on the small étale site of the scheme to its Zariski site. -/
def zariskiReadingIsoTopos (U : BigFppfOver B S hS) :=
  NatIso.ofComponents (F := (representedReindexEquivalenceTopos U).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (selfOpensPushforwardIso B S hS U) fun _ =>
      SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => rfl)

/-- Quasi-coherence is carried by the inverse of
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos`. -/
theorem isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse (U : BigFppfOver B S hS)
    (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (hF : F.IsQuasicoherentOnSite) :
    ((representedReindexEquivalenceTopos U).inverse.obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_representedSmallEtaleInverse B S hS U F hF

set_option maxHeartbeats 400000 in
-- Checking the proof term against the statement, which states the type of the same term, unfolds
-- the categories of modules involved and takes more than the default budget.
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom) in
/-- The description of the transposed base change of the Zariski reading through
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos`, as a term whose type fixes the
spelling of the categories of modules. -/
theorem zariskiReadingPullbackHomAppToposAux : type_of% fun (hH : _)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) =>
  Adjunction.comp_homEquiv_symm_eq_of_equivalenceMate _ (representedReindexEquivalenceTopos T) _
    (Stacks.RingedSpace.pullbackAdjunction (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map h)))
    (representedReindexEquivalenceTopos T') _
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (zariskiReadingIsoTopos T) (zariskiReadingIsoTopos T')
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
    (conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp_topos h)
    hH N _
    (_root_.AlgebraicGeometry.SmallEtale.homEquiv_restrictModulePullbackObjIso_hom
      (associatedBigEtaleSite B) h.left _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)) :=
  (fun (hH : _)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) =>
  Adjunction.comp_homEquiv_symm_eq_of_equivalenceMate _ (representedReindexEquivalenceTopos T) _
    (Stacks.RingedSpace.pullbackAdjunction (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map h)))
    (representedReindexEquivalenceTopos T') _
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (zariskiReadingIsoTopos T) (zariskiReadingIsoTopos T')
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
    (conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp_topos h)
    hH N _
    (_root_.AlgebraicGeometry.SmallEtale.homEquiv_restrictModulePullbackObjIso_hom
      (associatedBigEtaleSite B) h.left _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)) :)

/-- **The base change of the Zariski reading through the comparisons of Stacks 04M0**, read
through `AlgebraicGeometry.Space.representedReindexEquivalenceTopos`, granted the sections
comparison of `AlgebraicGeometry.Space.zariskiDirectImageNatTrans` against the conjugate of
`representedSquareModulePullbackIso`. -/
theorem zariskiReadingPullbackHom_app_eq_of_sections_topos
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    type_of% (fun hH => zariskiReadingPullbackHomAppToposAux h hH N hN) :=
  fun hH => zariskiReadingPullbackHomAppToposAux h hH N hN

end AlgebraicGeometry.Space
