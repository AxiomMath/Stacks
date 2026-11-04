module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompJoin
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedModuleLiftPullback
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqCocycle
public import StacksFrontier.CategoryTheory.Functor.SquareIsoPasting
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposUniq
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Étale restriction and the transport to the spaces-étale site, compatibly with composition

For morphisms `g : Z ⟶ Y` and `f : Y ⟶ X` of algebraic spaces, the identification of the
pullback of modules along the morphism of spaces-étale ringed topoi of `f` with the pullback
along the site-presented morphism `f_{small}` is compatible with the composition isomorphisms of
both pullbacks; consequently, for étale `f` and `g`, the isomorphisms `ι(f^*M) ≅ f^*(ιM)` of
`AlgebraicGeometry.BigEtaleSpaceSite.etaleModulePullbackCompToSpacesEtaleModulesIso` paste along
composition.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtalePushforwardModulesIsoPushforwardTopos_comp`: the
  compatibility of the comparisons of direct images, on sections.
* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtalePullbackModulesIsoPullbackTopos_comp`: the
  compatibility of the comparisons of pullbacks.
* `AlgebraicGeometry.BigEtaleSpaceSite.etaleModulePullbackCompToSpacesEtaleModulesIso_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.BigEtaleSpaceSite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Space.SmallEtale.instHasSheafify
  Space.SmallEtale.instWEqualsLocallyBijective

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y Z : T.Spaces} (f : Y ⟶ X) (g : Z ⟶ Y)

open Space.SimplicialSpacesEtaleSite

/-- The two direct images of modules along the morphism of spaces-étale ringed topoi of `f`
agree. -/
def spacesEtalePushforwardModulesIsoPushforwardTopos :
    RingedToposHom.pushforwardModules (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
        (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
        (spacesEtaleRingedToposHom f) ≅
      (smallEtaleRingedSiteHom T f).pushforwardTopos :=
  (RingedSite.Hom.ofRingedToposSiteHom (smallEtaleRingedSiteHom T f)
    (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f)).pushforwardToposIso

/-- The identification of the two pullbacks of modules along `f` is the comparison of left
adjoints of their adjunctions, through the comparison of direct images. -/
theorem spacesEtalePullbackModulesIsoPullbackTopos_eq :
    spacesEtalePullbackModulesIsoPullbackTopos T f =
      Adjunction.leftAdjointUniq
        ((RingedToposHom.pullbackAdjPushforwardModules (spacesEtaleRingedToposHom f)).ofNatIsoRight
          (spacesEtalePushforwardModulesIsoPushforwardTopos T f))
        (smallEtaleRingedSiteHom T f).pullbackPushforwardAdjunctionTopos :=
  RingedSite.Hom.eqToIso_trans_pullbackModulesToposIso
    (RingedSite.Hom.ofRingedToposSiteHom (smallEtaleRingedSiteHom T f)
      (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f))

/-- **The comparisons of direct images are compatible with composition**: for `g : Z ⟶ Y` and
`f : Y ⟶ X`, the 2-isomorphism of Stacks 0DE7 for `g ≫ f`, the composition isomorphism of direct
images of modules and the comparisons for `f` and `g` give the comparison for `g ≫ f` followed by
the composition isomorphism of the site-presented direct images. All maps are the identity or
restriction along the isomorphism of iterated base changes on sections. -/
theorem spacesEtalePushforwardModulesIsoPushforwardTopos_comp
    (M : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z).O)) :
    (Space.spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp
        g f).pushforwardModulesIso.hom.app M ≫
      (RingedToposHom.pushforwardModulesCompIso (spacesEtaleRingedToposHom g)
        (spacesEtaleRingedToposHom f)).hom.app M ≫
      (spacesEtalePushforwardModulesIsoPushforwardTopos T f).hom.app
          ((RingedToposHom.pushforwardModules (spacesEtaleRingedToposHom g)).obj M) ≫
      (smallEtaleRingedSiteHom T f).pushforwardTopos.map
        ((spacesEtalePushforwardModulesIsoPushforwardTopos T g).hom.app M) =
    (spacesEtalePushforwardModulesIsoPushforwardTopos T (g ≫ f)).hom.app M ≫
      (smallEtaleRingedSiteHomPushforwardCompIso T g f).inv.app M := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  rfl

/-- **The comparison of the two pullbacks of modules is compatible with composition**: through
the composition isomorphisms of the pullbacks along the morphisms of spaces-étale ringed topoi
(Stacks 03D6 and the 2-isomorphism of Stacks 0DE7) and of the site-presented pullbacks. -/
theorem spacesEtalePullbackModulesIsoPullbackTopos_comp :
    ((RingedToposHom.pullbackModulesCompIso (spacesEtaleRingedToposHom g)
        (spacesEtaleRingedToposHom f)).symm ≪≫
      Space.spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp g f).hom ≫
      (spacesEtalePullbackModulesIsoPullbackTopos T (g ≫ f)).hom =
    Functor.whiskerRight (spacesEtalePullbackModulesIsoPullbackTopos T f).hom
        (spacesEtaleRingedToposHom g).toModulesHom.pullbackModules ≫
      Functor.whiskerLeft (smallEtaleRingedSiteHom T f).pullbackTopos
        (spacesEtalePullbackModulesIsoPullbackTopos T g).hom ≫
      (smallEtaleRingedSiteHomPullbackCompIso T g f).hom := by
  rw [spacesEtalePullbackModulesIsoPullbackTopos_eq T f,
    spacesEtalePullbackModulesIsoPullbackTopos_eq T g,
    spacesEtalePullbackModulesIsoPullbackTopos_eq T (g ≫ f)]
  have key := Stacks.CategoryTheory.leftAdjointUniq_comp_cocycle
    (RingedToposHom.pullbackAdjPushforwardModules (spacesEtaleRingedToposHom f))
    (RingedToposHom.pullbackAdjPushforwardModules (spacesEtaleRingedToposHom g))
    (RingedToposHom.pullbackAdjPushforwardModules (spacesEtaleRingedToposHom (g ≫ f)))
    (RingedToposHom.pullbackAdjPushforwardModules
      (RingedToposHom.comp (X := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
        (Y := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
        (Z := Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
        (spacesEtaleRingedToposHom f) (spacesEtaleRingedToposHom g)))
    (smallEtaleRingedSiteHom T f).pullbackPushforwardAdjunctionTopos
    (smallEtaleRingedSiteHom T g).pullbackPushforwardAdjunctionTopos
    (smallEtaleRingedSiteHom T (g ≫ f)).pullbackPushforwardAdjunctionTopos
    (spacesEtalePushforwardModulesIsoPushforwardTopos T f)
    (spacesEtalePushforwardModulesIsoPushforwardTopos T g)
    (spacesEtalePushforwardModulesIsoPushforwardTopos T (g ≫ f))
    (RingedToposHom.pushforwardModulesCompIso (spacesEtaleRingedToposHom g)
      (spacesEtaleRingedToposHom f))
    (Space.spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp
      g f).pushforwardModulesIso
    (smallEtaleRingedSiteHomPushforwardCompIso T g f)
    (spacesEtalePushforwardModulesIsoPushforwardTopos_comp T f g)
  exact key

/-- `ι(f^*M) ≅ f^*(ιM)` in layers. -/
theorem etaleModulePullbackCompToSpacesEtaleModulesIso_eq
    (hf : Space.IsEtale T.fppfSite S T.fppf_mem f.hom) :
    etaleModulePullbackCompToSpacesEtaleModulesIso T f hf =
      Functor.isoWhiskerRight
          (Space.modulePullbackIsoEtaleModulePullback T.fppfSite S T.fppf_mem f hf).symm _ ≪≫
        (asIso (toSpacesEtaleModulesPullbackHom T f)).symm ≪≫
        Functor.isoWhiskerLeft _ (spacesEtalePullbackModulesIsoPullbackTopos T f).symm :=
  rfl

/-- **Étale restriction commutes with `ι` compatibly with composition.** For étale
`g : Z ⟶ Y` and `f : Y ⟶ X`, the isomorphisms `ι(f^*M) ≅ f^*(ιM)` of
`AlgebraicGeometry.BigEtaleSpaceSite.etaleModulePullbackCompToSpacesEtaleModulesIso` paste, along
the strict composition of étale restrictions and the composition isomorphism of the pullbacks
of modules along the morphisms of spaces-étale ringed topoi, to the one for `g ≫ f`. -/
theorem etaleModulePullbackCompToSpacesEtaleModulesIso_comp
    (hf : Space.IsEtale T.fppfSite S T.fppf_mem f.hom)
    (hg : Space.IsEtale T.fppfSite S T.fppf_mem g.hom)
    (hgf : Space.IsEtale T.fppfSite S T.fppf_mem (g ≫ f).hom)
    (M : Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2) :
    (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem Z).map
        ((Space.etaleModulePullbackComp T.fppfSite S T.fppf_mem g f hg hf hgf).hom.app M) ≫
      (etaleModulePullbackCompToSpacesEtaleModulesIso T (g ≫ f) hgf).hom.app M =
    (etaleModulePullbackCompToSpacesEtaleModulesIso T g hg).hom.app
        ((Space.etaleModulePullback.{u, u} T.fppfSite S T.fppf_mem f hf).obj M) ≫
      (spacesEtaleRingedToposHom g).toModulesHom.pullbackModules.map
        ((etaleModulePullbackCompToSpacesEtaleModulesIso T f hf).hom.app M) ≫
      ((RingedToposHom.pullbackModulesCompIso (spacesEtaleRingedToposHom g)
        (spacesEtaleRingedToposHom f)).symm ≪≫
        Space.spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp g f).hom.app
        ((Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X).obj M) := by
  have ha := Space.modulePullbackCompIso_hom_comp_etaleRestriction T.fppfSite S T.fppf_mem
      g f hg hf hgf
      (Space.etaleModulePullbackCompAdjunction_unit T.fppfSite S T.fppf_mem g f hg hf hgf)
  have hb := fun N ↦ toSpacesEtaleModulesPullbackHom_comp_app T g f N
  have hc := spacesEtalePullbackModulesIsoPullbackTopos_comp T f g
  have key := Stacks.CategoryTheory.squareIso_pasting_of_layers
    (Space.modulePullbackIsoEtaleModulePullback T.fppfSite S T.fppf_mem f hf)
    (Space.modulePullbackIsoEtaleModulePullback T.fppfSite S T.fppf_mem g hg)
    (Space.modulePullbackIsoEtaleModulePullback T.fppfSite S T.fppf_mem (g ≫ f) hgf)
    (asIso (toSpacesEtaleModulesPullbackHom T f)) (asIso (toSpacesEtaleModulesPullbackHom T g))
    (asIso (toSpacesEtaleModulesPullbackHom T (g ≫ f)))
    (spacesEtalePullbackModulesIsoPullbackTopos T f)
    (spacesEtalePullbackModulesIsoPullbackTopos T g)
    (spacesEtalePullbackModulesIsoPullbackTopos T (g ≫ f))
    (Space.etaleModulePullbackComp T.fppfSite S T.fppf_mem g f hg hf hgf)
    (Space.modulePullbackCompIso T.fppfSite S T.fppf_mem g f)
    (smallEtaleRingedSiteHomPullbackCompIso T g f)
    ((RingedToposHom.pullbackModulesCompIso (spacesEtaleRingedToposHom g)
      (spacesEtaleRingedToposHom f)).symm ≪≫
      Space.spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp g f)
    ha hb hc M
  rw [etaleModulePullbackCompToSpacesEtaleModulesIso_eq T f hf,
    etaleModulePullbackCompToSpacesEtaleModulesIso_eq T g hg,
    etaleModulePullbackCompToSpacesEtaleModulesIso_eq T (g ≫ f) hgf]
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq key) (by heq_congr)))

end AlgebraicGeometry.BigEtaleSpaceSite

end
