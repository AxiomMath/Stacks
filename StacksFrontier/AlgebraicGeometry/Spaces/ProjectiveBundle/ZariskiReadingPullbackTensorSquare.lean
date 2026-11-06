module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceTensorPointPaste
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingReindexTopos

/-!
# The base change of the Zariski reading with comparisons that are the identity on sections

The comparison `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral` of the
two pushforwards of sheaves of modules along a morphism of ringed sites is the identity on
sections only up to a proved equation: its first factor is a transport along an equality of
functors.  Here the same comparison is rebuilt with components made from the identity of the
underlying sheaves of sets, so that it is the identity on sections by definition, and shown equal
to the original one.  The conjugate of `representedSquareModulePullbackIso` and the description of
the base change of the Zariski reading through
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos` are restated with these comparisons,
so that every factor of the sections comparison is definitional on sections.

## Main definitions

* `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoSections`: the comparison of
  the two pushforwards, the identity on sections by definition.
* `AlgebraicGeometry.Space.representedReindexPushforwardIsoSections`,
  `AlgebraicGeometry.Space.representedSchemeBaseChangePushforwardIsoSections`: its instances at the
  reindexing of a test object and at base change of schemes.

## Main results

* `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoSections_eq`.
* `CategoryTheory.Adjunction.equivalenceMateCompat_comp_of_app`: the sections compatibility for a
  comparison of right adjoints made of five comparisons, from its components.
* `AlgebraicGeometry.Space.conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp_sections`.
* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_app_eq_of_sections_sections`: the description
  of the transposed base change of the Zariski reading, granted the sections comparison.
* `CategoryTheory.Adjunction.equivalenceMateCompat_of_val_app`: the sections comparison with values
  in sheaves of modules from its two sides on sections.
* `AlgebraicGeometry.Space.zariskiReadingSectionsCompat`: the sections comparison itself.
* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_app_eq_sections`: the description of the
  transposed base change of the Zariski reading, unconditionally.
* `Space.pullback_map_zariskiReadingIsoTopos_hom_app_comp_zariskiReadingPullbackHom_app`: the
  same description for `AlgebraicGeometry.Space.zariskiReadingPullbackHom` itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedSite

universe uX vX uY vY w

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (f : HomGeneral X Y)

/-- The component at `N` of `pushforwardModulesToposIsoSections`. -/
def HomGeneral.pushforwardModulesToposObjIsoSections
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)) :
    (pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).obj N ≅
      f.toRingedToposSiteHom.pushforwardTopos.obj N where
  hom := ofSheafHom (𝟙 _)
    (fun Z x y => by
      have e := Sheaf.sectionsFunctor_map_moduleSheafFunctor_map_add _
        (f.pushforwardModulesToposIsoGeneral.hom.app N) Z x y
      rwa [f.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_hom_app N] at e)
    (fun Z r x => by
      have e := Sheaf.sectionsFunctor_map_moduleSheafFunctor_map_smul _
        (f.pushforwardModulesToposIsoGeneral.hom.app N) Z r x
      rwa [f.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_hom_app N] at e)
  inv := ofSheafHom (𝟙 _)
    (fun Z x y => by
      have e := Sheaf.sectionsFunctor_map_moduleSheafFunctor_map_add _
        (f.pushforwardModulesToposIsoGeneral.inv.app N) Z x y
      rwa [f.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_inv_app N] at e)
    (fun Z r x => by
      have e := Sheaf.sectionsFunctor_map_moduleSheafFunctor_map_smul _
        (f.pushforwardModulesToposIsoGeneral.inv.app N) Z r x
      rwa [f.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_inv_app N] at e)
  hom_inv_id := hom_ext_moduleSheafFunctor rfl
  inv_hom_id := hom_ext_moduleSheafFunctor rfl

/-- `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral` with components
built from the identity of the underlying sheaves of sets, so that it is the identity on
sections by definition. -/
def HomGeneral.pushforwardModulesToposIsoSections :
    pushforwardModules f.toRingedToposHom.toRingedToposModulesHom ≅
      f.toRingedToposSiteHom.pushforwardTopos :=
  NatIso.ofComponents f.pushforwardModulesToposObjIsoSections
    fun _ => hom_ext_moduleSheafFunctor rfl

/-- `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoSections` is
`AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral`: both are the identity
on underlying sheaves of sets. -/
theorem HomGeneral.pushforwardModulesToposIsoSections_eq :
    f.pushforwardModulesToposIsoSections = f.pushforwardModulesToposIsoGeneral :=
  Iso.ext (NatTrans.ext (funext fun N => hom_ext_moduleSheafFunctor
    (f.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_hom_app N).symm))

end AlgebraicGeometry.RingedSite

namespace CategoryTheory.Adjunction


variable {𝒵 𝒴₂ 𝒳 Ec' Z Z' : Type*} [Category 𝒵] [Category 𝒴₂] [Category 𝒳]
  [Category Ec'] [Category Z] [Category Z']
  {φp : 𝒳 ⥤ 𝒴₂} {gp : Ec' ⥤ 𝒵} {τp : Z' ⥤ Z} {zR : 𝒴₂ ⥤ Z} {zR' : 𝒳 ⥤ Z'}
  (E : 𝒵 ≌ 𝒴₂) (E' : Ec' ≌ 𝒳) (r : 𝒵 ⥤ Z) (r' : Ec' ⥤ Z')
  (ι : E.inverse ⋙ r ≅ zR) (ι' : E'.inverse ⋙ r' ≅ zR') (zDI : φp ⋙ zR ⟶ zR' ⋙ τp)
  (R1 : gp ⋙ r ≅ r' ⋙ τp)
  {ψ₂r : 𝒴₂ ⥤ 𝒵} {χr : 𝒳 ⥤ 𝒵} {φ₁r : 𝒳 ⥤ Ec'} {ψ₁r : Ec' ⥤ 𝒵}
  (Pψ₂ : ψ₂r ≅ E.inverse) (τ₂ : φp ⋙ ψ₂r ≅ χr) (τ₁ : φ₁r ⋙ ψ₁r ≅ χr) (Pψ₁ : ψ₁r ≅ gp)
  (Pφ₁ : φ₁r ≅ E'.inverse)

/-- The compatibility `EquivalenceMateCompat` for a comparison of right adjoints which is a
composite of five comparisons, from its components. -/
theorem equivalenceMateCompat_comp_of_app
    (H : ∀ M₀ : 𝒳, ι.hom.app (φp.obj M₀) ≫ zDI.app M₀ =
      r.map (Pψ₂.inv.app (φp.obj M₀)) ≫ r.map (τ₂.hom.app M₀) ≫ r.map (τ₁.inv.app M₀) ≫
        r.map (Pψ₁.hom.app (φ₁r.obj M₀)) ≫ r.map (gp.map (Pφ₁.hom.app M₀)) ≫
          R1.hom.app (E'.inverse.obj M₀) ≫ τp.map (ι'.hom.app M₀)) :
    EquivalenceMateCompat E E' r r' ι ι' zDI R1
      (Functor.whiskerLeft φp Pψ₂.inv ≫ τ₂.hom ≫ τ₁.inv ≫ Functor.whiskerLeft φ₁r Pψ₁.hom ≫
        Functor.whiskerRight Pφ₁.hom gp) := fun M₀ => by
  rw [H M₀]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]

end CategoryTheory.Adjunction

universe u

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- A composite of two morphisms of sheaves of modules equal on sections to seven morphisms
applied in turn is their composite. -/
theorem comp_eq_comp_of_val_app_apply₇ {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M₀ L M₁ M₂ M₃ M₄ M₅ M₆ M₇ : _root_.SheafOfModules.{u} R}
    (s₁ : M₀ ⟶ L) (s₂ : L ⟶ M₇) (f₁ : M₀ ⟶ M₁) (f₂ : M₁ ⟶ M₂) (f₃ : M₂ ⟶ M₃) (f₄ : M₃ ⟶ M₄)
    (f₅ : M₄ ⟶ M₅) (f₆ : M₅ ⟶ M₆) (f₇ : M₆ ⟶ M₇)
    (h : ∀ V x, s₂.val.app V (s₁.val.app V x) = f₇.val.app V (f₆.val.app V (f₅.val.app V
      (f₄.val.app V (f₃.val.app V (f₂.val.app V (f₁.val.app V x))))))) :
    s₁ ≫ s₂ = f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ ≫ f₇ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => h V x))

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The direct image of modules along the reindexing of `U` is the inverse of
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos`, by a comparison which is the
identity on sections by definition. -/
abbrev representedReindexPushforwardIsoSections (U : BigFppfOver B S hS) :
    pushforwardModules.{u, u, u, u + 1, u, u + 1} (representedReindexHom B S hS U) ≅
      (representedReindexEquivalenceTopos U).inverse :=
  (representedReindexRingedSiteHom U).pushforwardModulesToposIsoSections

/-- The conjugate of the identification of the pullback along the reindexing of `U` is the
inverse of `AlgebraicGeometry.Space.representedReindexPushforwardIsoSections`. -/
theorem conjugateEquiv_representedReindexPullbackIso_hom_sections (U : BigFppfOver B S hS) :
    conjugateEquiv (representedReindexEquivalenceTopos U).toAdjunction
      (pullbackAdjPushforwardModules (representedReindexHom B S hS U))
      (representedReindexPullbackIso B S hS U).hom =
    (representedReindexPushforwardIsoSections U).inv :=
  (conjugateEquiv_representedReindexPullbackIso_hom_topos U).trans
    (congrArg Iso.inv
      (representedReindexRingedSiteHom U).pushforwardModulesToposIsoSections_eq.symm)

variable {T T' : BigFppfOver B S hS} (h : T' ⟶ T)

/-- The direct image of modules along base change of schemes is that along the morphism of
ringed sites of Stacks 070R (2), by a comparison which is the identity on sections by
definition. -/
abbrev representedSchemeBaseChangePushforwardIsoSections :
    pushforwardModules.{u, u, u, u + 1, u, u + 1} (representedSchemeBaseChangeHom B S hS h) ≅
      (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        h.left).toRingedToposSiteHom.pushforwardTopos :=
  (smallEtaleRingedSiteHom (associatedBigEtaleSite B) h.left).pushforwardModulesToposIsoSections

/-- The conjugate of the identification of the pullback along base change of schemes is the
inverse of `AlgebraicGeometry.Space.representedSchemeBaseChangePushforwardIsoSections`. -/
theorem conjugateEquiv_pullbackModulesBaseChangeIso_hom_sections :
    conjugateEquiv
      (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        h.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
      (pullbackAdjPushforwardModules (representedSchemeBaseChangeHom B S hS h))
      (representedSchemeBaseChangePullbackIso B S hS h).hom =
    (representedSchemeBaseChangePushforwardIsoSections h).inv :=
  (conjugateEquiv_pullbackModulesBaseChangeIso_hom B S hS h).trans
    (congrArg Iso.inv (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
      h.left).pushforwardModulesToposIsoSections_eq.symm)

/-- The conjugate of `representedSquareModulePullbackIso` through the equivalences
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos`, with comparisons which are the
identity on sections by definition, as a term whose type fixes the spelling of the categories of
modules. -/
def conjugateEquivRepresentedSquareSectionsAux :=
  Adjunction.conjugateEquiv_factorizationIso_hom_equivalence
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
    (representedSchemeBaseChangePushforwardIsoSections h)
    (representedReindexPushforwardIsoSections T') (representedReindexPushforwardIsoSections T)
    (conjugateEquiv_representedSchemeRoutePullbackCompIso_hom B S hS h)
    (conjugateEquiv_representedSpaceRoutePullbackCompIso_hom B S hS h
      (relativelyRepresentable_yoneda_map B S hS h))
    (conjugateEquiv_pullbackModulesBaseChangeIso_hom_sections h)
    (conjugateEquiv_representedReindexPullbackIso_hom_sections T')
    (conjugateEquiv_representedReindexPullbackIso_hom_sections T)

/-- **The conjugate of `representedSquareModulePullbackIso`** through the equivalences
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos` is the composite of the comparisons
of direct images round the square of `h`, each of which is definitional on sections except the
comparison of composite direct images along the lower route. -/
theorem conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp_sections :
    type_of% (conjugateEquivRepresentedSquareSectionsAux h) :=
  conjugateEquivRepresentedSquareSectionsAux h

/-- The description of the transposed base change of the Zariski reading through
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos` and
`AlgebraicGeometry.Space.conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp_sections`,
as a term whose type fixes the spelling of the categories of modules. -/
def zariskiReadingPullbackHomAppSectionsAux := fun (hH : _)
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
    (conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp_sections h)
    hH N _
    (_root_.AlgebraicGeometry.SmallEtale.homEquiv_restrictModulePullbackObjIso_hom
      (associatedBigEtaleSite B) h.left _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN))

/-- **The base change of the Zariski reading through the comparisons of Stacks 04M0**, read
through `AlgebraicGeometry.Space.representedReindexEquivalenceTopos` with comparisons which are
the identity on sections by definition, granted the sections comparison of
`AlgebraicGeometry.Space.zariskiDirectImageNatTrans` against the conjugate of
`representedSquareModulePullbackIso`. -/
theorem zariskiReadingPullbackHom_app_eq_of_sections_sections
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    type_of% (fun hH => zariskiReadingPullbackHomAppSectionsAux h hH N hN) :=
  fun hH => zariskiReadingPullbackHomAppSectionsAux h hH N hN

end AlgebraicGeometry.Space

namespace CategoryTheory.Adjunction

/-- The compatibility `EquivalenceMateCompat` with values in sheaves of modules, from its two
sides computed on sections through a common intermediate value. -/
theorem equivalenceMateCompat_of_val_app
    {𝒵 𝒴₂ 𝒳 Ec' Z' : Type*} [Category 𝒵] [Category 𝒴₂] [Category 𝒳] [Category Ec']
    [Category Z'] {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {φp : 𝒳 ⥤ 𝒴₂} {gp : Ec' ⥤ 𝒵} {τp : Z' ⥤ _root_.SheafOfModules.{u} R}
    {zR : 𝒴₂ ⥤ _root_.SheafOfModules.{u} R} {zR' : 𝒳 ⥤ Z'} {E : 𝒵 ≌ 𝒴₂} {E' : Ec' ≌ 𝒳}
    {r : 𝒵 ⥤ _root_.SheafOfModules.{u} R} {r' : Ec' ⥤ Z'} {ι : E.inverse ⋙ r ≅ zR}
    {ι' : E'.inverse ⋙ r' ≅ zR'} {zDI : φp ⋙ zR ⟶ zR' ⋙ τp} {R1 : gp ⋙ r ≅ r' ⋙ τp}
    {κ : φp ⋙ E.inverse ⟶ E'.inverse ⋙ gp}
    (Ψ : ∀ (M₀ : 𝒳) (V : Cᵒᵖ), (r.obj (E.inverse.obj (φp.obj M₀))).val.obj V →
      (r.obj (gp.obj (E'.inverse.obj M₀))).val.obj V)
    (Θ : ∀ (M₀ : 𝒳) (V : Cᵒᵖ), (r.obj (gp.obj (E'.inverse.obj M₀))).val.obj V →
      (τp.obj (zR'.obj M₀)).val.obj V)
    (Φ : ∀ (M₀ : 𝒳) (V : Cᵒᵖ), (r.obj (E.inverse.obj (φp.obj M₀))).val.obj V →
      (τp.obj (zR'.obj M₀)).val.obj V)
    (hL : ∀ M₀ V x, (zDI.app M₀).val.app V ((ι.hom.app (φp.obj M₀)).val.app V x) = Φ M₀ V x)
    (hΦ : ∀ M₀ V x, Φ M₀ V x = Θ M₀ V (Ψ M₀ V x))
    (hκ : ∀ M₀ V x, (r.map (κ.app M₀)).val.app V x = Ψ M₀ V x)
    (hR : ∀ M₀ V y, (τp.map (ι'.hom.app M₀)).val.app V ((R1.hom.app (E'.inverse.obj M₀)).val.app V
      y) = Θ M₀ V y) :
    EquivalenceMateCompat E E' r r' ι ι' zDI R1 κ := fun M₀ =>
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => (hL M₀ V x).trans ((hΦ M₀ V x).trans
      ((congrArg (Θ M₀ V) (hκ M₀ V x)).symm.trans (hR M₀ V _).symm))))

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The right-hand side of an equation. -/
abbrev eqRhs {α : Sort*} {a b : α} (_ : a = b) : α := b

/-- The hypothesis of an implication: a theorem stated as it fixes the spelling of the
hypothesis to that of the implication. -/
abbrev HypothesisOf {α β : Prop} (_ : α → β) : Prop := α

/-- The first hypothesis of a fourfold implication. -/
abbrev HypothesisOf₄₁ {α β γ δ ε : Prop} (_ : α → β → γ → δ → ε) : Prop := α

/-- The second hypothesis of a fourfold implication. -/
abbrev HypothesisOf₄₂ {α β γ δ ε : Prop} (_ : α → β → γ → δ → ε) : Prop := β

/-- The third hypothesis of a fourfold implication. -/
abbrev HypothesisOf₄₃ {α β γ δ ε : Prop} (_ : α → β → γ → δ → ε) : Prop := γ

/-- The fourth hypothesis of a fourfold implication. -/
abbrev HypothesisOf₄₄ {α β γ δ ε : Prop} (_ : α → β → γ → δ → ε) : Prop := δ

variable {T T' : BigFppfOver B S hS} (h : T' ⟶ T)

/-- The direct image along `τ` of the Zariski reading isomorphism of `T'` is the identity on
sections. -/
theorem pushforwardFunctor_map_zariskiReadingIsoTopos_hom_app_val_app
    (M₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O))
    (O) (y) :
    ((@CategoryTheory.Functor.map
        (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf
          ((BigFppfOver.toScheme B S hS).obj T').toRingedSpace))
        SheafOfModules.instCategory
        (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf
          ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))
        SheafOfModules.instCategory
        (Stacks.RingedSpace.pushforwardFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map h))) _ _
      ((@CategoryTheory.NatTrans.app
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O))
          SheafOfModules.instCategory
          (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf
            ((BigFppfOver.toScheme B S hS).obj T').toRingedSpace))
          SheafOfModules.instCategory _ _
      (@CategoryTheory.Iso.hom
          ((SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedTopos B S hS
                ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O)) ⥤
            (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf
              ((BigFppfOver.toScheme B S hS).obj T').toRingedSpace)))
          CategoryTheory.Functor.category _ _ (zariskiReadingIsoTopos T')) M₀))).val.app O) y = y :=
  rfl

/-- On sections over a Zariski open `O`, the Zariski reading of the conjugate of
`representedSquareModulePullbackIso` is the comparison of composite direct images along the lower
route over the étale open of `O`. -/
theorem restrictModule_map_conjugateEquivRepresentedSquareSections_app_val_app
    (M₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O))
    (O) (y) :
    ((@CategoryTheory.Functor.map
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
            T.left.property).toRingedTopos.O))
        SheafOfModules.instCategory
        (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf
          ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))
        SheafOfModules.instCategory
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property) _ _
      ((eqRhs (conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp_sections h)).app
        M₀)).val.app O) y =
    (((pushforwardModulesCompIso
        (X := (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩))
        (Y := (smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
        (Z := ((_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          (@ObjectProperty.FullSubcategory.obj _ _
            (schemeSizeBelow (associatedBigEtaleSite B).cutoff) T.left)
          (@ObjectProperty.FullSubcategory.property _ _
            (schemeSizeBelow (associatedBigEtaleSite B).cutoff) T.left)).toRingedTopos))
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h))
      (representedReindexHom B S hS T) (representedSquareHom B S hS h)
      (representedSquareDirectImageIso B S hS h (relativelyRepresentable_yoneda_map B S hS h))
      (fSharpSetComp_representedSquareDirectImageIso B S hS h
        (relativelyRepresentable_yoneda_map B S hS h))).hom.app M₀).val.app
      (op ((SmallEtale.opensToSmallEtale (associatedBigEtaleSite B) _ T.left.property).obj
        O.unop))) y := by
  with_unfolding_all rfl

/-- On sections, the comparison of composite direct images of modules along the lower route is the
comparison `representedSquareDirectImageIso` of the underlying sheaves of sets. -/
theorem pushforwardModulesCompIso_representedSquareDirectImageIso_hom_app_val_app
    (M₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩).O))
    (W) (y) :
    (((pushforwardModulesCompIso
        (X := (smallEtaleRingedTopos B S hS ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩))
        (Y := (smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))
        (Z := ((_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          (@ObjectProperty.FullSubcategory.obj _ _
            (schemeSizeBelow (associatedBigEtaleSite B).cutoff) T.left)
          (@ObjectProperty.FullSubcategory.property _ _
            (schemeSizeBelow (associatedBigEtaleSite B).cutoff) T.left)).toRingedTopos))
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h))
      (representedReindexHom B S hS T) (representedSquareHom B S hS h)
      (representedSquareDirectImageIso B S hS h (relativelyRepresentable_yoneda_map B S hS h))
      (fSharpSetComp_representedSquareDirectImageIso B S hS h
        (relativelyRepresentable_yoneda_map B S hS h))).hom.app M₀).val.app W) y =
      ((representedSquareDirectImageIso B S hS h
          (relativelyRepresentable_yoneda_map B S hS h)).hom.app
        ((Sheaf.moduleSheafFunctor (testRing T')).obj M₀)).hom.app W y :=
  rfl


/-- The sections over `W` of the comparison `representedSquareDirectImageIso`: the chart
comparison over `e_T⁻¹ W` followed by restriction along the inverse of
`representedEquivInverseBaseChangeIso`. -/
def representedSquareDirectImageSection
    (F : Sheaf (SmallEtale.topology B S hS (yoneda.obj T')) (Type u))
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ)
    (z : (Sheaf.sectionsFunctor (SmallEtale.topology B S hS (yoneda.obj T))
        (Opposite.op ((representedSmallEtaleEquivalence B S hS T).inverse.obj W.unop))).obj
          ((smallEtaleRingedToposModulesHom B S hS
            (representedSpaceMap B S hS h)).toToposHom.pushforward.obj F)) :
    F.obj.obj (op ((representedSmallEtaleEquivalence B S hS T').inverse.obj
        ((representedSchemeBaseChange B S hS h).obj W.unop))) :=
  F.obj.map
    ((representedEquivInverseBaseChangeIso B S hS h
      (relativelyRepresentable_yoneda_map B S hS h)).inv.app W.unop).op
    ((Sheaf.sectionsFunctor _
      (Opposite.op ((representedSmallEtaleEquivalence B S hS T).inverse.obj W.unop))).map
        ((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS h) ≪≫
          chartRanIso B S hS (representedSpaceMap B S hS h)
            (relativelyRepresentable_yoneda_map B S hS h)).hom.app F) z)

/-- On sections, `representedSquareDirectImageIso` is
`AlgebraicGeometry.Space.representedSquareDirectImageSection`. -/
theorem representedSquareDirectImageIso_hom_app_hom_app
    (F : Sheaf (SmallEtale.topology B S hS (yoneda.obj T')) (Type u))
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ) (z) :
    ((representedSquareDirectImageIso B S hS h
        (relativelyRepresentable_yoneda_map B S hS h)).hom.app F).hom.app W z =
      representedSquareDirectImageSection h F W z := by
  delta representedSquareDirectImageIso representedSquareDirectImageSection; rfl

/-- The sections compatibility of
`AlgebraicGeometry.Space.zariskiReadingPullbackHomAppSectionsAux` from its two sides and a
comparison of the two formulas, as a term whose type fixes the spelling of the four hypotheses. -/
def zariskiReadingSectionsCompatAux := fun (hL : _) (hΦ : _) (hκ : _) (hR : _) =>
  (Adjunction.equivalenceMateCompat_of_val_app
    (fun M₀ O x =>
      representedSquareDirectImageSection h ((Sheaf.moduleSheafFunctor (testRing T')).obj M₀)
        (op ((SmallEtale.opensToSmallEtale (associatedBigEtaleSite B) _ T.left.property).obj
          O.unop)) x)
    (fun M₀ O y =>
      ((Sheaf.moduleSheafFunctor (testRing T')).obj M₀).obj.map
        ((representedSmallEtaleEquivalence B S hS T').inverse.map
          ((SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B) h.left).hom.app O.unop)).op y)
    (fun M₀ O x =>
      ((Sheaf.moduleSheafFunctor (testRing T')).obj M₀).obj.map
        ((representedSmallEtaleEquivalence B S hS T').inverse.map
          ((SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B) h.left).hom.app O.unop)).op
      (((Sheaf.moduleSheafFunctor (testRing T')).obj M₀).obj.map
        ((representedEquivInverseBaseChangeIso B S hS h
            (relativelyRepresentable_yoneda_map B S hS h)).inv.app
          ((SmallEtale.opensToSmallEtale (associatedBigEtaleSite B) _ T.left.property).obj
            O.unop)).op
        ((Sheaf.sectionsFunctor _
        (Opposite.op ((representedSmallEtaleEquivalence B S hS T).inverse.obj
                ((SmallEtale.opensToSmallEtale (associatedBigEtaleSite B) _
                  T.left.property).obj O.unop)))).map
          ((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS h) ≪≫
            chartRanIso B S hS (representedSpaceMap B S hS h)
              (relativelyRepresentable_yoneda_map B S hS h)).hom.app
              ((Sheaf.moduleSheafFunctor (testRing T')).obj M₀)) x)))
    hL hΦ hκ hR : HypothesisOf (zariskiReadingPullbackHomAppSectionsAux h))

/-- The left-hand side of the sections compatibility: the identification of sections of the direct
image is restriction of the section given by the chart comparison, along the base change of the
chart of `O`. -/
theorem zariskiReadingSectionsCompat_directImage :
    HypothesisOf₄₁ (zariskiReadingSectionsCompatAux h) := by
  intro M₀ O x
  refine (congrArg
    (directImageSelfOpensSection h O.unop ((Sheaf.moduleSheafFunctor (testRing T')).obj M₀))
    (pushforwardModulesIso_hom_app_val_app B S hS (representedSpaceMap B S hS h) M₀ _ x)).trans ?_
  refine (directImageSelfOpensSection_eq_map h O.unop _ x
      ((representedSmallEtaleEquivalence B S hS T').inverse.map
          ((SmallEtale.baseChangeOpensIso (associatedBigEtaleSite B) h.left).hom.app O.unop) ≫
        (representedEquivInverseBaseChangeIso B S hS h
            (relativelyRepresentable_yoneda_map B S hS h)).inv.app
          ((SmallEtale.opensToSmallEtale (associatedBigEtaleSite B) _ T.left.property).obj
            O.unop))).trans ?_
  refine (Functor.map_comp_apply
    ((Sheaf.moduleSheafFunctor (testRing T')).obj M₀).obj _ _ _).trans ?_
  rfl

/-- The two formulas for the sections compatibility agree. -/
theorem zariskiReadingSectionsCompat_section :
    HypothesisOf₄₂ (zariskiReadingSectionsCompatAux h) := by
  intro M₀ O x
  delta representedSquareDirectImageSection
  rfl

/-- The Zariski reading of the conjugate of `representedSquareModulePullbackIso` on sections. -/
theorem zariskiReadingSectionsCompat_comparison :
    HypothesisOf₄₃ (zariskiReadingSectionsCompatAux h) := by
  intro M₀ O x
  refine (restrictModule_map_conjugateEquivRepresentedSquareSections_app_val_app h M₀ O x).trans ?_
  refine (pushforwardModulesCompIso_representedSquareDirectImageIso_hom_app_val_app h M₀
    (op ((SmallEtale.opensToSmallEtale (associatedBigEtaleSite B) _ T.left.property).obj O.unop))
    x).trans ?_
  exact representedSquareDirectImageIso_hom_app_hom_app h _ _ _

/-- The comparison of the two routes of direct images is restriction along the base change of
Zariski opens, on sections. -/
theorem zariskiReadingSectionsCompat_restriction :
    HypothesisOf₄₄ (zariskiReadingSectionsCompatAux h) := by
  intro M₀ O y
  refine (pushforwardFunctor_map_zariskiReadingIsoTopos_hom_app_val_app h M₀ O _).trans ?_
  rfl

/-- **The sections compatibility** of the identification of sections of direct images
`AlgebraicGeometry.Space.zariskiDirectImageNatTrans` with the conjugate of
`representedSquareModulePullbackIso` and the comparison of the two routes of direct images. -/
theorem zariskiReadingSectionsCompat : HypothesisOf (zariskiReadingPullbackHomAppSectionsAux h) :=
  zariskiReadingSectionsCompatAux h (zariskiReadingSectionsCompat_directImage h)
    (zariskiReadingSectionsCompat_section h) (zariskiReadingSectionsCompat_comparison h)
    (zariskiReadingSectionsCompat_restriction h)

/-- **The base change of the Zariski reading through the comparisons of Stacks 04M0**, read
through `AlgebraicGeometry.Space.representedReindexEquivalenceTopos`: the transposed base change at
`N` is the base change of modules followed by the reindexed mate and the Zariski reading. -/
theorem zariskiReadingPullbackHom_app_eq_sections
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    type_of% (zariskiReadingPullbackHomAppSectionsAux h (zariskiReadingSectionsCompat h) N hN) :=
  zariskiReadingPullbackHomAppSectionsAux h (zariskiReadingSectionsCompat h) N hN

end AlgebraicGeometry.Space

namespace CategoryTheory.Adjunction

variable {ℰ ℰ' 𝒵 𝒵' : Type*} [Category ℰ] [Category ℰ'] [Category 𝒵] [Category 𝒵']
  {φu : ℰ ⥤ ℰ'} {φl φl' : ℰ' ⥤ ℰ} {τu : 𝒵 ⥤ 𝒵'} {τl : 𝒵' ⥤ 𝒵} {Z : ℰ ⥤ 𝒵} {Z' : ℰ' ⥤ 𝒵'}

/-- The transposed comparison for an adjunction transported along an isomorphism of right
adjoints, through the untransported unit. -/
theorem transposeComparison_ofNatIsoRight (adjφ : φu ⊣ φl) (e : φl ≅ φl') (adjτ : τu ⊣ τl)
    (σ : φl' ⋙ Z ⟶ Z' ⋙ τl) (N : ℰ) :
    transposeComparison (adjφ.ofNatIsoRight e) adjτ σ N =
      (adjτ.homEquiv _ _).symm (Z.map (adjφ.unit.app N) ≫
        (Functor.whiskerRight e.hom Z ≫ σ).app (φu.obj N)) := by
  rw [NatTrans.comp_app, Functor.whiskerRight_app, ← Category.assoc, ← Z.map_comp]
  rfl

/-- `CategoryTheory.Adjunction.transposeComparison_ofNatIsoRight` after a morphism. -/
theorem comp_transposeComparison_ofNatIsoRight_eq (adjφ : φu ⊣ φl) (e : φl ≅ φl')
    (adjτ : τu ⊣ τl) (σ : φl' ⋙ Z ⟶ Z' ⋙ τl) (N : ℰ) {X : 𝒵'}
    (a : X ⟶ τu.obj (Z.obj N)) (b : X ⟶ Z'.obj (φu.obj N))
    (h : a ≫ (adjτ.homEquiv _ _).symm (Z.map (adjφ.unit.app N) ≫
        (Functor.whiskerRight e.hom Z ≫ σ).app (φu.obj N)) = b) :
    a ≫ transposeComparison (adjφ.ofNatIsoRight e) adjτ σ N = b := by
  rw [transposeComparison_ofNatIsoRight]; exact h

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {T T' : BigFppfOver B S hS} (h : T' ⟶ T)

/-- **The base change of the Zariski reading through the comparisons of Stacks 04M0**: after the
pullback of the Zariski reading isomorphism of `T`, the base change at `N` is the base change of
modules, the reindexed mate and the Zariski reading isomorphism of `T'`. -/
theorem pullback_map_zariskiReadingIsoTopos_hom_app_comp_zariskiReadingPullbackHom_app
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
        ((zariskiReadingIsoTopos T).hom.app N) ≫ (zariskiReadingPullbackHom h).app N =
      eqRhs (zariskiReadingPullbackHom_app_eq_sections h N hN) :=
  Adjunction.comp_transposeComparison_ofNatIsoRight_eq _ _ _ _ _ _ _
    (zariskiReadingPullbackHom_app_eq_sections h N hN)

end AlgebraicGeometry.Space
