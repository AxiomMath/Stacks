module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteSituation
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.AdjunctionQuotientCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModulePullback

/-!
# Reading the modules of the base changes of the Quot situation on `ℙⁿ_T`

For a test scheme `T` of the Quot situation `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ`
(`AlgebraicGeometry.ProjectiveQuot.quotSituation`), the base change `X_T` is the algebraic space
of `ℙⁿ_T` (`AlgebraicGeometry.ProjectiveQuot.projectiveSiteSpaceIso`).  A module on the small
étale site of `X_T` is read on the Zariski site of the scheme `ℙⁿ_T` by pulling it back along that
isomorphism and restricting it to the Zariski site
(`AlgebraicGeometry.Space.representedZariskiModule`). This reading is right adjoint to the
associated-module functor of Stacks 03DU followed by the transport back to `X_T`, and the
adjunction is an equivalence on quasi-coherent modules (Stacks 03DX), so the quotients of `F_T`
with quasi-coherent target correspond to those of the reading of `F_T`
(`CategoryTheory.Adjunction.QuotientCorrespondence`). The reading of `F_T` is `𝒪^{⊕ r}` on
`ℙⁿ_T`.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.siteReading`: the reading `Mod(X_T) ⥤ Mod(ℙⁿ_T)`.
* `AlgebraicGeometry.ProjectiveQuot.siteReadingAdjunction`: its left adjoint.
* `AlgebraicGeometry.ProjectiveQuot.siteReadingFreeIso`: `𝒪^{⊕ r} ≅` the reading of `F_T`.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.quotientCorrespondence_siteReadingAdjunction`: the adjunction
  matches quasi-coherent quotients on both sides.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n r : ℕ}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The unit of a composite of adjunctions is invertible where both units are. -/
theorem isIso_comp_unit_app {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟] [Category* ℰ]
    {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} {H : 𝒟 ⥤ ℰ} {I : ℰ ⥤ 𝒟} (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (X : 𝒞)
    [IsIso (adj₁.unit.app X)] [IsIso (adj₂.unit.app (F.obj X))] :
    IsIso ((adj₁.comp adj₂).unit.app X) := by
  rw [Adjunction.comp_unit_app]
  infer_instance

/-- The unit of an adjunction followed by an equivalence is invertible where the unit is. -/
private theorem isIso_comp_equivalence_unit_app {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟]
    [Category* ℰ] {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) (e : 𝒟 ≌ ℰ) (X : 𝒞)
    [IsIso (adj.unit.app X)] : IsIso ((adj.comp e.toAdjunction).unit.app X) :=
  isIso_comp_unit_app adj e.toAdjunction X

/-- The counit of an adjunction followed by an equivalence is invertible where the counit is. -/
private theorem isIso_comp_equivalence_counit_app {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟]
    [Category* ℰ] {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) (e : 𝒟 ≌ ℰ) (X : ℰ)
    [IsIso (adj.counit.app (e.inverse.obj X))] :
    IsIso ((adj.comp e.toAdjunction).counit.app X) := by
  rw [Adjunction.comp_counit_app]
  infer_instance

/-! ### The Zariski reading on a represented algebraic space, as an adjunction -/

variable (B) in
/-- The associated-module functor of Stacks 03DU on the small étale site of an object `W` of the
site, followed by the identification with the small étale site of `h_W`, is left adjoint to the
Zariski reading `AlgebraicGeometry.Space.representedZariskiModule`. -/
def zariskiAdjunction (W : BigFppfOver B integerBase B.contains_integerBase) :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((𝒯).obj W) W.left.property).comp
    (Space.representedSpaceModulesEquivalence B integerBase B.contains_integerBase W).toAdjunction

/-- The unit of `AlgebraicGeometry.ProjectiveQuot.zariskiAdjunction` is invertible at a
quasi-coherent module. -/
theorem isIso_zariskiAdjunction_unit_app (W : BigFppfOver B integerBase B.contains_integerBase)
    (M : ((𝒯).obj W).Modules) (hM : SheafOfModules.IsQuasicoherent M) :
    IsIso ((zariskiAdjunction B W).unit.app M) := by
  have := _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite B)
    ((𝒯).obj W) W.left.property ⟨M, hM⟩
  exact isIso_comp_equivalence_unit_app _ _ M

/-- The counit of `AlgebraicGeometry.ProjectiveQuot.zariskiAdjunction` is invertible at a
quasi-coherent module. -/
theorem isIso_zariskiAdjunction_counit_app (W : BigFppfOver B integerBase B.contains_integerBase)
    (N : Space.Modules.{u, u} B integerBase B.contains_integerBase (yoneda.obj W)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W))
    (hN : N.IsQuasicoherentOnSite) :
    IsIso ((zariskiAdjunction B W).counit.app N) := by
  let E := Space.representedSpaceModulesEquivalence B integerBase B.contains_integerBase W
  have hG : (E.inverse.obj N).IsQuasicoherentOnSite :=
    Space.isQuasicoherentOnSite_representedSmallEtaleInverse B integerBase B.contains_integerBase
      W N hN
  have := _root_.AlgebraicGeometry.SmallEtale.isIso_counit (associatedBigEtaleSite B)
    ((𝒯).obj W) W.left.property (E.inverse.obj N) hG
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule
      (associatedBigEtaleSite B) ((𝒯).obj W) W.left.property (E.inverse.obj N) hG)
  exact isIso_comp_equivalence_counit_app _ E N

/-! ### The reading of the modules of a base change -/

variable (r) in
/-- The equivalence of module categories induced by `h_{ℙⁿ_T} ≅ X_T`. -/
abbrev siteSpaceEquivalence (T : Space.SchemesOver (quotSituation B n r).Y) :=
  (Space.modulePushforwardCoherence B integerBase B.contains_integerBase).modulePullbackEquivalence
    (projectiveSiteSpaceIso r T)

variable (r) in
/-- **The reading on `ℙⁿ_T` of a module on the base change `X_T`**: pull back along
`h_{ℙⁿ_T} ≅ X_T`, read on the small étale site of the scheme `ℙⁿ_T`, restrict to its Zariski
site. -/
abbrev siteReading (T : Space.SchemesOver (quotSituation B n r).Y) :
    Space.Modules.{u, u} B integerBase B.contains_integerBase ((quotSituation B n r).space T).1
        ((quotSituation B n r).space T).2 ⥤
      ((𝒯).obj (projectiveSite B n T.left)).Modules :=
  (siteSpaceEquivalence r T).symm.inverse ⋙
    ((Space.representedSpaceModulesEquivalence B integerBase B.contains_integerBase
      (projectiveSite B n T.left)).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property)

/-- The counit of the reading adjunction is invertible at a quasi-coherent module. -/
theorem isIso_siteReadingAdjunction_counit_app (T : Space.SchemesOver (quotSituation B n r).Y)
    (A : Space.Modules.{u, u} B integerBase B.contains_integerBase ((quotSituation B n r).space T).1
        ((quotSituation B n r).space T).2) (hA : A.IsQuasicoherentOnSite) :
    IsIso (((zariskiAdjunction B (projectiveSite B n T.left)).comp
      (siteSpaceEquivalence r T).symm.toAdjunction).counit.app A) := by
  have hA' := Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
    B.contains_integerBase (projectiveSiteSpaceIso r T).hom A hA
  have := isIso_zariskiAdjunction_counit_app (projectiveSite B n T.left)
    ((siteSpaceEquivalence r T).symm.inverse.obj A) hA'
  exact isIso_comp_equivalence_counit_app _ _ A

/-- The unit of the reading adjunction is invertible at a quasi-coherent module. -/
theorem isIso_siteReadingAdjunction_unit_app (T : Space.SchemesOver (quotSituation B n r).Y)
    (M : ((𝒯).obj (projectiveSite B n T.left)).Modules)
    (hM : SheafOfModules.IsQuasicoherent M) :
    IsIso (((zariskiAdjunction B (projectiveSite B n T.left)).comp
      (siteSpaceEquivalence r T).symm.toAdjunction).unit.app M) := by
  have := isIso_zariskiAdjunction_unit_app (projectiveSite B n T.left) M hM
  exact isIso_comp_equivalence_unit_app _ _ M

/-- The reading of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_siteReading_obj (T : Space.SchemesOver (quotSituation B n r).Y)
    (A : Space.Modules.{u, u} B integerBase B.contains_integerBase ((quotSituation B n r).space T).1
        ((quotSituation B n r).space T).2) (hA : A.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent ((siteReading r T).obj A) :=
  _root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule
    (associatedBigEtaleSite B) _ _ _
    (Space.isQuasicoherentOnSite_representedSmallEtaleInverse B integerBase
      B.contains_integerBase _ _
      (Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
        B.contains_integerBase (projectiveSiteSpaceIso r T).hom A hA))

/-- **The reading on `ℙⁿ_T` matches quasi-coherent quotients on both sides** (Stacks 03DX). -/
theorem quotientCorrespondence_siteReadingAdjunction
    (T : Space.SchemesOver (quotSituation B n r).Y) :
    ((zariskiAdjunction B (projectiveSite B n T.left)).comp
      (siteSpaceEquivalence r T).symm.toAdjunction).QuotientCorrespondence
        (fun M => M.IsQuasicoherentOnSite)
        (fun L => SheafOfModules.IsQuasicoherent L) where
  isIso_counit A hA := isIso_siteReadingAdjunction_counit_app T A hA
  isIso_unit M hM := isIso_siteReadingAdjunction_unit_app T M hM
  map_right A hA := isQuasicoherent_siteReading_obj T A hA
  map_left M hM :=
    Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
      B.contains_integerBase (projectiveSiteSpaceIso r T).inv _
      (Space.isQuasicoherentOnSite_associatedModule_schemeSpace (projectiveSite B n T.left) M hM)
  cokernel_mem f hM hM' := by
    have := hM
    have := hM'
    exact Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel f
  of_iso_left e h := SheafOfModules.IsQuasicoherentOnSite.of_iso e h
  of_iso_right e h := (SheafOfModules.isQuasicoherent _).prop_of_iso e h

/-! ### The reading of `F_T` is `𝒪^{⊕ r}` -/

/-- The morphism `X_T ⟶ X` read on `h_{ℙⁿ_T}` is the morphism of algebraic spaces represented by
`ℙⁿ_T ⟶ ℙⁿ_ℤ`. -/
theorem projectiveSiteSpaceIso_hom_sourceProjection_eq_representedSpaceMap
    (T : Space.SchemesOver (quotSituation B n r).Y) :
    (projectiveSiteSpaceIso r T).hom ≫ (quotSituation B n r).sourceProjection T =
      Space.representedSpaceMap B integerBase B.contains_integerBase
        (projectiveSiteMap B n (toSiteBase B T.left)) :=
  projectiveSiteSpaceIso_hom_sourceProjection T

variable (r) in
/-- **The reading of `F_T` on `ℙⁿ_T` is `𝒪^{⊕ r}`.**  The free module of `ℙⁿ_T` is the pullback
of that of `ℙⁿ_ℤ`, which is the Zariski reading of `F` (Stacks 03DX); the Zariski reading commutes
with pullback along `ℙⁿ_T ⟶ ℙⁿ_ℤ`
(`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`), and the pullback of `F` along
`h_{ℙⁿ_T} ⟶ X` is the pullback of `F_T` along `h_{ℙⁿ_T} ≅ X_T`. -/
def siteReadingFreeIso (T : Space.SchemesOver (quotSituation B n r).Y) :
    freeModule n r ((𝒯).obj T.left) ≅
      (siteReading r T).obj ((quotSituation B n r).baseChangeModule T) :=
  (freeModulePullbackIso n r ((𝒯).map (toSiteBase B T.left))).symm ≪≫
    (Scheme.Modules.pullback (projectiveSpaceOverMap n ((𝒯).map (toSiteBase B T.left)))).mapIso
      (Space.representedZariskiModuleQuasicoherentSchemeIso B integerBase B.contains_integerBase
        (projectiveSiteBase B n)
        ⟨freeModule n r integerBase, isQuasicoherent_freeModule n r _⟩).symm ≪≫
    Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase
      (projectiveSiteMap B n (toSiteBase B T.left))
      (Functor.relativelyRepresentable.map yoneda _) (siteFreeModuleQcoh B n r).obj
      (siteFreeModuleQcoh B n r).property ≪≫
    ((Space.representedSpaceModulesEquivalence B integerBase B.contains_integerBase
        (projectiveSite B n T.left)).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).mapIso
      ((Space.modulePullbackTriangle B integerBase B.contains_integerBase
        (projectiveSiteSpaceIso_hom_sourceProjection_eq_representedSpaceMap T)).app
          (siteFreeModuleQcoh B n r).obj)

end AlgebraicGeometry.ProjectiveQuot

end
