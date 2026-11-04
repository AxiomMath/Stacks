module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteReading
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.ReindexFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAllPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentSelfChart
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteIff
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FinitePresentationAgreement03DX

/-!
# Finite presentation and flatness, read on `ℙⁿ_T`

For a test scheme `T` of the Quot situation `𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ` and a quasi-coherent module `Q` on
the base change `X_T`, the reading `AlgebraicGeometry.ProjectiveQuot.siteReading` of `Q` on the
scheme `ℙⁿ_T` is of finite presentation exactly when `Q` is (Stacks 05VG), and flat over `T`
exactly when `Q` is flat over `T` in the sense of Stacks 05VV.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.isFinitePresentationOnSite_iff_siteReading`.
* `AlgebraicGeometry.ProjectiveQuot.isFlatOver_iff_siteReading`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n r : ℕ}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- **The two Zariski readings of a quasi-coherent module on a represented algebraic space
agree**: the restriction to the identity chart and the restriction of the small étale reading. -/
def representedZariskiRestrictionIsoModule (W : BigFppfOver B integerBase B.contains_integerBase)
    (N : Space.Modules.{u, u} B integerBase B.contains_integerBase (yoneda.obj W)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W))
    (hN : N.IsQuasicoherentOnSite) :
    Space.representedZariskiRestriction B integerBase B.contains_integerBase W
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W) N ≅
      Space.representedZariskiModule B integerBase B.contains_integerBase W N :=
  haveI := isIso_zariskiAdjunction_counit_app W N hN
  (Space.representedZariskiRestrictionIso B integerBase B.contains_integerBase W _
      (asIso ((zariskiAdjunction B W).counit.app N))).symm ≪≫
    Space.representedZariskiRestriction_representedQuasicoherentIso B integerBase
      B.contains_integerBase W _
      (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule
        (associatedBigEtaleSite B) _ _ _
        (Space.isQuasicoherentOnSite_representedSmallEtaleInverse B integerBase
          B.contains_integerBase W N hN))

variable (T : Space.SchemesOver (quotSituation B n r).Y)
  (Q : Space.Modules.{u, u} B integerBase B.contains_integerBase ((quotSituation B n r).space T).1
    ((quotSituation B n r).space T).2)

/-- The pullback of a module on `X_T` to `h_{ℙⁿ_T}`. -/
abbrev siteChartModule := ((siteSpaceEquivalence r T).functor.obj Q :
  Space.Modules.{u, u} B integerBase B.contains_integerBase (yoneda.obj (projectiveSite B n T.left))
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase (projectiveSite B n T.left)))

/-- The pullback to `h_{ℙⁿ_T}` of a quasi-coherent module on `X_T` is quasi-coherent. -/
theorem isQuasicoherentOnSite_siteChartModule (hQ : Q.IsQuasicoherentOnSite) :
    (siteChartModule T Q).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
    B.contains_integerBase (projectiveSiteSpaceIso r T).hom Q hQ

/-- **Finite presentation is read on `ℙⁿ_T`** (Stacks 05VG). -/
theorem isFinitePresentationOnSite_iff_siteReading (hQ : Q.IsQuasicoherentOnSite) :
    SheafOfModules.IsFinitePresentationOnSite Q ↔
      ((siteReading r T).obj Q).IsFinitePresentation := by
  have hN := isQuasicoherentOnSite_siteChartModule T Q hQ
  refine ⟨fun hfp => SheafOfModules.IsFinitePresentation.of_iso
    (Space.isFinitePresentation_restrictToChart B integerBase B.contains_integerBase
      (schemeSpace (projectiveSite B n T.left)) _ hN
      (Space.isFinitePresentationOnSite_modulePullback B integerBase
        B.contains_integerBase (projectiveSiteSpaceIso r T).hom Q hfp) _)
    (representedZariskiRestrictionIsoModule (projectiveSite B n T.left) _ hN), fun hfp => ?_⟩
  set L := (siteReading r T).obj Q
  have : SheafOfModules.IsQuasicoherent L := isQuasicoherent_siteReading_obj T Q hQ
  have h1 : SheafOfModules.IsFinitePresentationOnSite
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).obj L) :=
    (_root_.AlgebraicGeometry.SmallEtale.isFinitePresentationOnSite_iff_associatedModule
      (associatedBigEtaleSite B) _ _ L).1
      ((SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation L).2 hfp)
  have h2 := Stacks.SheafOfModules.isFinitePresentationOnSite_reindex
    (J' := Space.SmallEtale.topology B integerBase B.contains_integerBase
      (yoneda.obj (projectiveSite B n T.left)))
    (Space.representedSmallEtaleEquivalence B integerBase B.contains_integerBase
      (projectiveSite B n T.left))
    (Space.representedSchemeStructureSheaf B integerBase B.contains_integerBase
      (projectiveSite B n T.left)) _ (hM := h1)
  have h3 := Space.isFinitePresentationOnSite_modulePullback B integerBase
    B.contains_integerBase (projectiveSiteSpaceIso r T).inv _ h2
  have := isIso_siteReadingAdjunction_counit_app T Q hQ
  exact SheafOfModules.IsFinitePresentationOnSite.of_iso
    (asIso (((zariskiAdjunction B (projectiveSite B n T.left)).comp
      (siteSpaceEquivalence r T).symm.toAdjunction).counit.app Q)) h3

/-- **Flatness over `T` is read on `ℙⁿ_T`.**  Flatness of a quasi-coherent module on `X_T` over
`T` in the sense of Stacks 05VV is flatness of its pullback to `h_{ℙⁿ_T}` over `T`
(`AlgebraicGeometry.Space.isFlatOver_modulePullback_iso_iff`), which is checked at the points of
the representing scheme `ℙⁿ_T` on the identity chart
(`AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAt_representedZariskiRestriction`), where
it is the flatness of Stacks 08KT of the Zariski reading. -/
theorem isFlatOver_iff_siteReading (hQ : Q.IsQuasicoherentOnSite) :
    Space.IsFlatOver B integerBase B.contains_integerBase ((quotSituation B n r).space T).2
        ((quotSituation B n r).projection T).hom Q ↔
      AlgebraicGeometry.IsFlatOver ((𝒯).map (projectiveSiteStructure B n T.left)).toLRSHom.toShHom
        ((siteReading r T).obj Q) := by
  have hN := isQuasicoherentOnSite_siteChartModule T Q hQ
  rw [← Space.isFlatOver_modulePullback_iso_iff (projectiveSiteSpaceIso r T)
    ((quotSituation B n r).projection T) Q hQ, projectiveSiteSpaceIso_hom_projection]
  refine (Space.isFlatOver_iff_forall_isFlatOverAtPoint B integerBase B.contains_integerBase
    (X := schemeSpace (projectiveSite B n T.left)) (Y := schemeSpace T.left)
    (schemeSpaceMap (projectiveSiteStructure B n T.left)) (siteChartModule T Q) hN).trans ?_
  have key : ∀ u, Space.IsFlatOverAtPoint B integerBase B.contains_integerBase
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase (projectiveSite B n T.left))
      (yoneda.map (projectiveSiteStructure B n T.left)) (siteChartModule T Q)
      (Space.pointOfEtaleChart B integerBase B.contains_integerBase
        (Space.selfChart B integerBase B.contains_integerBase (projectiveSite B n T.left)) u) ↔
      AlgebraicGeometry.IsFlatOverAt ((𝒯).map (projectiveSiteStructure B n T.left)).toLRSHom.toShHom
        ((siteReading r T).obj Q) u := fun u =>
    (Space.isFlatOverAtPoint_iff_isFlatOverAt_representedZariskiRestriction B integerBase
      B.contains_integerBase (projectiveSiteStructure B n T.left) _ hN u).trans
      (flatOverAt_iff_of_iso _ (representedZariskiRestrictionIsoModule _ _ hN) u)
  refine ⟨fun h u => (key u).1 (h _), fun h x => ?_⟩
  obtain ⟨u, rfl⟩ : ∃ u, Space.pointOfEtaleChart B integerBase B.contains_integerBase
      (Space.selfChart B integerBase B.contains_integerBase (projectiveSite B n T.left)) u = x :=
    ⟨Space.pointsEquivScheme B integerBase B.contains_integerBase (projectiveSite B n T.left) x,
      (Space.pointOfEtaleChart_selfChart B integerBase B.contains_integerBase
        (projectiveSite B n T.left) _).trans (Equiv.symm_apply_apply _ x)⟩
  exact (key u).2 (h u)

end AlgebraicGeometry.ProjectiveQuot

end
