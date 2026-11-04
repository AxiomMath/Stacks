/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteReadingConditions

/-!
# Reading the modules of an algebraic space identified with a scheme

Let `e : h_W ≅ Z` identify an algebraic space `Z` over `Spec ℤ` with the algebraic space of an
object `W` of the big fppf site.  A module on the small étale site of `Z` is read as a module on
the scheme underlying `W` by pulling it back along `e` and taking the Zariski reading of
`AlgebraicGeometry.Space.representedZariskiModule`.  This reading is right adjoint to the
associated-module functor of Stacks 03DU followed by the transport back along `e`, and the
adjunction is an equivalence on quasi-coherent modules (Stacks 03DX), so it matches the
quasi-coherent quotients on both sides (`CategoryTheory.Adjunction.QuotientCorrespondence`).
Finite presentation (Stacks 05VG) and flatness over a scheme (Stacks 05VV against 08KT) are read
on `W`.

This is the reading of `AlgebraicGeometry.ProjectiveQuot.siteReading` for an arbitrary
identification `e`, as needed for the base changes of a Quot situation with a projective frame.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.isoReading`: the reading `Mod(Z) ⥤ Mod(W)`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.isoReadingLeft`: its left adjoint.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.quotientCorrespondence_isoReadingAdjunction`: the
  adjunction matches quasi-coherent quotients on both sides.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.isFinitePresentationOnSite_iff_isoReading`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.isFlatOver_iff_isoReading`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The ambient-universe abelian structure of site modules cannot describe the `𝒪_Z`-modules here,
-- whose sections live in the universe of the schemes; left in place it is selected ahead of
-- `SheafOfModules.instAbelian` in the quotient correspondence, which then disagrees with the
-- abelian structure its consumers see (as in
-- `StacksFrontier/AlgebraicGeometry/Quot/ProjectiveQuot/SiteBridge.lean`).
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

variable {W : BigFppfOver B integerBase B.contains_integerBase}
  {Z : AlgebraicSpaces B integerBase B.contains_integerBase} (e : schemeSpace W ≅ Z)

/-! ### The reading along `h_W ≅ Z` -/

/-- **The reading on the scheme `W` of a module on `Z ≅ h_W`**: pull back along `h_W ≅ Z`, read
on the small étale site of the scheme `W`, restrict to its Zariski site. -/
abbrev isoReading :
    Space.Modules.{u, u} B integerBase B.contains_integerBase Z.1 Z.2 ⥤ ((𝒯).obj W).Modules :=
  Space.modulePullback B integerBase B.contains_integerBase e.hom ⋙
    ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      W).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W) W.left.property)

/-- The equivalence of module categories induced by `h_W ≅ Z`. -/
abbrev isoReadingEquivalence :=
  (Space.modulePushforwardCoherence B integerBase B.contains_integerBase).modulePullbackEquivalence
    e

/-- The left adjoint of the reading: the associated module of Stacks 03DU on the small étale site
of `W`, read on `h_W`, then transported to `Z` along `e`. -/
abbrev isoReadingLeft : ((𝒯).obj W).Modules ⥤
    Space.Modules.{u, u} B integerBase B.contains_integerBase Z.1 Z.2 :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((𝒯).obj W) W.left.property ⋙
    (Space.representedSpaceModulesEquivalence B integerBase B.contains_integerBase W).functor) ⋙
  Space.modulePullback B integerBase B.contains_integerBase e.inv

/-- Pulling a quasi-coherent module back along `e.hom` gives a quasi-coherent module. -/
private theorem isQuasicoherentOnSite_modulePullback_hom
    {A : Space.Modules.{u, u} B integerBase B.contains_integerBase Z.1 Z.2}
    (hA : A.IsQuasicoherentOnSite) :
    ((isoReadingEquivalence e).symm.inverse.obj A).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite _ _ _ _ _ hA

/-- The counit of the reading adjunction is invertible at a quasi-coherent module. -/
theorem isIso_isoReadingAdjunction_counit_app
    (A : Space.Modules.{u, u} B integerBase B.contains_integerBase Z.1 Z.2)
    (hA : A.IsQuasicoherentOnSite) :
    IsIso (((zariskiAdjunction B W).comp
      (isoReadingEquivalence e).symm.toAdjunction).counit.app A) := by
  have h1 : IsIso ((zariskiAdjunction B W).counit.app
      ((isoReadingEquivalence e).symm.inverse.obj A)) :=
    isIso_zariskiAdjunction_counit_app W _
      (isQuasicoherentOnSite_modulePullback_hom e hA)
  have h2 : IsIso ((isoReadingEquivalence e).symm.toAdjunction.counit.app A) :=
    inferInstanceAs (IsIso ((isoReadingEquivalence e).symm.counitIso.app A).hom)
  exact (congrArg IsIso (Adjunction.comp_counit_app (zariskiAdjunction B W)
    (isoReadingEquivalence e).symm.toAdjunction A)).mpr
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) h2)

/-- The unit of the reading adjunction is invertible at a quasi-coherent module. -/
theorem isIso_isoReadingAdjunction_unit_app (M : ((𝒯).obj W).Modules)
    (hM : SheafOfModules.IsQuasicoherent M) :
    IsIso (((zariskiAdjunction B W).comp
      (isoReadingEquivalence e).symm.toAdjunction).unit.app M) := by
  have h1 := isIso_zariskiAdjunction_unit_app W M hM
  have h2 : IsIso ((isoReadingEquivalence e).symm.toAdjunction.unit.app
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((𝒯).obj W) W.left.property ⋙
      (Space.representedSpaceModulesEquivalence B integerBase B.contains_integerBase
        W).functor).obj M)) :=
    inferInstanceAs (IsIso ((isoReadingEquivalence e).symm.unitIso.app _).hom)
  exact @isIso_comp_unit_app _ _ _ _ _ _ _ _ _ _ (zariskiAdjunction B W)
    (isoReadingEquivalence e).symm.toAdjunction M h1 h2

/-- The reading of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_isoReading_obj
    (A : Space.Modules.{u, u} B integerBase B.contains_integerBase Z.1 Z.2)
    (hA : A.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent ((isoReading e).obj A) :=
  _root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule
    (associatedBigEtaleSite B) _ _ _
    (Space.isQuasicoherentOnSite_representedSmallEtaleInverse B integerBase
      B.contains_integerBase _ _
      (isQuasicoherentOnSite_modulePullback_hom e hA))

/-- The left adjoint of the reading carries quasi-coherent modules to quasi-coherent modules. -/
theorem isQuasicoherentOnSite_isoReadingLeft_obj (M : ((𝒯).obj W).Modules)
    (hM : SheafOfModules.IsQuasicoherent M) :
    ((isoReadingLeft e).obj M).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
    B.contains_integerBase e.inv _
    (Space.isQuasicoherentOnSite_associatedModule_schemeSpace W M hM)

/-- **The reading on `W` matches quasi-coherent quotients on both sides** (Stacks 03DX). -/
theorem quotientCorrespondence_isoReadingAdjunction :
    ((zariskiAdjunction B W).comp
      (isoReadingEquivalence e).symm.toAdjunction).QuotientCorrespondence
      (fun M => M.IsQuasicoherentOnSite) (fun L => SheafOfModules.IsQuasicoherent L) where
  isIso_counit A hA := isIso_isoReadingAdjunction_counit_app e A hA
  isIso_unit M hM := isIso_isoReadingAdjunction_unit_app e M hM
  map_right A hA := isQuasicoherent_isoReading_obj e A hA
  map_left M hM := isQuasicoherentOnSite_isoReadingLeft_obj e M hM
  cokernel_mem f hM hM' := by
    have := hM
    have := hM'
    exact Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel f
  of_iso_left e h := SheafOfModules.IsQuasicoherentOnSite.of_iso e h
  of_iso_right e h := (SheafOfModules.isQuasicoherent _).prop_of_iso e h

/-! ### Finite presentation and flatness, read on `W` -/

/-- **Finite presentation is read on `W`** (Stacks 05VG). -/
theorem isFinitePresentationOnSite_iff_isoReading
    (Q : Space.Modules.{u, u} B integerBase B.contains_integerBase Z.1 Z.2)
    (hQ : Q.IsQuasicoherentOnSite) :
    SheafOfModules.IsFinitePresentationOnSite Q ↔ ((isoReading e).obj Q).IsFinitePresentation := by
  refine ⟨fun hfp => ?_, fun hfp => ?_⟩
  · have hN := isQuasicoherentOnSite_modulePullback_hom e hQ
    exact SheafOfModules.IsFinitePresentation.of_iso
      (Space.isFinitePresentation_restrictToChart B integerBase B.contains_integerBase
        (schemeSpace W) _ hN (Space.isFinitePresentationOnSite_modulePullback B integerBase
          B.contains_integerBase e.hom Q hfp) _)
      (representedZariskiRestrictionIsoModule W _ hN)
  · set L := (isoReading e).obj Q
    have : SheafOfModules.IsQuasicoherent L := isQuasicoherent_isoReading_obj e Q hQ
    have h1 : SheafOfModules.IsFinitePresentationOnSite
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((𝒯).obj W) W.left.property).obj L) :=
      (_root_.AlgebraicGeometry.SmallEtale.isFinitePresentationOnSite_iff_associatedModule
        (associatedBigEtaleSite B) _ _ L).1
        ((SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation L).2 hfp)
    have h2 := Stacks.SheafOfModules.isFinitePresentationOnSite_reindex
      (J' := Space.SmallEtale.topology B integerBase B.contains_integerBase (yoneda.obj W))
      (Space.representedSmallEtaleEquivalence B integerBase B.contains_integerBase W)
      (Space.representedSchemeStructureSheaf B integerBase B.contains_integerBase W) _ (hM := h1)
    have h3 := Space.isFinitePresentationOnSite_modulePullback B integerBase
      B.contains_integerBase e.inv _ h2
    have := isIso_isoReadingAdjunction_counit_app e Q hQ
    exact SheafOfModules.IsFinitePresentationOnSite.of_iso
      (asIso (((zariskiAdjunction B W).comp
        (isoReadingEquivalence e).symm.toAdjunction).counit.app Q)) h3

/-- **Flatness over a scheme is read on `W`.**  For a morphism `π : Z ⟶ h_V` which is read on
`h_W` as the morphism represented by `s : W ⟶ V`, a quasi-coherent module on `Z` is flat over
`V` in the sense of Stacks 05VV exactly when its reading on `W` is flat over `V` in the sense of
Stacks 08KT. -/
theorem isFlatOver_iff_isoReading {V : BigFppfOver B integerBase B.contains_integerBase}
    (π : Z ⟶ schemeSpace V) (s : W ⟶ V) (hs : e.hom ≫ π = schemeSpaceMap s)
    (Q : Space.Modules.{u, u} B integerBase B.contains_integerBase Z.1 Z.2)
    (hQ : Q.IsQuasicoherentOnSite) :
    Space.IsFlatOver B integerBase B.contains_integerBase Z.2 π.hom Q ↔
      AlgebraicGeometry.IsFlatOver ((𝒯).map s).toLRSHom.toShHom ((isoReading e).obj Q) := by
  have hN := isQuasicoherentOnSite_modulePullback_hom e hQ
  rw [← Space.isFlatOver_modulePullback_iso_iff e π Q hQ, hs]
  refine (Space.isFlatOver_iff_forall_isFlatOverAtPoint B integerBase B.contains_integerBase
    (X := schemeSpace W) (Y := schemeSpace V) (schemeSpaceMap s)
    ((Space.modulePullback B integerBase B.contains_integerBase e.hom).obj Q) hN).trans ?_
  have key : ∀ u, Space.IsFlatOverAtPoint B integerBase B.contains_integerBase
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W)
      (yoneda.map s) ((Space.modulePullback B integerBase B.contains_integerBase e.hom).obj Q)
      (Space.pointOfEtaleChart B integerBase B.contains_integerBase
        (Space.selfChart B integerBase B.contains_integerBase W) u) ↔
      AlgebraicGeometry.IsFlatOverAt ((𝒯).map s).toLRSHom.toShHom ((isoReading e).obj Q) u :=
    fun u =>
    (Space.isFlatOverAtPoint_iff_isFlatOverAt_representedZariskiRestriction B integerBase
      B.contains_integerBase s _ hN u).trans
      (flatOverAt_iff_of_iso _ (representedZariskiRestrictionIsoModule _ _ hN) u)
  refine ⟨fun h u => (key u).1 (h _), fun h x => ?_⟩
  obtain ⟨u, rfl⟩ : ∃ u, Space.pointOfEtaleChart B integerBase B.contains_integerBase
      (Space.selfChart B integerBase B.contains_integerBase W) u = x :=
    ⟨Space.pointsEquivScheme B integerBase B.contains_integerBase W x,
      (Space.pointOfEtaleChart_selfChart B integerBase B.contains_integerBase W _).trans
        (Equiv.symm_apply_apply _ x)⟩
  exact (key u).2 (h u)

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
