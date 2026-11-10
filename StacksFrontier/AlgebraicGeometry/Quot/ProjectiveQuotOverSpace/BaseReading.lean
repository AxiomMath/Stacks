/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Bridge

/-!
# A framed Quot situation over a scheme, read on `ℙⁿ_W`

Let `F/X/B` be a Quot situation over `Spec ℤ` with a projective frame `X = B × ℙⁿ_ℤ`, and suppose
the base `B` is identified with the algebraic space of an object `W` of the site
(`φ : h_W ≅ B`).  Then `X` itself is the algebraic space of `ℙⁿ_W` (pasting the frame with the
cartesian square of `ℙⁿ_W ⟶ ℙⁿ_ℤ`), so modules on `X` are read on the scheme `ℙⁿ_W`
(`AlgebraicGeometry.ProjectiveQuotOverSpace.baseReading`), and the reading is an equivalence on
quasi-coherent modules (Stacks 03DX).  For a test scheme `T` whose morphism to `B` is
represented by `a : T ⟶ W`, the reading of `F_T` on `ℙⁿ_T` is the inverse image along
`ℙⁿ_T ⟶ ℙⁿ_W` of the reading of `F` on `ℙⁿ_W`.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.baseSpaceIso`: `h_{ℙⁿ_W} ≅ X`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.baseReading`: the reading `Mod(X) ⥤ Mod(ℙⁿ_W)`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.baseReadingPullbackIso`: the reading of `F_T` is the
  inverse image of the reading of `F`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.baseLift`: a module on `ℙⁿ_W` read back on `X`.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.isIso_baseReading_unit_app`,
  `AlgebraicGeometry.ProjectiveQuotOverSpace.baseLiftReadingIso`: the reading is an equivalence on
  quasi-coherent modules, so a map `G ⟶ (baseReading E φ).obj F` from a quasi-coherent `G` is read
  back to `AlgebraicGeometry.ProjectiveQuotOverSpace.baseLiftMap : baseLift G ⟶ F` on `X`, whose
  source is quasi-coherent with reading `G` up to the unit isomorphism.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}
  {D : Space.QuotSituation B integerBase B.contains_integerBase}
  (E : ProjectiveFrame B n D) {W : BigFppfOver B integerBase B.contains_integerBase}
  (φ : schemeSpace W ≅ D.Y)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- `X ⟶ ℙⁿ_ℤ` and `X ⟶ B ≅ h_W` exhibit `X` as the base change of `ℙⁿ_ℤ ⟶ Spec ℤ` along
`W ⟶ Spec ℤ`. -/
theorem isPullback_base :
    IsPullback E.toProjective (D.f ≫ φ.inv) (quotSituation B n 0).f
      (schemeSpaceMap (toSiteBase B W)) :=
  IsPullback.of_iso E.isPullback (Iso.refl _) (Iso.refl _) φ.symm (Iso.refl _)
    (by simp) (by simp) (by simp)
    (ObjectProperty.hom_ext _ (isTerminal_yoneda_siteBase.hom_ext _ _))

/-- **`X = B × ℙⁿ_ℤ` is the algebraic space of `ℙⁿ_W`** when `B ≅ h_W`. -/
def baseSpaceIso : schemeSpace (projectiveSite B n W) ≅ D.X :=
  (isPullback_projectiveSiteSpace (r := 0) W).isoIsPullback _ _ (isPullback_base E φ)

/-- The composite `h_{ℙⁿ_W} ≅ X ⟶ ℙⁿ_ℤ` is the morphism represented by `ℙⁿ_W ⟶ ℙⁿ_ℤ`. -/
@[reassoc (attr := simp)]
theorem baseSpaceIso_hom_toProjective :
    (baseSpaceIso E φ).hom ≫ E.toProjective =
      schemeSpaceMap (projectiveSiteMap B n (toSiteBase B W)) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The composite `h_{ℙⁿ_W} ≅ X ⟶ B` is the structure morphism `h_{ℙⁿ_W} ⟶ h_W` followed by
`φ : h_W ≅ B`. -/
@[reassoc]
theorem baseSpaceIso_hom_f :
    (baseSpaceIso E φ).hom ≫ D.f = schemeSpaceMap (projectiveSiteStructure B n W) ≫ φ.hom := by
  have h : (baseSpaceIso E φ).hom ≫ D.f ≫ φ.inv = schemeSpaceMap (projectiveSiteStructure B n W) :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  rw [← h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The reading on `ℙⁿ_W` of a module on `X`.** -/
abbrev baseReading :
    Space.Modules.{u, u} B integerBase B.contains_integerBase D.X.1 D.X.2 ⥤
      ((𝒯).obj (projectiveSite B n W)).Modules :=
  isoReading (baseSpaceIso E φ)

/-! ### The reading of `F_T` over a test scheme with a morphism to `W` -/

section TestScheme

variable (T : Space.SchemesOver D.Y) (a : T.left ⟶ W) (ha : T.hom = schemeSpaceMap a ≫ φ.hom)

include ha in
/-- `X_T ⟶ X` read on `h_{ℙⁿ_T} ⟶ h_{ℙⁿ_W}` is the morphism represented by `ℙⁿ_T ⟶ ℙⁿ_W`. -/
theorem spaceIso_hom_sourceProjection_eq :
    (spaceIso E T).hom ≫ D.sourceProjection T =
      schemeSpaceMap (projectiveSiteMap B n a) ≫ (baseSpaceIso E φ).hom := by
  refine E.isPullback.hom_ext ?_ ?_
  · rw [Category.assoc, spaceIso_hom_sourceProjection_toProjective, Category.assoc,
      baseSpaceIso_hom_toProjective]
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map _ = yoneda.map _ ≫ yoneda.map _
    rw [← Functor.map_comp, ← projectiveSiteMap_comp]
    exact congrArg (fun k => yoneda.map (projectiveSiteMap B n k))
      ((isTerminal_siteBase B).hom_ext _ _)
  · have hw : D.sourceProjection T ≫ D.f = D.projection T ≫ T.hom :=
      (AlgebraicSpaces.isPullback_fiberProduct B integerBase B.contains_integerBase
        D.f T.hom).w
    have key : schemeSpaceMap (projectiveSiteStructure B n T.left) ≫ schemeSpaceMap a =
        schemeSpaceMap (projectiveSiteMap B n a) ≫ schemeSpaceMap (projectiveSiteStructure B n W) :=
      ObjectProperty.hom_ext _ (by
        change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ yoneda.map _
        rw [← Functor.map_comp, ← Functor.map_comp, (isPullback_projectiveSite B n a).w])
    rw [Category.assoc, hw, spaceIso_hom_projection_assoc, ha, Category.assoc,
      baseSpaceIso_hom_f]
    exact (reassoc_of% key) φ.hom

/-- `F` is quasi-coherent after pulling back to `h_{ℙⁿ_W}`. -/
theorem isQuasicoherentOnSite_modulePullback_baseSpaceIso :
    ((Space.modulePullback B integerBase B.contains_integerBase (baseSpaceIso E φ).hom).obj
      D.F).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
    B.contains_integerBase _ _ D.quasicoherent

/-- **The reading of `F_T` on `ℙⁿ_T` is the inverse image along `ℙⁿ_T ⟶ ℙⁿ_W` of the reading of
`F` on `ℙⁿ_W`.** -/
def baseReadingPullbackIso :
    (reading E T).obj (D.baseChangeModule T) ≅
      (Scheme.Modules.pullback (projectiveSpaceOverMap n ((𝒯).map a))).obj
        ((baseReading E φ).obj D.F) :=
  ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (projectiveSite B n T.left)).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).mapIso
    ((Space.modulePullbackSquare B integerBase B.contains_integerBase rfl
      (spaceIso_hom_sourceProjection_eq E φ T a ha).symm).app D.F) ≪≫
  (Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase
    (projectiveSiteMap B n a)
    (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
    ((Space.modulePullback B integerBase B.contains_integerBase (baseSpaceIso E φ).hom).obj D.F)
    (isQuasicoherentOnSite_modulePullback_baseSpaceIso E φ)).symm

end TestScheme

/-! ### The reading on `ℙⁿ_W` is an equivalence on quasi-coherent modules -/

/-- The reading of a quasi-coherent module on `X` is quasi-coherent. -/
theorem isQuasicoherent_baseReading_obj
    (A : Space.Modules.{u, u} B integerBase B.contains_integerBase D.X.1 D.X.2)
    (hA : A.IsQuasicoherentOnSite) : SheafOfModules.IsQuasicoherent ((baseReading E φ).obj A) :=
  isQuasicoherent_isoReading_obj (baseSpaceIso E φ) A hA

/-- The reading of `F` on `ℙⁿ_W` is quasi-coherent. -/
theorem isQuasicoherent_baseReading_F :
    SheafOfModules.IsQuasicoherent ((baseReading E φ).obj D.F) :=
  isQuasicoherent_baseReading_obj E φ D.F D.quasicoherent

/-- **A module on `ℙⁿ_W` read back on `X`**: the left adjoint of the reading. -/
abbrev baseLift : ((𝒯).obj (projectiveSite B n W)).Modules ⥤
    Space.Modules.{u, u} B integerBase B.contains_integerBase D.X.1 D.X.2 :=
  isoReadingLeft (baseSpaceIso E φ)

/-- The read-back of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherentOnSite_baseLift_obj (G : ((𝒯).obj (projectiveSite B n W)).Modules)
    (hG : SheafOfModules.IsQuasicoherent G) : ((baseLift E φ).obj G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_isoReadingLeft_obj (baseSpaceIso E φ) G hG

/-- **Reading back and reading again recovers a quasi-coherent module on `ℙⁿ_W`**: the unit of
the reading adjunction is invertible there (Stacks 03DX). -/
theorem isIso_baseReading_unit_app (G : ((𝒯).obj (projectiveSite B n W)).Modules)
    (hG : SheafOfModules.IsQuasicoherent G) :
    IsIso (((zariskiAdjunction B (projectiveSite B n W)).comp
      (isoReadingEquivalence (baseSpaceIso E φ)).symm.toAdjunction).unit.app G) :=
  isIso_isoReadingAdjunction_unit_app (baseSpaceIso E φ) G hG

/-- **Reading and reading back recovers a quasi-coherent module on `X`** (the counit of the
reading adjunction, Stacks 03DX). -/
def baseLiftReadingIso (A : Space.Modules.{u, u} B integerBase B.contains_integerBase D.X.1 D.X.2)
    (hA : A.IsQuasicoherentOnSite) :=
  @asIso _ _ _ _ (((zariskiAdjunction B (projectiveSite B n W)).comp
    (isoReadingEquivalence (baseSpaceIso E φ)).symm.toAdjunction).counit.app A)
    (isIso_isoReadingAdjunction_counit_app (baseSpaceIso E φ) A hA)

/-- The morphism `baseLift G ⟶ F` read back from a morphism `G ⟶ (baseReading E φ).obj F`. -/
def baseLiftMap {G : ((𝒯).obj (projectiveSite B n W)).Modules}
    (p : G ⟶ (baseReading E φ).obj D.F) : (baseLift E φ).obj G ⟶ D.F :=
  (baseLift E φ).map p ≫ (baseLiftReadingIso E φ D.F D.quasicoherent).hom

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
