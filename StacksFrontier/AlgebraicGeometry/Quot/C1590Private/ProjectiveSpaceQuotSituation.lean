module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FramedQuotUnitReading
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFamilyQuotSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleBase
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The Quot situation of `𝒪` on `ℙⁿ_U ⟶ U`

For an object `U` of the big fppf site over `Spec ℤ`, the structure morphism `ℙⁿ_U ⟶ U`, read as
a morphism of algebraic spaces, is of finite presentation, so it has the Quot situation of its
structure sheaf (`AlgebraicGeometry.Space.structureSheafQuotSituation`), the one whose Quot functor
is the Hilbert functor of `ℙⁿ_U ⟶ U` (Stacks 0D00). This file equips that situation with its
projective frame `ℙⁿ_U = U × ℙⁿ_ℤ` and shows that the reading of `𝒪_{ℙⁿ_U}` on `ℙⁿ_T` is
`𝒪_{ℙⁿ_T}` for every test scheme `T`.

## Main definitions

* `AlgebraicGeometry.C1590Private.projectiveSpaceQuotSituation`.
* `AlgebraicGeometry.C1590Private.projectiveSpaceFrame`.

## Main results

* `AlgebraicGeometry.C1590Private.hasUnitReading_projectiveSpaceFrame`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.C1590Private

open ProjectiveQuot ProjectiveQuotOverSpace

universe u

variable {B : BigFppfSite.{u}} (n : ℕ) (U : BigFppfOver B integerBase B.contains_integerBase)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The structure morphism `ℙⁿ_U ⟶ U`, as a morphism of algebraic spaces. -/
abbrev projectiveSpaceMap : schemeSpace (projectiveSite B n U) ⟶ schemeSpace U :=
  schemeSpaceMap (projectiveSiteStructure B n U)

/-- The structure morphism `ℙⁿ_U ⟶ U` is of finite presentation. -/
theorem isFinitePresentation_projectiveSpaceMap :
    Space.IsFinitePresentation B integerBase B.contains_integerBase
      (projectiveSpaceMap n U).hom :=
  Space.isFinitePresentation_yoneda_map B integerBase B.contains_integerBase _
    (finitePresentation_projectiveSpaceOver n _)

/-- **The Quot situation of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U`.** -/
abbrev projectiveSpaceQuotSituation : Space.QuotSituation B integerBase B.contains_integerBase :=
  Space.structureSheafQuotSituation (projectiveSpaceMap n U)
    (isFinitePresentation_projectiveSpaceMap n U)

/-- **The projective frame `ℙⁿ_U = U × ℙⁿ_ℤ`.** -/
def projectiveSpaceFrame : ProjectiveFrame B n (projectiveSpaceQuotSituation n U) where
  toProjective := schemeSpaceMap (projectiveSiteMap B n (toSiteBase B U))
  isPullback := by
    have h := isPullback_projectiveSiteSpace (B := B) (n := n) (r := 0) U
    rwa [show schemeSpaceMap (toSiteBase B U) = toBaseSpace (schemeSpace U) from
      Subsingleton.elim _ _] at h

/-- **The reading of `𝒪_{ℙⁿ_U}` on `ℙⁿ_T` is `𝒪_{ℙⁿ_T}`.** -/
theorem hasUnitReading_projectiveSpaceFrame : HasUnitReading (projectiveSpaceFrame n U) := by
  intro T
  let D := projectiveSpaceQuotSituation n U
  let W := projectiveSite B n T.left
  let φ := @Iso.hom _ _ (schemeSpace W : AlgebraicSpaces B integerBase B.contains_integerBase) _
    (spaceIso (projectiveSpaceFrame n U) T)
  have e₁ := (Space.modulePullback B integerBase B.contains_integerBase φ).mapIso
    (Space.modulePullbackUnitIso B integerBase B.contains_integerBase (D.sourceProjection T)) ≪≫
    Space.modulePullbackUnitIso B integerBase B.contains_integerBase φ ≪≫
    (Space.representedAssociatedModuleObjUnitIso B integerBase B.contains_integerBase W
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W)).symm
  exact ⟨(_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj W) W.left.property).mapIso
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
        W).inverse.mapIso e₁) ≪≫
    Space.representedZariskiModuleQuasicoherentSchemeIso B integerBase B.contains_integerBase W
      ⟨SheafOfModules.unit _,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _⟩ ≪≫
    (coproductUniqueIso fun _ : Fin 1 =>
      Scheme.unitModule (projectiveSpaceOver n ((𝒯).obj T.left))).symm⟩

end AlgebraicGeometry.C1590Private

end
