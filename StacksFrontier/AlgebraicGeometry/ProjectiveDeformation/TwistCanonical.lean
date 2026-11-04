module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.CanonicalIdentification
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.TwistBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.TwistPowers

/-!
# The canonical twist map `θ'` of a deformation in every degree

For an admissible deformation and a positive cut `d₀`, `θ' : (r')^* 𝒪(1) ⟶ ℒ'`
(`canonicalTwistMap`) is the degree-one member, read through `ℒ'^{⊗ 1} ≅ ℒ'`, of the family
`θ'_n : (r')^* 𝒪_{Proj_{S'}(𝒜')}(n) ⟶ (ℒ')^{⊗ n}` (`canonicalTwistPow`): the map of Serre twists of
[Stacks, Tag 07ZJ] pulled back along `r_{ℒ', ψ}`, followed by `θ` of [Stacks, Tag 01O9]. The family
is multiplicative on inverse images of sections and carries the inverse image of the section
`ψ(a)` of `𝒪(d)` attached to a homogeneous `a` of `𝒜'_d` to the section `a` of `(ℒ')^{⊗ d}`.

## Main definitions

* `…AdmissibleDeformation.canonicalTwistPow`.

## Main results

* `…AdmissibleDeformation.canonicalTwistMap_eq`, `…canonicalTwistPow_unitMul`,
  `…canonicalTwistPow_app_unitApp_psiU`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp unitApp_naturality unitApp_map
  hom_app_map map_map_homOfLE)
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

namespace PolarizedFamily.AdmissibleDeformation

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`; see
-- `Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections`.
attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {P : PolarizedFamily.{u}} (D : P.AdmissibleDeformation) (d₀ : ℕ) (hd₀ : 0 < d₀)

/-- The map of Serre twists of [Stacks, Tag 07ZJ] for the comparison `𝒜' ⟶ ⨁_{d ≥ 0} 𝒜'_d` is the
degree-one component of `projTwistHom`. -/
theorem projTruncationTwistIso_hom_eq :
    (projTruncationTwistIso (D.sectionAlgebraComparison d₀ hd₀)
        (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀)).hom =
      (projTwistHomOf (D.sectionAlgebraComparison d₀ hd₀)
        (projDomainRetract (D.sectionAlgebraComparison d₀ hd₀)
          (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))
        (projDomainRetract_comp_ι (D.sectionAlgebraComparison d₀ hd₀)
          (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))).app 1 :=
  rfl

/-- **`θ'` in degree `n`**: `(r')^* 𝒪_{Proj_{S'}(𝒜')}(n) ⟶ (ℒ')^{⊗ n}`, the map of Serre twists of
[Stacks, Tag 07ZJ] pulled back along `r_{ℒ', ψ}` followed by `θ` of [Stacks, Tag 01O9] in
degree `n`. -/
def canonicalTwistPow (n : ℤ) :
    (Scheme.Modules.pullback (D.fullSectionProjHom D.isRelativelyAmple_L' ≫
        projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
          (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))).obj
        (relativeTwist (D.truncatedSectionAlgebra d₀ hd₀) n) ⟶ tensorPowerModule D.X' D.L' n :=
  letI := D.finitePresentation.quasiCompact
  letI := D.finitePresentation.quasiSeparated
  TwistSections.comp₂ D.L' (D.fullSectionProjHom D.isRelativelyAmple_L')
    (projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
      (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))
    (projTwistHomOf (D.sectionAlgebraComparison d₀ hd₀)
      (projDomainRetract (D.sectionAlgebraComparison d₀ hd₀)
        (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))
      (projDomainRetract_comp_ι (D.sectionAlgebraComparison d₀ hd₀)
        (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀)))
    (Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistPow D.f' D.L'
      D.isRelativelyAmple_L') n

/-- **`θ'` is `θ'_1` read through `ℒ'^{⊗ 1} ≅ ℒ'`.** -/
theorem canonicalTwistMap_eq :
    D.canonicalTwistMap d₀ hd₀ = D.canonicalTwistPow d₀ hd₀ 1 ≫
      (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare D.L' 1).inv ≫ (λ_ D.L').hom := by
  let := D.finitePresentation.quasiCompact
  let := D.finitePresentation.quasiSeparated
  rw [canonicalTwistMap, Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistIso_hom_eq,
    projTruncationTwistIso_hom_eq]
  exact ((Category.assoc _ _ _).trans (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _))).symm

/-- `θ'_n` is multiplicative on the inverse images of sections. -/
theorem canonicalTwistPow_unitMul :
    TwistSections.UnitMul D.L' (D.fullSectionProjHom D.isRelativelyAmple_L' ≫
        projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
          (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))
      (twistAlgebra (D.truncatedSectionAlgebra d₀ hd₀)) (D.canonicalTwistPow d₀ hd₀) := by
  let := D.finitePresentation.quasiCompact
  let := D.finitePresentation.quasiSeparated
  exact TwistSections.comp₂_unitMul D.L' _ _ _ _
    (Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistPow_unitMul D.f' D.L'
      D.isRelativelyAmple_L')

/-- The inverse image of `V` along the composite of the canonical morphism to the relative `Proj`
of the truncated section algebra with its structure morphism lies in `f'⁻¹ V`. -/
theorem canonicalProjHom_preimage_le (V : D.S'.Opens) :
    (D.fullSectionProjHom D.isRelativelyAmple_L' ≫
        projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
          (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀)) ⁻¹ᵁ
        ((relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V) ≤ D.f' ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, ← D.canonicalProjHom_comp_toBase d₀ hd₀]
  rfl

/-- **`θ'_d` on the section attached to a homogeneous element**: it carries the inverse image of
`ψ(a)` to `a`, read as a section of `(ℒ')^{⊗ d}` through the comparison `𝒜' ⟶ ⨁_{d ≥ 0} 𝒜'_d`. -/
theorem canonicalTwistPow_app_unitApp_psiU (d : ℕ) (V : D.S'.Opens)
    (a : Γ((D.truncatedSectionAlgebra d₀ hd₀).piece (d : ℤ), V)) :
    (D.canonicalTwistPow d₀ hd₀ d).app
        ((D.fullSectionProjHom D.isRelativelyAmple_L' ≫
          projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
            (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀)) ⁻¹ᵁ
          ((relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V))
        (unitApp (D.fullSectionProjHom D.isRelativelyAmple_L' ≫
          projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
            (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))
          (relativeTwist (D.truncatedSectionAlgebra d₀ hd₀) d)
          ((relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
          (psiU (D.truncatedSectionAlgebra d₀ hd₀) d V a)) =
      (tensorPowerModule D.X' D.L' d).presheaf.map
          (homOfLE (D.canonicalProjHom_preimage_le d₀ hd₀ V)).op
        (show Γ(tensorPowerModule D.X' D.L' d, D.f' ⁻¹ᵁ V) from
          ((D.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app V a) := by
  let := D.finitePresentation.quasiCompact
  let := D.finitePresentation.quasiSeparated
  have hle : projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
      (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀) ⁻¹ᵁ
        ((relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V) ≤
      (relativeProj D.fullSectionAlgebra).toBase ⁻¹ᵁ V :=
    retract_preimage_toBase_le _ _ (projDomainRetract_comp_ι _ _) V
  have e2 : Scheme.Modules.Hom.app ((projTwistHomOf (D.sectionAlgebraComparison d₀ hd₀)
        (projDomainRetract (D.sectionAlgebraComparison d₀ hd₀)
          (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))
        (projDomainRetract_comp_ι (D.sectionAlgebraComparison d₀ hd₀)
          (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))).app (d : ℤ))
      (projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
        (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀) ⁻¹ᵁ
          ((relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V))
      (unitApp (projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
        (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))
        (relativeTwist (D.truncatedSectionAlgebra d₀ hd₀) d)
        ((relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
        (psiU (D.truncatedSectionAlgebra d₀ hd₀) d V a)) =
      (relativeTwist D.fullSectionAlgebra d).presheaf.map (homOfLE hle).op
        (psiU D.fullSectionAlgebra d V
          (((D.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app V a)) :=
    projTwistHomOf_app_unitApp_psiU _ _ _ d V a
  have e1 := TwistSections.comp₂_app_eq D.L' (D.fullSectionProjHom D.isRelativelyAmple_L')
    (projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
      (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))
    (projTwistHomOf (D.sectionAlgebraComparison d₀ hd₀)
      (projDomainRetract (D.sectionAlgebraComparison d₀ hd₀)
        (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))
      (projDomainRetract_comp_ι (D.sectionAlgebraComparison d₀ hd₀)
        (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀)))
    (Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistPow D.f' D.L'
      D.isRelativelyAmple_L') d ((relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).toBase ⁻¹ᵁ V)
    (psiU (D.truncatedSectionAlgebra d₀ hd₀) d V a)
    (psiU D.fullSectionAlgebra d V (((D.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app V a))
    hle e2
  have h' : D.fullSectionProjHom D.isRelativelyAmple_L' ⁻¹ᵁ
      ((relativeProj D.fullSectionAlgebra).toBase ⁻¹ᵁ V) ≤ D.f' ⁻¹ᵁ V :=
    Stacks.RelativeAmple.TwistIdentification.relativeAmpleProjHom_preimage_toBase_le D.f' D.L'
      D.isRelativelyAmple_L' V
  have e3 : (Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistPow D.f' D.L'
      D.isRelativelyAmple_L' d).app (D.fullSectionProjHom D.isRelativelyAmple_L' ⁻¹ᵁ
        ((relativeProj D.fullSectionAlgebra).toBase ⁻¹ᵁ V))
      (unitApp (D.fullSectionProjHom D.isRelativelyAmple_L')
        (relativeTwist D.fullSectionAlgebra d)
        ((relativeProj D.fullSectionAlgebra).toBase ⁻¹ᵁ V)
        (psiU D.fullSectionAlgebra d V
          (((D.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app V a))) =
      (tensorPowerModule D.X' D.L' d).presheaf.map (homOfLE h').op
        (show Γ(tensorPowerModule D.X' D.L' d, D.f' ⁻¹ᵁ V) from
          ((D.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app V a) :=
    Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistPow_app_unitApp_psiU
      D.f' D.L' D.isRelativelyAmple_L' d V
      (((D.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)).app V a)
  have t1 : D.canonicalTwistPow d₀ hd₀ d = TwistSections.comp₂ D.L'
      (D.fullSectionProjHom D.isRelativelyAmple_L')
      (projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
        (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))
      (projTwistHomOf (D.sectionAlgebraComparison d₀ hd₀)
        (projDomainRetract (D.sectionAlgebraComparison d₀ hd₀)
          (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))
        (projDomainRetract_comp_ι (D.sectionAlgebraComparison d₀ hd₀)
          (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀)))
      (Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistPow D.f' D.L'
        D.isRelativelyAmple_L') d := rfl
  rw [t1]
  refine e1.trans ?_
  refine (congrArg (fun z => (tensorPowerModule D.X' D.L' d).presheaf.map
    (homOfLE ((D.fullSectionProjHom D.isRelativelyAmple_L').preimage_mono hle)).op z) e3).trans ?_
  exact map_map_homOfLE _ _ h' _ _

end PolarizedFamily.AdmissibleDeformation

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
