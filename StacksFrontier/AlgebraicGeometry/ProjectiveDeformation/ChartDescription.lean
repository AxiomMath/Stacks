module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.CanonicalIdentification
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedMapHom

/-!
# The canonical morphism `r'` of a deformation, over an affine open of the base

For an admissible deformation `(X', S', i, i', f', ℒ')` and a cut `d₀ > 0`, the canonical
morphism `r' : X' ⟶ Proj_{S'}(𝒜')` of [Stacks, Tag 0D4F] (`canonicalProjHom`) is the morphism
`r_{ℒ', ψ}` of [Stacks, Tag 01VJ] into `Proj_{S'}(⨁_{d ≥ 0} 𝒜'_d)` followed by the isomorphism of
[Stacks, Tag 07ZJ]. This file computes it over an affine open `V` of `S'`: on `f'^{-1}(V)` it is
the morphism of [Stacks, Tag 01NK] for the graded map
`Γ(V, 𝒜') ⟶ Γ(V, ⨁_{d ≥ 0} 𝒜'_d) ⟶ Γ_*(f'^{-1}(V), ℒ')` followed by the chart of
`Proj_{S'}(𝒜')` over `V` ([Stacks, Tag 01NQ]).

## Main results

* `Stacks.RelativeAmple.ι_relativeAmpleProjHom`: the same for `r_{L, ψ}` itself, for any `L`
  ample relative to a quasi-compact quasi-separated `f`.
* `…ProjectiveDeformation.chart_comp_projTruncationComparison`: the comparison of
  [Stacks, Tag 07ZJ] read through the chart over an affine open is the morphism of
  [Stacks, Tag 01MY] for the comparison of the graded rings of sections.
* `…AdmissibleDeformation.ι_canonicalProjHom`: **`r'` over an affine open of the base.**

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.ProjShared (mapDomain)
open Stacks.AlgebraicGeometry.ProjTwistChain (mapHom)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap)

universe u

/-- The inverse of `⊤ ≅ Y` followed by the identification with an open equal to `⊤` is a section
of the inclusion of that open. -/
private theorem topIso_inv_isoOfEq_hom_ι {Y : Scheme.{u}} {U : Y.Opens} (h : U = ⊤) :
    Y.topIso.inv ≫ (Y.isoOfEq h.symm).hom ≫ U.ι = 𝟙 _ := by
  simp only [Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]

namespace Stacks.RelativeAmple

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  [QuasiCompact f] [QuasiSeparated f]

/-- **`r_{L, ψ}` over an affine open `V` of the base**: on `f^{-1}(V)` it is the morphism of
[Stacks, Tag 01NK] for the induced datum over `V` followed by the chart over `V`. This is clause
(3) of [Stacks, Tag 01O9], `GradedPowerMap.comp_globalMorphism_eq`, read on `f^{-1}(V)` through any
section `e` of the inclusion of the covering open of the datum, which is all of `f^{-1}(V)`. -/
theorem ι_relativeAmpleProjHom (hL : IsRelativelyAmple f L) {V : S.Opens} (hV : IsAffineOpen V)
    (e : (f ⁻¹ᵁ V).toScheme ⟶ ((directImagePowerMap f L).affineDatum V).coveringOpen.toScheme)
    (he : e ≫ ((directImagePowerMap f L).affineDatum V).coveringOpen.ι = 𝟙 _) :
    (f ⁻¹ᵁ V).ι ≫ relativeAmpleProjHom f L hL =
      e ≫ ((directImagePowerMap f L).affineDatum V).glued ≫
        (relativeProj (directImageAlgebra f L)).chart V hV := by
  let j : ((directImagePowerMap f L).affineDatum V).coveringOpen.toScheme ⟶
      (directImagePowerMap f L).coveringOpen.toScheme :=
    ((directImagePowerMap f L).affineDatum V).coveringOpen.ι ≫ (f ⁻¹ᵁ V).ι ≫ X.topIso.inv ≫
      (X.isoOfEq (coveringOpen_directImagePowerMap hL).symm).hom
  have key := (directImagePowerMap f L).comp_globalMorphism_eq
    (relativeProj (directImageAlgebra f L)) ⟨V, hV⟩ j
    (by simp only [j, Category.assoc,
      topIso_inv_isoOfEq_hom_ι (coveringOpen_directImagePowerMap hL), Category.comp_id])
  rw [← key, relativeAmpleProjHom]
  simp only [j, ← Category.assoc, he, Category.id_comp]

end Stacks.RelativeAmple

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

variable {P : PolarizedFamily.{u}} {D : P.AdmissibleDeformation} {A : SheafGradedAlgebra D.S'}
  (ψ : Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom A
    D.fullSectionAlgebra)
  (hψ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ.app (d : ℤ)))

include hψ in
/-- The morphism of [Stacks, Tag 01MY] attached to a comparison invertible in all large degrees is
defined on all of the projective spectrum of the sections over an affine open. -/
theorem mapDomain_sectionHom_eq_top (V : D.S'.Opens) :
    mapDomain (A.grading V) (D.fullSectionAlgebra.grading V) (ψ.sectionHom V) = ⊤ :=
  Stacks.AlgebraicGeometry.RelativeProjMapDomain.chartDomain_eq_top_of_eventually_isIso ψ hψ V

/-- **The comparison of [Stacks, Tag 07ZJ] read through the chart over an affine open `V`**: it is
the morphism of [Stacks, Tag 01MY] for `Γ(V, A) ⟶ Γ(V, ⨁_{d ≥ 0} 𝒜'_d)` followed by the chart of
`Proj_{S'}(A)`, through any section `m` of the inclusion of the domain of that morphism. -/
theorem chart_comp_projTruncationComparison (V : D.S'.Opens) (hV : IsAffineOpen V)
    (m : (AlgebraicGeometry.Proj (D.fullSectionAlgebra.grading V)) ⟶
      (mapDomain (A.grading V) (D.fullSectionAlgebra.grading V) (ψ.sectionHom V)).toScheme)
    (hm : m ≫ (mapDomain (A.grading V) (D.fullSectionAlgebra.grading V)
      (ψ.sectionHom V)).ι = 𝟙 _) :
    (relativeProj D.fullSectionAlgebra).chart V hV ≫ projTruncationComparison ψ hψ =
      m ≫ mapHom (A.grading V) (D.fullSectionAlgebra.grading V) (ψ.sectionHom V) ≫
        (relativeProj A).chart V hV := by
  have key := Stacks.AlgebraicGeometry.Tag07ZGMorphism.chart_comp_relativeMapHom ψ ⟨V, hV⟩
  have hfac : (relativeProj D.fullSectionAlgebra).chart V hV ≫ projDomainRetract ψ hψ =
      m ≫ (((relativeProj D.fullSectionAlgebra).chart V hV).isoImage
          (mapDomain (A.grading V) (D.fullSectionAlgebra.grading V) (ψ.sectionHom V))).hom ≫
        (relativeProj D.fullSectionAlgebra).scheme.homOfLE
          (Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartImage_le ψ ⟨V, hV⟩) := by
    rw [← cancel_mono ψ.relativeMapDomain.ι, Category.assoc, projDomainRetract_comp_ι,
      Category.comp_id, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
      Scheme.Hom.isoImage_hom_ι, ← Category.assoc, hm, Category.id_comp]
  rw [projTruncationComparison, ← Category.assoc, hfac, Category.assoc, Category.assoc, key]

namespace PolarizedFamily.AdmissibleDeformation

variable (D) (d₀ : ℕ) (hd₀ : 0 < d₀)

/-- **The datum `ψ : (f')^*(⨁_{d ≥ 0} 𝒜'_d) ⟶ ⨁_{d ≥ 0} (ℒ')^{⊗ d}` of [Stacks, Tag 01O8]** of a
deformation, whose morphism `r_{ℒ', ψ}` of [Stacks, Tag 01O9] is `fullSectionProjHom`. -/
def sectionPowerMap : GradedPowerMap D.fullSectionAlgebra D.f' :=
  letI := D.finitePresentation.quasiCompact
  letI := D.finitePresentation.quasiSeparated
  Stacks.RelativeAmple.directImagePowerMap D.f' D.L'

/-- **The [Stacks, Tag 01NK] datum of `r'` over an open `V` of the base**: the graded map
`Γ(V, 𝒜') ⟶ Γ(V, ⨁_{d ≥ 0} 𝒜'_d) ⟶ Γ_*(f'^{-1}(V), ℒ')`. -/
abbrev chartDatum (V : D.S'.Opens) :
    Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections
      ((D.truncatedSectionAlgebra d₀ hd₀).grading V)
      ((Scheme.Modules.pullback (D.f' ⁻¹ᵁ V).ι).obj D.sectionPowerMap.L) :=
  comap ((D.sectionAlgebraComparison d₀ hd₀).sectionHom V) ((D.sectionPowerMap).affineDatum V)

/-- The datum of `r'` over an affine open `V` generates everywhere on `f'^{-1}(V)`. -/
theorem coveringOpen_chartDatum {V : D.S'.Opens} (hV : IsAffineOpen V) :
    (D.chartDatum d₀ hd₀ V).coveringOpen = ⊤ := by
  let := D.finitePresentation.quasiCompact
  let := D.finitePresentation.quasiSeparated
  rw [chartDatum, ProjChartGradedRingFunctoriality.coveringOpen_comap_eq_of_mapDomain_eq_top
    _ _ (mapDomain_sectionHom_eq_top _ (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀) V)]
  exact Stacks.RelativeAmple.coveringOpen_affineDatum_eq_top D.isRelativelyAmple_L' hV

/-- **`r'` over an affine open `V` of the base** ([Stacks, Tag 0D4F] (4), read through the chart of
[Stacks, Tag 01NQ]): on `f'^{-1}(V)` the canonical morphism `r' : X' ⟶ Proj_{S'}(𝒜')` is the
morphism of [Stacks, Tag 01NK] for `chartDatum` followed by the chart of `Proj_{S'}(𝒜')` over `V`,
read through any section `e` of the inclusion of `U(chartDatum) = f'^{-1}(V)`. -/
theorem ι_canonicalProjHom {V : D.S'.Opens} (hV : IsAffineOpen V)
    (e : (D.f' ⁻¹ᵁ V).toScheme ⟶ (D.chartDatum d₀ hd₀ V).coveringOpen.toScheme)
    (he : e ≫ (D.chartDatum d₀ hd₀ V).coveringOpen.ι = 𝟙 _) :
    (D.f' ⁻¹ᵁ V).ι ≫ D.canonicalProjHom d₀ hd₀ =
      e ≫ (D.chartDatum d₀ hd₀ V).glued ≫
        (relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).chart V hV := by
  let := D.finitePresentation.quasiCompact
  let := D.finitePresentation.quasiSeparated
  have hc := D.eventually_isIso_sectionAlgebraComparison d₀ hd₀
  have hdom := mapDomain_sectionHom_eq_top (D.sectionAlgebraComparison d₀ hd₀) hc V
  let m : (AlgebraicGeometry.Proj (D.fullSectionAlgebra.grading V)) ⟶
      (mapDomain ((D.truncatedSectionAlgebra d₀ hd₀).grading V) (D.fullSectionAlgebra.grading V)
        ((D.sectionAlgebraComparison d₀ hd₀).sectionHom V)).toScheme :=
    (AlgebraicGeometry.Proj (D.fullSectionAlgebra.grading V)).topIso.inv ≫
      ((AlgebraicGeometry.Proj (D.fullSectionAlgebra.grading V)).isoOfEq hdom.symm).hom
  have hm : m ≫ (mapDomain ((D.truncatedSectionAlgebra d₀ hd₀).grading V)
      (D.fullSectionAlgebra.grading V)
        ((D.sectionAlgebraComparison d₀ hd₀).sectionHom V)).ι = 𝟙 _ := by
    simpa only [m, Category.assoc] using topIso_inv_isoOfEq_hom_ι hdom
  have hle := Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.coveringOpen_le
    ((D.sectionAlgebraComparison d₀ hd₀).sectionHom V) (D.sectionPowerMap.affineDatum V)
  have he₀ : (e ≫ (D.f' ⁻¹ᵁ V).toScheme.homOfLE hle) ≫
      (D.sectionPowerMap.affineDatum V).coveringOpen.ι = 𝟙 _ := by
    rw [Category.assoc, Scheme.homOfLE_ι]; exact he
  have h1 := Stacks.RelativeAmple.ι_relativeAmpleProjHom D.f' D.L' D.isRelativelyAmple_L' hV _ he₀
  have h2 := chart_comp_projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀) hc V hV m hm
  have h3 := Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.glued_comp_mapHom
    ((D.sectionAlgebraComparison d₀ hd₀).sectionHom V) (D.sectionPowerMap.affineDatum V)
    ((D.f' ⁻¹ᵁ V).toScheme.homOfLE hle ≫ (D.sectionPowerMap.affineDatum V).glued ≫ m)
    (by rw [Category.assoc, Category.assoc, hm, Category.comp_id])
  have h1' : (D.f' ⁻¹ᵁ V).ι ≫ D.fullSectionProjHom D.isRelativelyAmple_L' =
      (e ≫ (D.f' ⁻¹ᵁ V).toScheme.homOfLE hle) ≫ (D.sectionPowerMap.affineDatum V).glued ≫
        (relativeProj D.fullSectionAlgebra).chart V hV := h1
  calc (D.f' ⁻¹ᵁ V).ι ≫ D.canonicalProjHom d₀ hd₀
      = ((D.f' ⁻¹ᵁ V).ι ≫ D.fullSectionProjHom D.isRelativelyAmple_L') ≫
          projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀) hc :=
        (Category.assoc _ _ _).symm
    _ = ((e ≫ (D.f' ⁻¹ᵁ V).toScheme.homOfLE hle) ≫ (D.sectionPowerMap.affineDatum V).glued ≫
          (relativeProj D.fullSectionAlgebra).chart V hV) ≫
            projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀) hc := by
        rw [h1']
    _ = (e ≫ (D.f' ⁻¹ᵁ V).toScheme.homOfLE hle) ≫ (D.sectionPowerMap.affineDatum V).glued ≫
          ((relativeProj D.fullSectionAlgebra).chart V hV ≫
            projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀) hc) := by
        simp only [Category.assoc]
    _ = (e ≫ (D.f' ⁻¹ᵁ V).toScheme.homOfLE hle) ≫ (D.sectionPowerMap.affineDatum V).glued ≫ m ≫
          mapHom ((D.truncatedSectionAlgebra d₀ hd₀).grading V) (D.fullSectionAlgebra.grading V)
            ((D.sectionAlgebraComparison d₀ hd₀).sectionHom V) ≫
              (relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).chart V hV := by
        rw [h2]
    _ = e ≫ (((D.f' ⁻¹ᵁ V).toScheme.homOfLE hle ≫ (D.sectionPowerMap.affineDatum V).glued ≫ m) ≫
          mapHom ((D.truncatedSectionAlgebra d₀ hd₀).grading V) (D.fullSectionAlgebra.grading V)
            ((D.sectionAlgebraComparison d₀ hd₀).sectionHom V)) ≫
              (relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).chart V hV := by
        simp only [Category.assoc]
    _ = _ :=
      congrArg (fun z => e ≫ z ≫ (relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).chart V hV) h3

end PolarizedFamily.AdmissibleDeformation

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
