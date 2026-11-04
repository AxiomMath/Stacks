module

public import StacksFrontier.AlgebraicGeometry.Morphism.ChartPullback
public import StacksFrontier.AlgebraicGeometry.Morphism.ChartSquare
public import StacksFrontier.AlgebraicGeometry.Morphism.KerChart
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ChartKernel
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.DegreePresenterChart
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.IsoClause

/-!
# The closed subscheme `Proj_S(𝒜/ℱ𝒜)` depends only on `ℱ`

Work in Situation 01NN: a scheme `S` and a quasi-coherent graded `𝒪_S`-algebra `𝒜`.  Let
`ℱ ⊆ 𝒜_d` be a quasi-coherent submodule of one homogeneous piece.  A degreewise surjection
`ψ : 𝒜 ⟶ ℬ` whose kernel is the graded ideal `ℱ𝒜`
(`…RelativeProjGradedIdeal.IsQuotientByDegreeSubmodule`) presents the closed subscheme
`Proj_S(ℬ) ⊆ Proj_S(𝒜)` (Stacks 07ZI).  This file proves that this closed subscheme depends only
on `ℱ`: two such surjections have closed immersions `Proj_S(ℬ₁) ⟶ Proj_S(𝒜)` and
`Proj_S(ℬ₂) ⟶ Proj_S(𝒜)` with the same ideal sheaf.  Consequently every presentation
`Z = Proj_S(𝒜/ℱ𝒜)` of Tag 0802 (`…RelativeProjGradedIdeal.DegreeQuotientPresentation`) has the
ideal sheaf of `Proj_S(ℬ)` for any such `ψ`.

This is the scheme half of the identification, in Stacks 085N, of the fibre of
`Proj_X(𝒜/ℱ𝒜) ⟶ Proj_X(𝒜)` over an étale chart `W ⟶ X` with the closed subscheme which the
chart case of Stacks 0803 produces: both are cut out by the base-changed `ℱ`.

## Main results

* `…RelativeProjGradedIdeal.ker_chartMap_eq_of_isQuotientByDegreeSubmodule`: over an affine open
  of the base, the chart maps of two such surjections have the same kernel.  On each standard open
  `D₊(f)` of the chart both kernels are the ideal `…RelativeProjGradedIdeal.chartIdeal` that `ℱ`
  generates there (`…RelativeProjGradedIdeal.ker_awayMap_sectionHom_eq_chartIdeal`).
* `…RelativeProjGradedIdeal.ker_map_eq_of_isQuotientByDegreeSubmodule`: **the closed immersions
  `Proj_S(ℬ₁) ⟶ Proj_S(𝒜)` and `Proj_S(ℬ₂) ⟶ Proj_S(𝒜)` have the same ideal sheaf.**
* `…RelativeProjGradedIdeal.DegreeQuotientPresentation.ker_eq_ker_map`: a presentation
  `Z = Proj_S(𝒜/ℱ𝒜)` has the ideal sheaf of `Proj_S(ℬ)` for every degreewise surjection `𝒜 ⟶ ℬ`
  with kernel `ℱ𝒜`.
* `…RelativeProjGradedIdeal.ker_relativeMapHom_eq_ker_map`: for a degreewise surjection the
  morphism `r_ψ : U(ψ) ⟶ Proj_S(𝒜)` of Tag 07ZG and the closed immersion
  `…ProjBundleSurjection.map` have the same ideal sheaf; on the charts both are `Proj.map` of the
  surjection of section rings (`…Tag07ZGMorphism.mapHom_eq_ι_comp_proj_map`).
* `…RelativeProjGradedIdeal.DegreeQuotientPresentation.ker_eq_ker_relativeMapHom`: the same
  comparison of a presentation `Z = Proj_S(𝒜/ℱ𝒜)` with `r_ψ`, the form in which the fibres of
  `Proj_X(𝒜/ℱ𝒜) ⟶ Proj_X(𝒜)` over the scheme points of an algebraic space are given.

## References

* [Stacks Project, Tag 0802](https://stacks.math.columbia.edu/tag/0802)
* [Stacks Project, Tag 07ZI](https://stacks.math.columbia.edu/tag/07ZI)
* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S) {d : ℕ} (ℱ : (𝒜.piece (d : ℤ)).Submodule)

/-- The standard opens of the homogeneous sections of positive degree cover `Proj Γ(U, 𝒜)`. -/
theorem iSup_basicOpen_positive_eq_top (U : S.Opens) :
    (⨆ x : {p : 𝒜.sectionRing U × ℕ // p.1 ∈ 𝒜.grading U p.2 ∧ 0 < p.2},
      AlgebraicGeometry.Proj.basicOpen (𝒜.grading U) x.1.1) = ⊤ :=
  AlgebraicGeometry.Proj.iSup_basicOpen_eq_top _ _
    ((HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun i hi x hx =>
      Ideal.subset_span ⟨⟨(x, i), hx, hi⟩, rfl⟩)

variable {ℱ}

/-- The `Proj.map` of the section rings of a degreewise surjection is a closed immersion. -/
private theorem isClosedImmersion_proj_map_sectionHom {B : SheafGradedAlgebra S}
    {ψ : SheafGradedAlgebraHom 𝒜 B} (hψ : ProjBundleSurjection.SurjectiveOnAffineSections ψ)
    {U : S.Opens} (hU : IsAffineOpen U) :
    IsClosedImmersion (AlgebraicGeometry.Proj.map (ψ.sectionHom U)
      (ProjBundleSurjection.irrelevant_le_map_sectionHom hψ hU)) := by
  rw [← ProjBundleSurjection.chartMap_eq_map]
  exact ProjBundleSurjection.isClosedImmersion_chartMap hψ U hU

/-- **Over an affine open of the base, the chart maps of two degreewise surjections with kernel
`ℱ𝒜` have the same kernel.**  Both chart maps are the morphisms of absolute projective spectra of
the induced maps of section rings (`…ProjBundleSurjection.chartMap_eq_map`), and on each standard
open `D₊(f)`, `f` homogeneous of positive degree, both kernels are `chartIdeal ℱ`. -/
theorem ker_chartMap_eq_of_isQuotientByDegreeSubmodule {B₁ B₂ : SheafGradedAlgebra S}
    {ψ₁ : SheafGradedAlgebraHom 𝒜 B₁} {ψ₂ : SheafGradedAlgebraHom 𝒜 B₂}
    (hqc : ((ℱ.toSheafOfModules : S.Modules)).IsQuasicoherent)
    (hk₁ : IsQuotientByDegreeSubmodule 𝒜 ℱ ψ₁) (hk₂ : IsQuotientByDegreeSubmodule 𝒜 ℱ ψ₂)
    (hψ₁ : ProjBundleSurjection.SurjectiveOnAffineSections ψ₁)
    (hψ₂ : ProjBundleSurjection.SurjectiveOnAffineSections ψ₂)
    (U : S.Opens) (hU : IsAffineOpen U) :
    (ProjBundleSurjection.chartMap hψ₁ U hU).ker =
      (ProjBundleSurjection.chartMap hψ₂ U hU).ker := by
  have := isClosedImmersion_proj_map_sectionHom 𝒜 hψ₁ hU
  have := isClosedImmersion_proj_map_sectionHom 𝒜 hψ₂ hU
  rw [ProjBundleSurjection.chartMap_eq_map, ProjBundleSurjection.chartMap_eq_map]
  refine ker_projMap_eq_of_ker_awayMap_eq _ _ _ _
    (fun x : {p : 𝒜.sectionRing U × ℕ // p.1 ∈ 𝒜.grading U p.2 ∧ 0 < p.2} => x.1.1)
    (fun x => x.1.2) (fun x => x.2.1) (fun x => x.2.2) (iSup_basicOpen_positive_eq_top 𝒜 U)
    fun x => ?_
  rw [ker_awayMap_sectionHom_eq_chartIdeal 𝒜 ℱ ψ₁ hqc hk₁ hU x.2.1,
    ker_awayMap_sectionHom_eq_chartIdeal 𝒜 ℱ ψ₂ hqc hk₂ hU x.2.1]

/-- **The closed subscheme `Proj_S(𝒜/ℱ𝒜)` depends only on `ℱ`.**  Two degreewise surjections
`𝒜 ⟶ ℬ₁`, `𝒜 ⟶ ℬ₂` whose kernels are the graded ideal generated by the quasi-coherent
`ℱ ⊆ 𝒜_d` give closed immersions `Proj_S(ℬ₁) ⟶ Proj_S(𝒜)` and `Proj_S(ℬ₂) ⟶ Proj_S(𝒜)` with the
same ideal sheaf.  The charts over the affine opens of the base cover `Proj_S(𝒜)`, and over each
of them the two chart maps have the same kernel. -/
theorem ker_map_eq_of_isQuotientByDegreeSubmodule {B₁ B₂ : SheafGradedAlgebra S}
    {ψ₁ : SheafGradedAlgebraHom 𝒜 B₁} {ψ₂ : SheafGradedAlgebraHom 𝒜 B₂}
    (hqc : ((ℱ.toSheafOfModules : S.Modules)).IsQuasicoherent)
    (hk₁ : IsQuotientByDegreeSubmodule 𝒜 ℱ ψ₁) (hk₂ : IsQuotientByDegreeSubmodule 𝒜 ℱ ψ₂)
    (hψ₁ : ProjBundleSurjection.SurjectiveOnAffineSections ψ₁)
    (hψ₂ : ProjBundleSurjection.SurjectiveOnAffineSections ψ₂) :
    (ProjBundleSurjection.map hψ₁).ker = (ProjBundleSurjection.map hψ₂).ker := by
  have : IsClosedImmersion (ProjBundleSurjection.map hψ₁) :=
    ProjBundleSurjection.isClosedImmersion_map hψ₁
  have : IsClosedImmersion (ProjBundleSurjection.map hψ₂) :=
    ProjBundleSurjection.isClosedImmersion_map hψ₂
  exact KerChart.ker_eq_of_forall_chart _ _
    (fun U : AffineOpen S => (relativeProj 𝒜).chart U.1 U.2)
    (fun U => ProjBundleSurjection.chartMap hψ₁ U.1 U.2)
    (fun U => (relativeProj B₁).chart U.1 U.2)
    (fun U => (ProjBundleSurjection.isPullback_chart hψ₁ U.1 U.2).flip)
    (fun U => ProjBundleSurjection.chartMap hψ₂ U.1 U.2)
    (fun U => (relativeProj B₂).chart U.1 U.2)
    (fun U => (ProjBundleSurjection.isPullback_chart hψ₂ U.1 U.2).flip)
    (ProjBundleSurjection.iSup_opensRange_chart_eq_top (relativeProj 𝒜))
    fun U => ker_chartMap_eq_of_isQuotientByDegreeSubmodule 𝒜 hqc hk₁ hk₂ hψ₁ hψ₂ U.1 U.2

/-- **A presentation `Z = Proj_S(𝒜/ℱ𝒜)` has the ideal sheaf of `Proj_S(ℬ)` for every degreewise
surjection `𝒜 ⟶ ℬ` with kernel `ℱ𝒜`.**  Its own quotient homomorphism is one such surjection, and
its identification `Z ≅ Proj_S(𝒜/ℱ𝒜)` is an isomorphism over `Proj_S(𝒜)`. -/
theorem DegreeQuotientPresentation.ker_eq_ker_map {Z : Scheme.{u}}
    {i : Z ⟶ (relativeProj 𝒜).scheme} (p : DegreeQuotientPresentation 𝒜 i ℱ)
    (hqc : ((ℱ.toSheafOfModules : S.Modules)).IsQuasicoherent) {B : SheafGradedAlgebra S}
    {ψ : SheafGradedAlgebraHom 𝒜 B} (hk : IsQuotientByDegreeSubmodule 𝒜 ℱ ψ)
    (hψ : ProjBundleSurjection.SurjectiveOnAffineSections ψ) :
    i.ker = (ProjBundleSurjection.map hψ).ker := by
  have hiZ : i.ker = (ProjBundleSurjection.map p.surjective).ker := by
    conv_lhs => rw [← p.iso_comp]
    exact Scheme.Hom.ker_comp_of_isIso _ _
  rw [hiZ]
  exact ker_map_eq_of_isQuotientByDegreeSubmodule 𝒜 hqc p.kernel hk p.surjective hψ

/-- **For a degreewise surjection, `r_ψ : U(ψ) ⟶ Proj_S(𝒜)` of Tag 07ZG and the closed immersion
`Proj_S(ℬ) ⟶ Proj_S(𝒜)` of `…ProjBundleSurjection.map` have the same ideal sheaf.**  Over the
chart of an affine open `U` of the base both are cartesian over the chart of `Proj_S(𝒜)`
(`…Tag07ZGMorphism.isPullback_chart_relativeMapHom`, `…ProjBundleSurjection.isPullback_chart`),
and their chart maps are `Proj.map` of `ψ_U`, the first after the inclusion of the domain of
definition `D(ψ_U) = ⊤`, which is an isomorphism. -/
theorem ker_relativeMapHom_eq_ker_map {B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom 𝒜 B) (hψ : ProjBundleSurjection.SurjectiveOnAffineSections ψ)
    [QuasiCompact (Tag07ZGMorphism.relativeMapHom ψ)] :
    (Tag07ZGMorphism.relativeMapHom ψ).ker = (ProjBundleSurjection.map hψ).ker := by
  have : IsClosedImmersion (ProjBundleSurjection.map hψ) :=
    ProjBundleSurjection.isClosedImmersion_map hψ
  refine KerChart.ker_eq_of_forall_chart _ _
    (fun U : AffineOpen S => (relativeProj 𝒜).chart U.1 U.2)
    (fun U => Stacks.AlgebraicGeometry.ProjTwistChain.mapHom (𝒜.grading U.1) (B.grading U.1)
      (ψ.sectionHom U.1))
    (fun U => (Tag07ZGMorphism.chartPieceIso ψ U).hom ≫
        (relativeProj B).scheme.homOfLE
          (inf_le_left : ψ.relativeMapDomain ⊓ ((relativeProj B).toBase ⁻¹ᵁ U.1) ≤ _))
    (fun U => (Tag07ZGMorphism.isPullback_chart_relativeMapHom ψ U).flip)
    (fun U => ProjBundleSurjection.chartMap hψ U.1 U.2)
    (fun U => (relativeProj B).chart U.1 U.2)
    (fun U => (ProjBundleSurjection.isPullback_chart hψ U.1 U.2).flip)
    (ProjBundleSurjection.iSup_opensRange_chart_eq_top (relativeProj 𝒜)) fun U => ?_
  have hχ := ProjBundleSurjection.irrelevant_le_map_sectionHom hψ U.2
  have hdom := Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_irrelevant_le_map
    (𝒜.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) hχ
  have : IsIso (Stacks.AlgebraicGeometry.ProjShared.mapDomain (𝒜.grading U.1) (B.grading U.1)
      (ψ.sectionHom U.1)).ι := by
    rw [hdom, ← Scheme.topIso_hom]
    infer_instance
  rw [Tag07ZGMorphism.mapHom_eq_ι_comp_proj_map _ _ _ hχ, Scheme.Hom.ker_comp_of_isIso,
    ProjBundleSurjection.chartMap_eq_map]

/-- **A presentation `Z = Proj_S(𝒜/ℱ𝒜)` has the ideal sheaf of `r_ψ : U(ψ) ⟶ Proj_S(𝒜)`** for
every degreewise surjection `ψ : 𝒜 ⟶ ℬ` with kernel `ℱ𝒜`. -/
theorem DegreeQuotientPresentation.ker_eq_ker_relativeMapHom {Z : Scheme.{u}}
    {i : Z ⟶ (relativeProj 𝒜).scheme} (p : DegreeQuotientPresentation 𝒜 i ℱ)
    (hqc : ((ℱ.toSheafOfModules : S.Modules)).IsQuasicoherent) {B : SheafGradedAlgebra S}
    {ψ : SheafGradedAlgebraHom 𝒜 B} (hk : IsQuotientByDegreeSubmodule 𝒜 ℱ ψ)
    (hψ : ProjBundleSurjection.SurjectiveOnAffineSections ψ)
    [hqcψ : QuasiCompact (Tag07ZGMorphism.relativeMapHom ψ)] :
    i.ker = (Tag07ZGMorphism.relativeMapHom ψ).ker :=
  (p.ker_eq_ker_map 𝒜 hqc hk hψ).trans (ker_relativeMapHom_eq_ker_map 𝒜 ψ hψ).symm

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
