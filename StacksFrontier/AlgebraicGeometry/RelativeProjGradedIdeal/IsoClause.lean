module

public import StacksFrontier.AlgebraicGeometry.Morphism.KerChart
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.DegreeDefs
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.Kernel
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.SectionQuotient

/-!
# Tag 0801's `iso` clause, reduced to the charts

Work in Situation 01NN: a scheme `S`, a quasi-coherent graded `𝒪_S`-algebra `𝒜` and a graded
ideal `ℐ` with quasi-coherent pieces, so that `𝒜/ℐ` and the closed immersion
`Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)` of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Quotient.lean` are available. Let
`i : Z ⟶ Proj_S(𝒜)` be a closed immersion. Tag 0801's remaining clause asks for an identification
`Z ≅ Proj_S(𝒜/ℐ)` over `Proj_S(𝒜)`.

This file reduces that clause, in two steps, to a statement about one chart:

* both morphisms being closed immersions, the identification **is** an equality of kernel ideal
  sheaves — `…gradedQuotientPresentation_of_ker_eq` below builds the whole of Tag 0801's
  `GradedQuotientPresentation` out of that equality;
* and the equality of kernel ideal sheaves is **local on the charts** of `Proj_S(𝒜)` —
  `…ker_eq_quotAmbientHom_of_forall_chart` below, from
  `Stacks.AlgebraicGeometry.KerChart.ker_eq_of_forall_chart`.

## Main definitions

* `…RelativeProjGradedIdeal.gradedQuotientPresentation_of_ker_eq`: **Tag 0801's graded-quotient
  presentation, from the equality of kernel ideal sheaves.**

## Main results

* `…RelativeProjGradedIdeal.ker_eq_of_forall_chart`: an equality of kernel ideal sheaves on
  `Proj_S(𝒜)` reduces to the charts over the affine opens of the base.
* `…RelativeProjGradedIdeal.ker_eq_quotAmbientHom_of_forall_chart`: **Tag 0801's `iso` clause
  reduces to one equality of kernels per chart**, against the chart map of `𝒜 ⟶ 𝒜/ℐ`, which
  `…chartMap_quotMk_eq` identifies with the absolute `Proj` of a graded quotient map.
* `…RelativeProjGradedIdeal.gradedQuotientPresentation_kernel_of_forall_chart`: the same at
  `ℐ = ker ψ`, which is the form Tag 0801's own chain takes — its `ℐ` is
  `…RelativeProjTwists.closedVanishingIdeal`, the kernel of `…psiClosedHom`, and its ambient
  morphism is `…kernelAmbientHom` of that `ψ`.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)

## Not done here

No Stacks tag is claimed here. **Tag 0801's relative `iso` clause is proved**, downstream, in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/VanishingPresentation.lean`: the
chart-level hypothesis the reductions of this file leave is discharged there by
`Stacks.AlgebraicGeometry.RelativeProjTwists.ker_eq_chartMap_ker`, and the whole of
`…RelativeProjGradedIdeal.VanishingIdealPresentation` is built as
`…RelativeProjTwists.vanishingIdealPresentation`, on no hypothesis beyond Tag 0801's own. Tag
0803 is registered with that presentation discharged in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/FiniteTypePresentationOffSupport.lean`.

What closed the clause, on top of the reductions here: the chart comparison
`…RelativeProjTwists.pullbackGlobalSections_degreeSection_eq_zero_iff`, which composes
`…RelativeProjTwists.TwistData.ψ_chart` with the base change of the unit `M ⟶ i_*i^*M` along an
arbitrary open immersion (`Stacks.AlgebraicGeometry.ChartUnit.app_unit_eq_zero_iff`) and with
`…RelativeProjTwists.restrictionHom_app_eq_zero_iff_restrictionToClosed`; the resulting equality
of homogeneous ideals `…RelativeProjTwists.sectionGradedIdeal_eq_idealOfClosedSubscheme`; and the
absolute case of Tag 0801 restated at an `AddSubgroup`-valued grading,
`Stacks.ProjChartKerQuotient.ker_eq_ker_projMap_quotientMk`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

universe u

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S)

/-! ### An equality of kernel ideal sheaves on a relative Proj reduces to the charts -/

/-- **An equality of kernel ideal sheaves on `Proj_S(𝒜)` reduces to the charts over the affine
opens of the base.** The chart images cover `Proj_S(𝒜)`
(`…ProjBundleSurjection.iSup_opensRange_chart_eq_top`) and each chart is an open immersion, so
this is `Stacks.AlgebraicGeometry.KerChart.ker_eq_of_forall_chart` at the tautological pullback
squares. -/
public theorem ker_eq_of_forall_chart {Y₁ Y₂ : Scheme.{u}}
    (g₁ : Y₁ ⟶ (relativeProj 𝒜).scheme) (g₂ : Y₂ ⟶ (relativeProj 𝒜).scheme)
    [QuasiCompact g₁] [QuasiCompact g₂]
    (h : ∀ U : AffineOpen S,
      (pullback.snd g₁ ((relativeProj 𝒜).chart U.1 U.2)).ker =
        (pullback.snd g₂ ((relativeProj 𝒜).chart U.1 U.2)).ker) :
    g₁.ker = g₂.ker :=
  KerChart.ker_eq_of_forall_chart g₁ g₂
    (fun U : AffineOpen S => (relativeProj 𝒜).chart U.1 U.2)
    (fun _ => pullback.snd _ _) (fun _ => pullback.fst _ _)
    (fun _ => (IsPullback.of_hasPullback _ _).flip)
    (fun _ => pullback.snd _ _) (fun _ => pullback.fst _ _)
    (fun _ => (IsPullback.of_hasPullback _ _).flip)
    (ProjBundleSurjection.iSup_opensRange_chart_eq_top (relativeProj 𝒜)) h

/-! ### Tag 0801's `iso` clause from the equality of kernel ideal sheaves -/

variable (ℐ : GradedIdeal 𝒜) (hqc : IsQuasicoherentQuotPieces 𝒜 ℐ)
  (hℐ : ∀ n : ℤ, ((ℐ.piece n).toSheafOfModules : S.Modules).IsQuasicoherent)

/-- **Tag 0801's graded-quotient presentation, from the equality of kernel ideal sheaves.** Four
of the five fields of `…GradedQuotientPresentation` are supplied by the sibling files;
the identification `Z ≅ Proj_S(𝒜/ℐ)` and its compatibility over `Proj_S(𝒜)` come from the
equality of the two closed immersions' kernels, by
`Stacks.AlgebraicGeometry.KerChart.isoOfKerEq`. -/
public def gradedQuotientPresentation_of_ker_eq {Z : Scheme.{u}}
    (i : Z ⟶ (relativeProj 𝒜).scheme) [IsClosedImmersion i]
    (h : i.ker = (quotAmbientHom 𝒜 ℐ hqc hℐ).ker) :
    GradedQuotientPresentation 𝒜 i :=
  haveI : IsClosedImmersion (quotAmbientHom 𝒜 ℐ hqc hℐ) :=
    isClosedImmersion_quotAmbientHom 𝒜 ℐ hqc hℐ
  { target := quotSheafGradedAlgebra 𝒜 ℐ hqc
    hom := quotMk 𝒜 ℐ hqc
    surjective := surjectiveOnAffineSections_quotMk 𝒜 ℐ hqc hℐ
    iso := KerChart.isoOfKerEq (quotAmbientHom 𝒜 ℐ hqc hℐ) i h.symm
    iso_comp := KerChart.isoOfKerEq_hom_comp _ _ _ }

/-- **Tag 0801's `iso` clause reduces to one equality of kernel ideal sheaves per chart.** Over an
affine open `U` of the base, the hypothesis compares the part of `Z` lying over the chart with the
chart map of `𝒜 ⟶ 𝒜/ℐ`, which `…chartMap_quotMk_eq` identifies with `AlgebraicGeometry.Proj.map`
of the graded quotient map of `Γ(U, 𝒜)` by `…sectionGradedIdeal`. -/
public theorem ker_eq_quotAmbientHom_of_forall_chart {Z : Scheme.{u}}
    (i : Z ⟶ (relativeProj 𝒜).scheme) [IsClosedImmersion i]
    (h : ∀ U : AffineOpen S,
      (pullback.snd i ((relativeProj 𝒜).chart U.1 U.2)).ker =
        (ProjBundleSurjection.chartMap
          (surjectiveOnAffineSections_quotMk 𝒜 ℐ hqc hℐ) U.1 U.2).ker) :
    i.ker = (quotAmbientHom 𝒜 ℐ hqc hℐ).ker := by
  have : IsClosedImmersion (quotAmbientHom 𝒜 ℐ hqc hℐ) :=
    isClosedImmersion_quotAmbientHom 𝒜 ℐ hqc hℐ
  exact KerChart.ker_eq_of_forall_chart i (quotAmbientHom 𝒜 ℐ hqc hℐ)
    (fun U : AffineOpen S => (relativeProj 𝒜).chart U.1 U.2)
    (fun _ => pullback.snd _ _) (fun _ => pullback.fst _ _)
    (fun _ => (IsPullback.of_hasPullback _ _).flip)
    (fun U => ProjBundleSurjection.chartMap
      (surjectiveOnAffineSections_quotMk 𝒜 ℐ hqc hℐ) U.1 U.2)
    (fun U => (relativeProj (quotSheafGradedAlgebra 𝒜 ℐ hqc)).chart U.1 U.2)
    (fun U => (ProjBundleSurjection.isPullback_chart
      (surjectiveOnAffineSections_quotMk 𝒜 ℐ hqc hℐ) U.1 U.2).flip)
    (ProjBundleSurjection.iSup_opensRange_chart_eq_top (relativeProj 𝒜)) h

/-- **Tag 0801's graded-quotient presentation, reduced to the charts.** The two reductions of this
file, composed: a chart-by-chart equality of kernel ideal sheaves gives the whole presentation. -/
public def gradedQuotientPresentation_of_forall_chart {Z : Scheme.{u}}
    (i : Z ⟶ (relativeProj 𝒜).scheme) [IsClosedImmersion i]
    (h : ∀ U : AffineOpen S,
      (pullback.snd i ((relativeProj 𝒜).chart U.1 U.2)).ker =
        (ProjBundleSurjection.chartMap
          (surjectiveOnAffineSections_quotMk 𝒜 ℐ hqc hℐ) U.1 U.2).ker) :
    GradedQuotientPresentation 𝒜 i :=
  gradedQuotientPresentation_of_ker_eq 𝒜 ℐ hqc hℐ i
    (ker_eq_quotAmbientHom_of_forall_chart 𝒜 ℐ hqc hℐ i h)

/-! ### The same at the quotient by the kernel of a homomorphism -/

/-- **Tag 0801's `iso` clause at `𝒜/ker ψ`, reduced to the charts.** This is the shape the tag's
own chain takes: its graded ideal is `…RelativeProjTwists.closedVanishingIdeal`, the degreewise
kernel of `…psiClosedHom`, and the morphism its `iso_comp` compares against is
`…kernelAmbientHom` of that `ψ`. -/
public theorem ker_eq_kernelAmbientHom_of_forall_chart {ℬ : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom 𝒜 ℬ) {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme)
    [IsClosedImmersion i]
    (h : ∀ U : AffineOpen S,
      (pullback.snd i ((relativeProj 𝒜).chart U.1 U.2)).ker =
        (ProjBundleSurjection.chartMap
          (surjectiveOnAffineSections_quotMkKernel ψ) U.1 U.2).ker) :
    i.ker = (kernelAmbientHom ψ).ker :=
  ker_eq_quotAmbientHom_of_forall_chart 𝒜 (kernelGradedIdeal ψ)
    (isQuasicoherentQuotPieces_kernelGradedIdeal ψ)
    (isQuasicoherent_kernelGradedIdeal_piece ψ) i h

/-- **Tag 0801's graded-quotient presentation at `𝒜/ker ψ`, reduced to the charts.** -/
public def gradedQuotientPresentation_kernel_of_forall_chart {ℬ : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom 𝒜 ℬ) {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme)
    [IsClosedImmersion i]
    (h : ∀ U : AffineOpen S,
      (pullback.snd i ((relativeProj 𝒜).chart U.1 U.2)).ker =
        (ProjBundleSurjection.chartMap
          (surjectiveOnAffineSections_quotMkKernel ψ) U.1 U.2).ker) :
    GradedQuotientPresentation 𝒜 i :=
  gradedQuotientPresentation_of_forall_chart 𝒜 (kernelGradedIdeal ψ)
    (isQuasicoherentQuotPieces_kernelGradedIdeal ψ)
    (isQuasicoherent_kernelGradedIdeal_piece ψ) i h

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
