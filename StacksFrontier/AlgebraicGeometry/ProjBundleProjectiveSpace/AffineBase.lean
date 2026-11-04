module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled

/-!
# Over an affine base the relative homogeneous spectrum is an absolute one

The relative `Proj` of Tag 01NQ is glued from the absolute `Proj Γ(U, 𝒜)` over the affine opens
`U` of the base, and the chart over `U` is cartesian over the inclusion `U ⊆ S`. When the base is
itself affine, `⊤` is one of those affine opens and its inclusion is an isomorphism, so the chart
over `⊤` is an isomorphism: `Proj_S(𝒜) ≅ Proj Γ(S, 𝒜)` over `S`.

This is recorded as absent in the `Not done here` section of
`StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled`, which says nothing is proved about the
glued datum beyond its construction.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjAffineBase.isIso_chart_top`: the chart over `⊤` is an
  isomorphism when `⊤` is affine.
* `Stacks.AlgebraicGeometry.RelativeProjAffineBase.topChartIso` and
  `topChartIso_hom_relativeProjToBase`: that isomorphism, and the fact that it is an isomorphism
  over the base.
* `Stacks.AlgebraicGeometry.RelativeProjAffineBase.exists_iso_relativeProj_of_isAffine`: the same
  for the assembled `Stacks.AlgebraicGeometry.RelativeProj.relativeProj`.

## Implementation notes

Being an isomorphism is stable under base change, as
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.isomorphisms`, so the conclusion is one
application of `CategoryTheory.MorphismProperty.of_isPullback` to
`Stacks.AlgebraicGeometry.RelativeProjGlue.isPullback_chart` once
`AlgebraicGeometry.Scheme.Opens.ι` of `⊤` is known to be an isomorphism, which is
`AlgebraicGeometry.Scheme.topIso`.

`AlgebraicGeometry.Scheme.AffineZariskiSite` is a `def` for the subtype of affine opens, so the
object `⊤` of the site is written as an anonymous constructor at an ascribed type at every
occurrence; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled`.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)

## Not done here

No project tag is attached: Tag 01NQ's assertion is the construction of the glued datum, already
tagged at `Stacks.AlgebraicGeometry.RelativeProj.relativeProj`.

Nothing here identifies the absolute `Proj Γ(S, 𝒜)` with anything else; in particular the graded
ring of sections of a symmetric algebra is not computed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.RelativeProjAffineBase

universe u

variable {S : Scheme.{u}} (𝒜 : GradedAlgebra S)

/-- The inclusion of the top open of a scheme is an isomorphism. -/
public theorem isIso_ι_top : IsIso ((⊤ : S.Opens).ι) := by
  rw [← Scheme.topIso_hom S]
  infer_instance

/-- **Over an affine base the chart over `⊤` is an isomorphism**: it is the base change of the
inclusion `⊤ ⊆ S`, which is an isomorphism. -/
public theorem isIso_chart_top (hS : IsAffineOpen (⊤ : S.Opens)) :
    IsIso (RelativeProjGlue.chart 𝒜 (⟨(⊤ : S.Opens), hS⟩ : S.AffineZariskiSite)) :=
  MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u})
    (isPullback_chart 𝒜 (⟨(⊤ : S.Opens), hS⟩ : S.AffineZariskiSite)) isIso_ι_top

/-- **Over an affine base the relative homogeneous spectrum is the absolute `Proj` of the graded
ring of global sections.** -/
public def topChartIso (hS : IsAffineOpen (⊤ : S.Opens)) :
    𝒜.projOver (⟨(⊤ : S.Opens), hS⟩ : S.AffineZariskiSite) ≅ relativeProj 𝒜 :=
  haveI := isIso_chart_top 𝒜 hS
  asIso (RelativeProjGlue.chart 𝒜 (⟨(⊤ : S.Opens), hS⟩ : S.AffineZariskiSite))

/-- The isomorphism is an isomorphism over the base. -/
public theorem topChartIso_hom_relativeProjToBase (hS : IsAffineOpen (⊤ : S.Opens)) :
    (topChartIso 𝒜 hS).hom ≫ relativeProjToBase 𝒜 =
      𝒜.toBase (⟨(⊤ : S.Opens), hS⟩ : S.AffineZariskiSite) :=
  chart_relativeProjToBase 𝒜 (⟨(⊤ : S.Opens), hS⟩ : S.AffineZariskiSite)

/-- **The assembled form.** Over an affine base the relative homogeneous spectrum of a sheaf-level
graded algebra is the absolute `Proj` of its graded ring of global sections, over the base. -/
public theorem exists_iso_relativeProj_of_isAffine (A : SheafGradedAlgebra S)
    (hS : IsAffineOpen (⊤ : S.Opens)) :
    ∃ e : AlgebraicGeometry.Proj (A.grading (⊤ : S.Opens)) ≅
        (RelativeProj.relativeProj A).scheme,
      e.hom ≫ (RelativeProj.relativeProj A).toBase =
        RelativeProj.projInclusionToOpen A (⊤ : S.Opens) hS ≫ (⊤ : S.Opens).ι :=
  ⟨topChartIso A.toGradedAlgebra hS,
    (topChartIso_hom_relativeProjToBase A.toGradedAlgebra hS).trans
      (A.toGradedAlgebra.toOpen_ι (⟨(⊤ : S.Opens), hS⟩ : S.AffineZariskiSite)).symm⟩

end Stacks.AlgebraicGeometry.RelativeProjAffineBase

end
