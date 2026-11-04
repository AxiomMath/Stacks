module

public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothAffineLocally
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsLocallyProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
import StacksCore.Tactic.StacksAttribute

/-!
# Relative differentials of a smooth morphism of algebraic spaces are locally projective

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`.
`AlgebraicGeometry.Space.isLocallyProjective_sheafOfDifferentials` is [Stacks Project,
Tag 061I]: if `f` is *formally* smooth then `Ω_{X/Y}` is locally projective on `X`.

That form of the statement cannot be used inside the proof of the implication from smoothness
to formal smoothness of [Stacks Project, Tag 04AM], where local projectivity of `Ω_{X/Y}` is
one of the inputs to the triviality of the pseudo-torsor of lifts: formal smoothness is there
the conclusion, so the hypothesis of Tag 061I is exactly what is not yet available.  This file
removes the circularity by deriving the same conclusion from smoothness directly.

## Main results

* `AlgebraicGeometry.Space.isLocallyProjective_sheafOfDifferentials_of_isSmooth`: the sheaf of
  relative differentials of a *smooth* morphism of algebraic spaces is locally projective.

## Implementation notes

Nothing of Tag 04AM is used, and in particular not the implication this is wanted for.
`AlgebraicGeometry.Space.IsSmooth` is a condition on every commuting square of étale scheme
charts, so a surjective such square — produced from an atlas of the target by
`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift` — comes with its morphism of
schemes *smooth*, and a smooth morphism of schemes is affine-locally formally smooth by
`Stacks.Smooth.smooth_iff_formallySmoothAffineLocally`, which is Tag 02H6 in affine-local form
and is in the library.  That is precisely the data that the proof of Tag 061I consumes: the hypothesis
`AlgebraicGeometry.Space.FormallySmooth` enters that proof only through
`AlgebraicGeometry.Space.holdsOnSurjectiveEtaleChart_formallySmoothAffineLocally`, which
produces such a square and nothing else.

The chart data are therefore assembled here and handed to the same two steps the proof of
Tag 061I uses — the identification
`AlgebraicGeometry.Space.restrictToChartSchemeSheafOfDifferentialsIso` of the restriction of
`Ω_{X/Y}` to the chart scheme with `Ω` of the morphism of schemes, and the descent
`AlgebraicGeometry.Space.exists_surjective_isLocallyProjective_iff_forall` of local
projectivity from one surjective chart to all charts.

No tag is placed: Tag 061I is already carried, for its own hypothesis, by
`AlgebraicGeometry.Space.isLocallyProjective_sheafOfDifferentials`.

## References

* [Stacks Project, Tag 061I](https://stacks.math.columbia.edu/tag/061I)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sheaf of relative differentials of a smooth morphism of algebraic spaces is locally
projective.**  This is the conclusion of [Stacks Project, Tag 061I] under the hypothesis that
`f` is smooth rather than formally smooth, which is what the proof of the implication from
smoothness to formal smoothness of [Stacks Project, Tag 04AM] can supply. -/
theorem isLocallyProjective_sheafOfDifferentials_of_isSmooth {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsSmooth B S hS f.hom) :
    IsLocallyProjective B S hS X.2
      ⟨sheafOfDifferentials B S hS f, isQuasicoherentOnSite_sheafOfDifferentials B S hS f⟩ := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := Y.2.exists_atlas
  obtain ⟨U, a, α, hcomm, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.2 Y.2 f.hom V b hbSurj hbEtale
  have hα : Stacks.Smooth.FormallySmoothAffineLocally
      ((BigFppfOver.toScheme B S hS).map α) :=
    ((Stacks.Smooth.smooth_iff_formallySmoothAffineLocally
      ((BigFppfOver.toScheme B S hS).map α)).mp
        (hf U V a b α haEtale hbEtale hcomm.symm)).1
  set A : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk a, haEtale⟩ with hA
  have hchart : Scheme.Modules.IsLocallyProjective
      (restrictToChartScheme B S hS X.1 X.2 (sheafOfDifferentials B S hS f) A) :=
    Scheme.Modules.isLocallyProjective_of_iso
      (restrictToChartSchemeSheafOfDifferentialsIso B S hS f U V a b α haEtale hbEtale
        hcomm.symm).symm
      (Stacks.Smooth.isLocallyProjective_relativeDifferentials_of_formallySmoothAffineLocally
        ((BigFppfOver.toScheme B S hS).map α) hα)
  have hall := (exists_surjective_isLocallyProjective_iff_forall B S hS X.1 X.2
    (sheafOfDifferentials B S hS f) (isQuasicoherentOnSite_sheafOfDifferentials B S hS f)).1
    ⟨A, isSurjective_of_presheafSurjective B S hS a haSurj, hchart⟩
  exact fun W => Scheme.Modules.isLocallyProjective_of_iso
    (restrictToChartIsoRestrictToChartScheme B S hS X.2 _ W).symm (hall W)

end AlgebraicGeometry.Space

end
