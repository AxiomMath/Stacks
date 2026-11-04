module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-compactness and quasi-separatedness from a presentation

An algebraic space presented by `R ⇉ U` is quasi-compact as soon as the underlying space of
`U` is compact, and quasi-separated as soon as that space is quasi-separated and the source
projection `R ⟶ U` is quasi-compact.

The first is immediate from the definition of Stacks 03E3, which asks for exactly such an
atlas. The second is Stacks 07S4, whose hypothesis on the kernel pair of the atlas is
supplied by the presentation: the relation *is* that kernel pair.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_presentation`: quasi-compactness.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_presentation`:
  quasi-separatedness.
* `AlgebraicGeometry.Space.presheaf_quasiCompact_toSpace_of_presentation`: the chart of a
  presentation with quasi-compact source projection is itself quasi-compact, as a
  representable morphism of presheaves.

## Implementation notes

The three results share one step: the second projection of the kernel pair of the chart is
quasi-compact. That projection is the source projection of the presentation transported along
`CategoryTheory.IsPullback.isoPullback`, so the statement is quasi-compactness of a morphism
of the site, promoted to the relative property of the Yoneda embedding by
`CategoryTheory.MorphismProperty.relative_map`.

Quasi-compactness of the chart itself is then Stacks 02WZ at the property `QuasiCompact`,
taking the chart as its own surjective étale atlas: the base change of the chart along itself
is the projection just discussed.

## References

* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
* [Stacks Project, Tag 02WZ](https://stacks.math.columbia.edu/tag/02WZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
  (P : Presentation B S hS F hF)

/-- The property of morphisms of the big fppf site of `S` of having quasi-compact underlying
morphism of schemes is stable under base change. -/
@[ega "I 6.6.4" "(iii), special case"]
theorem isStableUnderBaseChange_inverseImage_quasiCompact :
    (MorphismProperty.inverseImage (@QuasiCompact.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨fun sq hf => MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @QuasiCompact.{u}) (sq.map (BigFppfOver.toScheme B S hS)) hf⟩

/-- **The second projection of the kernel pair of the chart of a presentation is
quasi-compact** as soon as the source projection of the presentation is. The relation of the
presentation is that kernel pair, and the two projections correspond under
`CategoryTheory.IsPullback.isoPullback`. -/
theorem presheaf_quasiCompact_pullback_snd_of_presentation
    (hsource : QuasiCompact ((BigFppfOver.toScheme B S hS).map P.source)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage (@QuasiCompact.{u})
      (BigFppfOver.toScheme B S hS))) (pullback.snd P.toSpace P.toSpace) := by
  have _ := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS (@QuasiCompact.{u})
  have hmap : (MorphismProperty.presheaf (MorphismProperty.inverseImage (@QuasiCompact.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map P.source) :=
    MorphismProperty.relative_map hsource
  simpa only [P.isPullback.isoPullback_inv_snd] using
    MorphismProperty.RespectsIso.precomp _ P.isPullback.isoPullback.inv
      (yoneda.map P.source) hmap

/-- **The chart of a presentation with quasi-compact source projection is quasi-compact.**

This is Stacks 02WZ at the property `QuasiCompact`, with the chart taken as its own
surjective étale atlas: its base change along itself is the second projection of its kernel
pair, which is `presheaf_quasiCompact_pullback_snd_of_presentation`. -/
theorem presheaf_quasiCompact_toSpace_of_presentation
    (hsource : QuasiCompact ((BigFppfOver.toScheme B S hS).map P.source)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage (@QuasiCompact.{u})
      (BigFppfOver.toScheme B S hS))) P.toSpace := by
  have _ := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS (@QuasiCompact.{u})
  refine (presheaf_inverseImage_iff_atlas_snd B S hS (@QuasiCompact.{u}) P.toSpace
    P.etale.rep P.U P.toSpace P.surjective P.etale).mpr ?_
  have hsnd := presheaf_quasiCompact_pullback_snd_of_presentation B S hS hF P hsource
  have hiso := MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage (@QuasiCompact.{u})
      (BigFppfOver.toScheme B S hS)))
    (P.etale.rep.isPullback P.toSpace).isoPullback.hom
    (pullback.snd P.toSpace P.toSpace) hsnd
  rw [IsPullback.isoPullback_hom_snd] at hiso
  exact MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage (@QuasiCompact.{u}) (BigFppfOver.toScheme B S hS))
    (F := yoneda) hiso

/-- **Stacks 03E3.** An algebraic space presented by a chart whose underlying space is
compact is quasi-compact: the chart is the surjective étale atlas the definition asks
for. -/
theorem isQuasiCompactSpace_of_presentation
    (hcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj P.U)) :
    IsQuasiCompactSpace B S hS F :=
  ⟨P.U, P.toSpace, hcompact, P.surjective, isEtale_of_presheaf_etale B S hS P.etale⟩

/-- **Stacks 07S4 for a presentation.** An algebraic space presented by a chart whose
underlying space is quasi-separated, with quasi-compact source projection, is
quasi-separated.

The relation of the presentation is the kernel pair of the chart, so
`presheaf_quasiCompact_pullback_snd_of_presentation` supplies the hypothesis of Stacks
07S4. -/
@[stacks 03BS "part (3): quasi-separated"]
theorem isAbsolutelyQuasiSeparated_of_presentation (hZ : B.Contains (⊤_ Scheme.{u}))
    (hseparated : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj P.U))
    (hsource : QuasiCompact ((BigFppfOver.toScheme B S hS).map P.source)) :
    IsAbsolutelyQuasiSeparated B S hS hZ F :=
  isQuasiSeparated_of_etaleAtlas_quasiCompact_projection B S hS hZ F hF
    ⟨P.U, P.toSpace, hseparated, P.surjective, P.etale,
      Or.inr (presheaf_quasiCompact_pullback_snd_of_presentation B S hS hF P hsource)⟩

end AlgebraicGeometry.Space

end
