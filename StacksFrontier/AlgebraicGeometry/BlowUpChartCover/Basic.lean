module

public import StacksFrontier.AlgebraicGeometry.AffineBlowupLift.Chart

/-!
# The affine blowup charts cover the blowup

Let `X` be a scheme and `I` a quasi-coherent ideal sheaf on it. For an affine open `U` of `X` and
a section `a ∈ I.ideal U`, the affine blowup algebra `Γ(X, U)[I/a]` has
`Spec Γ(X, U)[I/a]` an open subscheme of `Bl_I(X)` ([Stacks, Tag 0804]). This file assembles the
*global* covering statement: as `U` runs over the affine opens of `X` and `a` over the sections of
`I` on `U`, those open subschemes cover all of `Bl_I(X)`.

Nothing new is proved about the local picture. `AlgebraicGeometry.blownUpAffine_chart_cover`
already says that for a fixed affine open `U` the charts attached to the sections `a ∈ I.ideal U`
cover the inverse image `b⁻¹(U)`, and the affine opens of `X` cover `X`; what is new here is only
the morphism-level packaging — the chart presented as a morphism out of `Spec Γ(X, U)[I/a]`
through `Stacks.AlgebraicGeometry.AffineBlowupLift.chartToBlowUp`, so that the covering statement
is about `Spec` of the blowup algebras rather than about standard opens of a projective spectrum.

## Main definitions

* `Stacks.BlowUpChartCover.chartRing`: the affine blowup algebra `Γ(X, U)[I/a]`.
* `Stacks.BlowUpChartCover.chart`: the chart as a morphism `Spec Γ(X, U)[I/a] ⟶ Bl_I(X)`.

## Main results

* `Stacks.BlowUpChartCover.isOpenImmersion_chart`: the chart is an open immersion.
* `Stacks.BlowUpChartCover.chart_blowUpToBase`: the chart lies over `U ⊆ X`, by `Spec` of the
  canonical map `Γ(X, U) ⟶ Γ(X, U)[I/a]`.
* `Stacks.BlowUpChartCover.iUnion_range_chart_eq_univ` and
  `Stacks.BlowUpChartCover.iSup_opensRange_chart_eq_top`: **the charts cover the blowup.**

## Implementation notes

The chart morphism is `AlgebraicGeometry.affineBlowupStandardOpenIso` — the identification of
`Spec Γ(X, U)[I/a]` with the standard open `D₊(a⁽¹⁾)` of the projective spectrum of the local
Rees algebra — followed by `Stacks.AlgebraicGeometry.AffineBlowupLift.chartToBlowUp`, which is
that standard open included into the spectrum and then into the blowup through
`Stacks.RelativeProj.Situation.relativeProjChart`. Being an open immersion is therefore a
composition of three: an isomorphism, the inclusion of an open, and the relative-`Proj` chart,
whose open-immersion property is read off the cartesian square
`Stacks.RelativeProj.Situation.relativeProjChart_isPullback`.

No `@[stacks 0804]` attribute is attached here. Tag 0804's covering assertion is already
registered on `AlgebraicGeometry.blownUpAffine_chart_cover`, which is the statement over one
affine open of the base; the global statement below is a corollary of it together with the fact
that the affine opens form a basis, and adds no assertion of the tag.

## References

* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.BlowUpChartCover

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)

/-- The coordinate ring `Γ(X, U)[I/a]` of the standard affine chart of the blowup at `a`: the
affine blowup algebra of the ideal `I.ideal U` at `a`, inside the localization away from `a`. -/
abbrev chartRing : Type u :=
  affineBlowupAlgebra (I.ideal U) (a : Γ(X, U.1)) (Localization.Away (a : Γ(X, U.1)))

/-- **The standard affine chart of the blowup at `a`**, as a morphism
`Spec Γ(X, U)[I/a] ⟶ Bl_I(X)`: the identification of [Stacks, Tag 0804] of the spectrum of the
blowup algebra with the standard open `D₊(a⁽¹⁾)` of the local Rees projective spectrum, followed
by the inclusion of that standard open into the blowup. -/
noncomputable def chart : Spec (.of (chartRing I U a)) ⟶ blowUp I :=
  letI := (reesSituation I).sectionRingGradedRing U.1
  letI := (reesSituation I).sectionRingGradingGradedRing U.1
  (affineBlowupStandardOpenIso I U a).hom ≫
    Stacks.AlgebraicGeometry.AffineBlowupLift.chartToBlowUp I U a

/-- The chart is an open immersion: it is an isomorphism, followed by the inclusion of an open
subscheme of the local Rees projective spectrum, followed by the relative-`Proj` chart over `U`,
which is an open immersion because it is the base change of `U ⊆ X`. -/
instance isOpenImmersion_chart : IsOpenImmersion (chart I U a) := by
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  have hchart : IsOpenImmersion
      (Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U) :=
    MorphismProperty.of_isPullback
      (Stacks.RelativeProj.Situation.relativeProjChart_isPullback (reesSituation I) U).flip
      (show IsOpenImmersion U.1.ι from inferInstance)
  dsimp only [chart, Stacks.AlgebraicGeometry.AffineBlowupLift.chartToBlowUp]
  infer_instance

/-- **The chart lies over `U`.** Composing the chart with the blowup morphism gives `Spec` of the
canonical map `Γ(X, U) ⟶ Γ(X, U)[I/a]`, followed by the inclusion of the affine open `U`. -/
theorem chart_blowUpToBase :
    chart I U a ≫ blowUpToBase I =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (chartRing I U a))) ≫
        U.2.fromSpec := by
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  dsimp only [chart]
  rw [Category.assoc, Stacks.AlgebraicGeometry.AffineBlowupLift.chartToBlowUp_blowUpToBase]
  simpa only [Category.assoc, IsAffineOpen.fromSpec] using
    congrArg (fun k => k ≫ U.1.ι) (affineBlowupStandardOpenIso_over I U a)

/-- **The chart's image is the standard open of the local Rees projective spectrum**, included
into the blowup: the identification of [Stacks, Tag 0804] the chart is composed with is an
isomorphism, so it changes no image. -/
theorem range_chart :
    Set.range (chart I U a) =
      Set.range ((Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U a).1).ι ≫
          Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U) := by
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(affineBlowupStandardOpenIso I U a).hom w, rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨(affineBlowupStandardOpenIso I U a).inv w, ?_⟩
    show ((Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a).1).ι ≫
        Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U)
          ((affineBlowupStandardOpenIso I U a).hom
            ((affineBlowupStandardOpenIso I U a).inv w)) = _
    simp

/-- **The affine blowup charts cover the blowup.** Every point of `Bl_I(X)` lies in the image of
`Spec Γ(X, U)[I/a]` for some affine open `U` of `X` and some section `a ∈ I.ideal U`.

The point lies over some affine open `U` of `X`, because the affine opens are a basis;
`AlgebraicGeometry.blownUpAffine_chart_cover` then puts it on the standard open of the local Rees
projective spectrum attached to some `a ∈ I.ideal U`, and
`AlgebraicGeometry.affineBlowupStandardOpenIso` is surjective on points. -/
theorem iUnion_range_chart_eq_univ :
    (⋃ (U : X.affineOpens) (a : I.ideal U), Set.range (chart I U a)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((blowUpToBase I) x)) isOpen_univ
  set U : X.affineOpens := ⟨U₀, hU₀⟩
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  have hcover : x ∈ ⋃ b : I.ideal U, Set.range
      ((Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U b).1).ι ≫
        Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U) := by
    rwa [blownUpAffine_chart_cover I U]
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hcover
  exact Set.mem_iUnion₂.mpr ⟨U, b, (range_chart I U b).symm ▸ hb⟩

/-- **The affine blowup charts cover the blowup**, as a supremum of opens: the open ranges of the
charts `Spec Γ(X, U)[I/a] ⟶ Bl_I(X)` have supremum `⊤`. -/
theorem iSup_opensRange_chart_eq_top :
    (⨆ (U : X.affineOpens) (a : I.ideal U), (chart I U a).opensRange) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨U, a, hU⟩ := Set.mem_iUnion₂.mp ((iUnion_range_chart_eq_univ I).ge (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨U, Opens.mem_iSup.mpr ⟨a, hU⟩⟩

end Stacks.BlowUpChartCover

end
