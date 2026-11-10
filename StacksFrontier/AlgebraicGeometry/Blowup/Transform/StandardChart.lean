module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.AffineCharts

/-!
# The standard affine charts of a blowup

The blowup of a scheme `X` in a quasi-coherent ideal `I` is covered by the spectra of the
affine blowup algebras `Γ(X, U)[I(U)/a]`, one for each affine open `U` of `X` and each section
`a` of `I(U)`. This file packages those charts and their structure morphisms.

## Main definitions

* `AlgebraicGeometry.blowUpAffineChartRing`: the coordinate ring `Γ(X, U)[I(U)/a]` of a chart.
* `AlgebraicGeometry.blowUpAffineChart`: the chart, as an open immersion into the blowup.
* `AlgebraicGeometry.blowUpAffineChartCover`: the charts, as an open cover of the blowup.

## Main results

* `AlgebraicGeometry.blowUpAffineChart_comp_blowUpToBase`: the structure morphism of a chart to
  the base is `Spec` of the canonical map `Γ(X, U) → Γ(X, U)[I(U)/a]`, followed by the
  inclusion of `U`.
* `AlgebraicGeometry.exists_mem_range_blowUpAffineChart`: the charts cover the blowup.

## Implementation notes

A chart is the composite of the identification of `Spec Γ(X, U)[I(U)/a]` with a basic open of
the `Proj` of the Rees algebra over `U` (`AlgebraicGeometry.affineBlowupStandardOpenIso`, the
first assertion of Stacks tag 0804) with the relative-`Proj` chart of the blowup over `U`. That
these cover is the second assertion of the same tag,
`AlgebraicGeometry.blownUpAffine_chart_cover`.

## References

* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The coordinate ring of the standard affine chart of the blowup of `X` in `I` attached to an
affine open `U` and a section `a` of `I(U)`: the affine blowup algebra `Γ(X, U)[I(U)/a]`. -/
abbrev blowUpAffineChartRing (U : X.affineOpens) (a : I.ideal U) : Type u :=
  affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (.op U.1))
    (Localization.Away (a : X.presheaf.obj (.op U.1)))

/-- The relative-`Proj` chart of the blowup of `X` in `I` over an affine open `U` of `X`, from the
`Proj` of the Rees algebra over `U` into the blowup, is an open immersion. -/
instance isOpenImmersion_relativeProjChart_reesSituation (U : X.affineOpens) :
    IsOpenImmersion (Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U) :=
  MorphismProperty.of_isPullback
    (Stacks.RelativeProj.Situation.relativeProjChart_isPullback (reesSituation I) U).flip
    inferInstance

/-- The standard affine chart of the blowup of `X` in `I` attached to an affine open `U` of `X`
and a section `a` of `I(U)`: the spectrum of `Γ(X, U)[I(U)/a]`, mapped into the blowup. -/
def blowUpAffineChart (U : X.affineOpens) (a : I.ideal U) :
    Spec (.of (blowUpAffineChartRing I U a)) ⟶ blowUp I :=
  letI := (reesSituation I).sectionRingGradedRing U.1
  letI := (reesSituation I).sectionRingGradingGradedRing U.1
  (affineBlowupStandardOpenIso I U a).hom ≫
    (Proj.basicOpen ((reesSituation I).sectionRingGrading U.1) (reesDegreeOne I U a).1).ι ≫
      Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U

/-- The standard affine chart `blowUpAffineChart I U a` is an open immersion into the blowup. -/
instance isOpenImmersion_blowUpAffineChart (U : X.affineOpens) (a : I.ideal U) :
    IsOpenImmersion (blowUpAffineChart I U a) := by
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  dsimp only [blowUpAffineChart]
  infer_instance

/-- The structure morphism of a standard affine chart of the blowup down to the base is `Spec`
of the canonical map of `Γ(X, U)` into the affine blowup algebra, followed by the inclusion of
the affine open `U`. -/
theorem blowUpAffineChart_comp_blowUpToBase (U : X.affineOpens) (a : I.ideal U) :
    blowUpAffineChart I U a ≫ blowUpToBase I =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (.op U.1))
        (blowUpAffineChartRing I U a))) ≫ U.2.isoSpec.inv ≫ U.1.ι := by
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  have hw := (Stacks.RelativeProj.Situation.relativeProjChart_isPullback
    (reesSituation I) U).w
  have hover := affineBlowupStandardOpenIso_over I U a
  change ((affineBlowupStandardOpenIso I U a).hom ≫
    (Proj.basicOpen ((reesSituation I).sectionRingGrading U.1) (reesDegreeOne I U a).1).ι ≫
      Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U) ≫
        blowUpToBase I = _
  rw [Category.assoc, Category.assoc, hw, ← Category.assoc, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ U.1.ι)
    (by simpa only [Category.assoc] using hover)

/-- Every point of the blowup lying over an affine open `U` of `X` lies on the standard affine
chart attached to `U` and some section `a` of `I(U)`. -/
theorem exists_mem_range_blowUpAffineChart_of_mem (U : X.affineOpens) (x : blowUp I)
    (hx : x ∈ blowUpToBase I ⁻¹ᵁ U.1) :
    ∃ a : I.ideal U, x ∈ Set.range (blowUpAffineChart I U a) := by
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  have hxchart : x ∈ ⋃ a : I.ideal U,
      Set.range ((Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U a).1).ι ≫
        Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U) := by
    rw [blownUpAffine_chart_cover I U]
    exact hx
  obtain ⟨a, z, hz⟩ := Set.mem_iUnion.mp hxchart
  refine ⟨a, (affineBlowupStandardOpenIso I U a).inv z, ?_⟩
  change Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U
    ((Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a).1).ι
      ((affineBlowupStandardOpenIso I U a).hom
        ((affineBlowupStandardOpenIso I U a).inv z))) = x
  rw [show (affineBlowupStandardOpenIso I U a).hom
    ((affineBlowupStandardOpenIso I U a).inv z) = z from
      congrArg (fun f ↦ f z) (affineBlowupStandardOpenIso I U a).inv_hom_id]
  exact hz

/-- Every point of the blowup lies on a standard affine chart. -/
theorem exists_mem_range_blowUpAffineChart (x : blowUp I) :
    ∃ (U : X.affineOpens) (a : I.ideal U), x ∈ Set.range (blowUpAffineChart I U a) := by
  obtain ⟨y, hy⟩ := X.affineCover.covers (blowUpToBase I x)
  refine ⟨⟨(X.affineCover.f (X.affineCover.idx (blowUpToBase I x))).opensRange,
    isAffineOpen_opensRange _⟩, ?_⟩
  exact exists_mem_range_blowUpAffineChart_of_mem I _ x ⟨y, hy⟩

/-- The degree-one Rees element attached to the zero section of the centre is zero.

This is the form that asks for no membership proof and concludes in the submodule `I(U)` itself;
`AlgebraicGeometry.reesDegreeOne_zero` is the form that takes a membership proof for the zero
section and concludes in the ambient graded ring. -/
theorem reesDegreeOne_zero' (U : X.affineOpens) : reesDegreeOne I U (0 : I.ideal U) = 0 := by
  refine Subtype.ext ?_
  have he : ((reesAlgebraData I).pieceEquiv 1 (by omega) U).symm
      ⟨(0 : X.presheaf.obj (.op U.1)), by simp⟩ = 0 :=
    ((reesAlgebraData I).pieceEquiv 1 (by omega) U).injective (Subtype.ext (by simp))
  change DirectSum.of ((reesSituation I).sectionPieces U.1) 1
    (((reesAlgebraData I).pieceEquiv 1 (by omega) U).symm ⟨0, by simp⟩) = 0
  rw [he]
  exact map_zero _

/-- The standard affine chart at a zero section of the centre is empty: it is the basic open
of the degree-one Rees element attached to that section, which is zero. -/
theorem isEmpty_spec_blowUpAffineChartRing_of_eq_zero (U : X.affineOpens) (a : I.ideal U)
    (ha : (a : X.presheaf.obj (.op U.1)) = 0) :
    IsEmpty (Spec (.of (blowUpAffineChartRing I U a))) := by
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  refine ⟨fun w ↦ ?_⟩
  have hz : (reesDegreeOne I U a).1 = 0 := by
    rw [show a = 0 from Subtype.ext ha, reesDegreeOne_zero']
    rfl
  have hbot : ∀ p : Proj ((reesSituation I).sectionRingGrading U.1),
      p ∉ Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U a).1 := by
    rw [hz]
    intro p
    simp
  exact hbot _ ((affineBlowupStandardOpenIso I U a).hom w).2

/-- The standard affine charts, indexed by pairs of an affine open `U` of `X` and a section of
`I(U)`, as an open cover of the blowup. -/
def blowUpAffineChartCover : (blowUp I).OpenCover :=
  Scheme.Cover.mkOfCovers (J := Σ U : X.affineOpens, I.ideal U)
    (fun j ↦ Spec (.of (blowUpAffineChartRing I j.1 j.2)))
    (fun j ↦ blowUpAffineChart I j.1 j.2)
    (fun x ↦ by
      obtain ⟨U, a, z, hz⟩ := exists_mem_range_blowUpAffineChart I x
      exact ⟨⟨U, a⟩, z, hz⟩)
    (fun _ ↦ inferInstance)

end AlgebraicGeometry

end
