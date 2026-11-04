module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesProjBridge

/-!
# The identification of the blowup with the relative Proj of the Rees algebra, on the charts

`StacksFrontier/AlgebraicGeometry/Blowup/ReesProjBridge.lean` identifies the relative `Proj` of
`Stacks.Blowup.reesSheafGradedAlgebra I` with `AlgebraicGeometry.blowUp I` over the base, as an
existential statement. That is enough to transport a *global* statement about closed subschemes
of a relative `Proj` to the blowup, but not a statement read on the standard affine charts: the
existential discards the chart data the comparison is built from.

This file names the isomorphism and records how it acts on the charts. Over an affine open `U`
of the base the chart of the relative `Proj` is `Proj` of the graded ring of sections of the
`SheafGradedAlgebra`, the chart of the blowup is `Proj` of the graded ring of sections of
`AlgebraicGeometry.reesSituation`, and the comparison of the two is `AlgebraicGeometry.Proj.map`
of the graded ring isomorphism between them.

## Main definitions

* `Stacks.Blowup.reesChartGradedHom`: the graded ring isomorphism of the two spellings of the
  Rees algebra's sections over an affine open of the base, from the `SheafGradedAlgebra` to
  `AlgebraicGeometry.reesSituation`.
* `Stacks.Blowup.reesChartGradedInv`: its inverse.
* `Stacks.Blowup.reesChartProjIso`: the induced isomorphism of charts.
* `Stacks.Blowup.reesProjBlowUpIso`: **the identification of the relative `Proj` of the Rees
  algebra with the blowup**, as a named isomorphism.

## Main results

* `Stacks.Blowup.reesProjBlowUpIso_hom_blowUpToBase`: the identification is one over the base.
* `Stacks.Blowup.chart_reesProjBlowUpIso_hom`: **the identification carries the chart of the
  relative `Proj` over an affine open to the chart of the blowup**, through the chart
  isomorphism.

## Implementation notes

`AlgebraicGeometry.blowUp I` is, by definition, the relative `Proj` of
`AlgebraicGeometry.reesSituation I` glued as a `Stacks.RelativeProj.Data`, so the comparison is
a single application of `Stacks.AlgebraicGeometry.ProjPresentation.chartFamily` — the uniqueness
half of Tag 01NQ for the colimit glueing — and its chart lemma
`…RelativeProjDescent.ChartFamily.chart_iso_hom` is the chart statement wanted here.
`Stacks.Blowup.exists_iso_relativeProj_reesSheafGradedAlgebra_blowUp` instead goes through the
relative `Proj` of `Stacks.Blowup.reesSituation`, which is an intermediate step that has to be
composed away afterwards; the graded comparison used here is the composite of the two
comparisons that step is assembled from, namely `Stacks.Blowup.reesChartHom` and
`Stacks.Blowup.ReesModel.sectionGradedHom`.

`AlgebraicGeometry.Proj.map` is contravariant, so the chart comparison in the forward direction
is `Proj.map` of the *inverse* graded homomorphism.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)

## Not done here

No Stacks tag is claimed: the existence of the relative homogeneous spectrum is Tag 01NQ and is
tagged where it is built, and a comparison of two constructions of it is not a labelled
assertion of the source.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjDescent
open Stacks.AlgebraicGeometry.ProjPresentation

universe u

namespace Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The graded comparison of the two spellings of the Rees algebra's sections -/

/-- **The graded ring comparison of the two spellings of the Rees algebra's sections** over an
affine open of the base: from the `SheafGradedAlgebra` substrate on which Tags 0801–0803 are
stated to `AlgebraicGeometry.reesSituation`, out of which the blowup is glued. -/
public def reesChartGradedHom (U : X.AffineZariskiSite) :
    ((reesSheafGradedAlgebra I).toGradedAlgebra).grading U →+*ᵍ
      (AlgebraicGeometry.reesSituation I).sectionRingGrading (siteAffineOpen U).1 :=
  ((reesSituationModel I).sectionGradedHom (siteAffineOpen U)).comp (reesChartHom I U)

/-- The inverse of `Stacks.Blowup.reesChartGradedHom`. -/
public def reesChartGradedInv (U : X.AffineZariskiSite) :
    (AlgebraicGeometry.reesSituation I).sectionRingGrading (siteAffineOpen U).1 →+*ᵍ
      ((reesSheafGradedAlgebra I).toGradedAlgebra).grading U :=
  (reesChartInv I U).comp ((reesSituationModel I).sectionGradedHomInv (siteAffineOpen U))

/-- The inverse comparison of `ReesProjBridge.lean` undoes the comparison there. -/
public theorem reesChartInv_comp_hom (U : X.AffineZariskiSite) :
    (reesChartInv I U).comp (reesChartHom I U) =
      GradedRingHom.id (((reesSheafGradedAlgebra I).toGradedAlgebra).grading U) :=
  situationSectionGradedInv_comp_hom (reesGradedAlgebra I) (reesIsCommutative I)
    (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) U.toOpens

/-- The comparison of `ReesProjBridge.lean` undoes the inverse comparison there. -/
public theorem reesChartHom_comp_inv (U : X.AffineZariskiSite) :
    (reesChartHom I U).comp (reesChartInv I U) =
      GradedRingHom.id ((reesSituation I).sectionRingGrading (siteAffineOpen U).1) :=
  situationSectionGradedHom_comp_inv (reesGradedAlgebra I) (reesIsCommutative I)
    (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) U.toOpens

/-- The inverse comparison undoes the comparison, read on an element. -/
public theorem reesChartGradedInv_hom_apply (U : X.AffineZariskiSite)
    (x : ((reesSheafGradedAlgebra I).toGradedAlgebra).ring U) :
    reesChartGradedInv I U (reesChartGradedHom I U x) = x := by
  have h := GradedRingHom.congr_fun (reesChartInv_comp_hom I U) x
  rw [GradedRingHom.comp_apply, GradedRingHom.id_apply] at h
  refine Eq.trans ?_ h
  exact congrArg (reesChartInv I U)
    ((reesSituationModel I).sectionInv_sectionHom (siteAffineOpen U) (reesChartHom I U x))

/-- The comparison undoes the inverse comparison, read on an element. -/
public theorem reesChartGradedHom_inv_apply (U : X.AffineZariskiSite)
    (y : (AlgebraicGeometry.reesSituation I).sectionRing (siteAffineOpen U).1) :
    reesChartGradedHom I U (reesChartGradedInv I U y) = y := by
  have h := GradedRingHom.congr_fun (reesChartHom_comp_inv I U)
    ((reesSituationModel I).sectionGradedHomInv (siteAffineOpen U) y)
  rw [GradedRingHom.comp_apply, GradedRingHom.id_apply] at h
  show (reesSituationModel I).sectionGradedHom (siteAffineOpen U)
    (reesChartHom I U (reesChartInv I U
      ((reesSituationModel I).sectionGradedHomInv (siteAffineOpen U) y))) = y
  rw [h]
  exact (reesSituationModel I).sectionHom_sectionInv (siteAffineOpen U) y

/-- The inverse comparison undoes the comparison. -/
public theorem reesChartGradedInv_comp_hom (U : X.AffineZariskiSite) :
    (reesChartGradedInv I U).comp (reesChartGradedHom I U) =
      GradedRingHom.id (((reesSheafGradedAlgebra I).toGradedAlgebra).grading U) :=
  GradedRingHom.ext (reesChartGradedInv_hom_apply I U)

/-- The comparison undoes the inverse comparison. -/
public theorem reesChartGradedHom_comp_inv (U : X.AffineZariskiSite) :
    (reesChartGradedHom I U).comp (reesChartGradedInv I U) =
      GradedRingHom.id ((AlgebraicGeometry.reesSituation I).sectionRingGrading
        (siteAffineOpen U).1) :=
  GradedRingHom.ext (reesChartGradedHom_inv_apply I U)

/-- The comparison commutes with the restriction maps of the two spellings. -/
public theorem reesChartGradedHom_comp_res (U V : X.AffineZariskiSite)
    (h : U.toOpens ≤ V.toOpens) :
    (reesChartGradedHom I U).comp (((reesSheafGradedAlgebra I).toGradedAlgebra).res h) =
      ((Stacks.RelativeProj.Situation.chartData (AlgebraicGeometry.reesSituation I)).restrict
        (siteAffineOpen_le h)).comp (reesChartGradedHom I V) := by
  refine GradedRingHom.ext fun x => ?_
  have h1 : reesChartHom I U (((reesSheafGradedAlgebra I).toGradedAlgebra).res h x) =
      Stacks.RelativeProj.Situation.gradedSectionRestriction (reesSituation I)
        (siteAffineOpen U).1 (siteAffineOpen V).1 (siteAffineOpen_le h)
        (reesChartHom I V x) :=
    situationSectionRingEquiv_resRingHom (reesGradedAlgebra I) (reesIsCommutative I)
      (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) h x
  have h2 := GradedRingHom.congr_fun
    ((reesSituationModel I).sectionGradedHom_comp_restrict
      (U := siteAffineOpen U) (V := siteAffineOpen V) (siteAffineOpen_le h))
    (reesChartHom I V x)
  rw [GradedRingHom.comp_apply, GradedRingHom.comp_apply] at h2
  refine Eq.trans ?_ h2
  exact congrArg ((reesSituationModel I).sectionGradedHom (siteAffineOpen U)) h1

/-- **The comparison carries the degree-zero identification of the `SheafGradedAlgebra` to that
of `AlgebraicGeometry.reesSituation`.** -/
public theorem strZero_comp_reesChartGradedHom (U : X.AffineZariskiSite) :
    ((reesSheafGradedAlgebra I).toGradedAlgebra).strZero U ≫
        CommRingCat.ofHom (reesChartGradedHom I U).gradedZeroRingHom =
      (Stacks.RelativeProj.Situation.chartData
        (AlgebraicGeometry.reesSituation I)).base (siteAffineOpen U) := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  have e1 := ConcreteCategory.congr_hom (strZero_comp_reesChartHom I U) r
  have e2 := ConcreteCategory.congr_hom
    ((reesSituationModel I).sectionRingZeroMap_comp_sectionGradedHom (siteAffineOpen U)) r
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at e1 e2 ⊢
  show ((reesSituationModel I).sectionGradedHom (siteAffineOpen U)).gradedZeroRingHom
    ((reesChartHom I U).gradedZeroRingHom
      ((((reesSheafGradedAlgebra I).toGradedAlgebra).strZero U).hom r)) = _
  rw [e1]
  exact e2

/-! ### The identification with the blowup -/

/-- The chart family that reads the charts of the blowup as a chart family for the Rees algebra
on the `SheafGradedAlgebra` substrate. This is the datum
`Stacks.Blowup.exists_iso_relativeProj_reesSheafGradedAlgebra_blowUp` discards. -/
public def reesBlowUpChartFamily :
    ChartFamily ((reesSheafGradedAlgebra I).toGradedAlgebra) (AlgebraicGeometry.blowUp I)
      (AlgebraicGeometry.blowUpToBase I) :=
  chartFamily (Stacks.RelativeProj.Situation.chartData (AlgebraicGeometry.reesSituation I))
    ((reesSheafGradedAlgebra I).toGradedAlgebra)
    (reesChartGradedHom I) (reesChartGradedInv I)
    (reesChartGradedInv_comp_hom I) (reesChartGradedHom_comp_inv I)
    (reesChartGradedHom_comp_res I) (strZero_comp_reesChartGradedHom I)

/-- **The chart comparison over an affine open of the base**: `AlgebraicGeometry.Proj` of the
graded ring of sections of the Rees algebra on the `SheafGradedAlgebra` substrate is `Proj` of
the graded ring of sections of `AlgebraicGeometry.reesSituation`. -/
public def reesChartProjIso (U : X.AffineZariskiSite) :
    ((reesSheafGradedAlgebra I).toGradedAlgebra).projOver U ≅
      AlgebraicGeometry.Proj
        ((AlgebraicGeometry.reesSituation I).sectionRingGrading (siteAffineOpen U).1) :=
  projIso (ℬ := fun W : X.affineOpens =>
      (AlgebraicGeometry.reesSituation I).sectionRingGrading W.1)
    ((reesSheafGradedAlgebra I).toGradedAlgebra) (reesChartGradedHom I) (reesChartGradedInv I)
    (reesChartGradedInv_comp_hom I) (reesChartGradedHom_comp_inv I) U

/-- The comparison of the irrelevant ideals that `AlgebraicGeometry.Proj.map` of the inverse
graded comparison asks for; it is automatic for an isomorphism. Proved here rather than taken
from `Stacks.AlgebraicGeometry.ProjPresentation.irrelevant_le_hn`, whose implicit arguments are
too expensive to solve at these gradings. -/
public theorem irrelevant_le_map_reesChartGradedInv (U : X.AffineZariskiSite) :
    HomogeneousIdeal.irrelevant (((reesSheafGradedAlgebra I).toGradedAlgebra).grading U) ≤
      (HomogeneousIdeal.irrelevant
        ((AlgebraicGeometry.reesSituation I).sectionRingGrading
          (siteAffineOpen U).1)).map (reesChartGradedInv I U) := by
  refine (HomogeneousIdeal.irrelevant_le _).2 fun n hn x hx => ?_
  rw [← reesChartGradedInv_hom_apply I U x]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hn
    ((reesChartGradedHom I U).map_mem hx))

/-- The chart comparison is `AlgebraicGeometry.Proj.map` of the inverse graded comparison. -/
public theorem reesChartProjIso_hom (U : X.AffineZariskiSite) :
    (reesChartProjIso I U).hom =
      AlgebraicGeometry.Proj.map (reesChartGradedInv I U)
        (irrelevant_le_map_reesChartGradedInv I U) := rfl

/-- **The relative `Proj` of the Rees algebra of `I` on the `SheafGradedAlgebra` substrate is
the blowup of `X` in `I`**, as a named isomorphism. This is
`Stacks.Blowup.exists_iso_relativeProj_reesSheafGradedAlgebra_blowUp` with the witness named, so
that its action on the charts can be recorded. -/
public def reesProjBlowUpIso :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (reesSheafGradedAlgebra I)).scheme ≅
      AlgebraicGeometry.blowUp I :=
  (reesBlowUpChartFamily I).iso

/-- The identification of the relative `Proj` of the Rees algebra with the blowup is one over
the base. -/
public theorem reesProjBlowUpIso_hom_blowUpToBase :
    (reesProjBlowUpIso I).hom ≫ AlgebraicGeometry.blowUpToBase I =
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (reesSheafGradedAlgebra I)).toBase :=
  (reesBlowUpChartFamily I).iso_hom_comp

/-- **The identification with the blowup, read on the charts.** Over an affine open `U` of the
base the chart of the relative `Proj` of the Rees algebra is carried to the chart of the blowup,
through the chart comparison. -/
public theorem chart_reesProjBlowUpIso_hom (U : X.AffineZariskiSite) :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
          (reesSheafGradedAlgebra I)).chart U.toOpens (isAffineOpen_toOpens U) ≫
        (reesProjBlowUpIso I).hom =
      AlgebraicGeometry.Proj.map (reesChartGradedInv I U)
          (irrelevant_le_map_reesChartGradedInv I U) ≫
        Stacks.RelativeProj.Situation.relativeProjChart (AlgebraicGeometry.reesSituation I)
          (siteAffineOpen U) :=
  (reesBlowUpChartFamily I).chart_iso_hom U

end Stacks.Blowup

end
