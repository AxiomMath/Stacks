module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwist
public import StacksFrontier.AlgebraicGeometry.BlowUpChartCover.ChartImage
public import StacksFrontier.AlgebraicGeometry.RelativeProj.ChartStructureSections
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneChartAgreement

/-!
# The chartwise comparison of `𝒪(1)` with the exceptional ideal sheaf of a blowup

Let `X` be a scheme, `ℐ` a quasi-coherent ideal sheaf on it, `U` an affine open of `X` and
`a ∈ ℐ(U)`. On the standard affine chart of the blowup at `a`, with image
`Stacks.BlowUpChartCover.chartOpen ℐ U a`, both sheaves being compared are trivial:

* the twisting sheaf `𝒪_{X'}(1)` is trivialized by the degree-one generator `a⁽¹⁾` of the graded
  section ring of the Rees algebra on `U`, because the chart is the part of the relative-`Proj`
  chart over `U` cut out by `D₊(a⁽¹⁾)`
  (`Stacks.BlowUpChartCover.preimage_relativeProjChart_chartOpen`);
* the exceptional ideal sheaf is trivialized by the pullback of `a`
  (`Stacks.BlowUpChartCover.exceptionalChartTrivialization`).

This file composes the two trivializations into the chartwise comparison
`AlgebraicGeometry.chartEquiv`, and characterises it by the identity
`ι(chartEquiv t) = chartTwistCoeff t · chartGenerator` in the structure sheaf of the blowup.
That identity is what two charts are compared through, since it has no reference to the chart's
graded ring.

## Main definitions

* `AlgebraicGeometry.exceptionalIdealModule`: the ideal sheaf of the exceptional divisor, as a
  sheaf of modules on the blowup.
* `AlgebraicGeometry.chartTwistSections`: a section of `𝒪_{X'}(1)` over an open of the chart,
  read on the relative-`Proj` chart over `U`.
* `AlgebraicGeometry.chartTwistCoeff`: that section divided by the trivializing section of
  `a⁽¹⁾`, read back as a section of the structure sheaf of the blowup.
* `AlgebraicGeometry.chartTwistEquiv` and `AlgebraicGeometry.chartIdealEquiv`: the two
  trivializations with their scalars at one spelling, and `AlgebraicGeometry.chartEquiv` their
  composite.

## Main results

* `AlgebraicGeometry.incl_app_chartEquiv`: **the chartwise comparison is division by the
  pullback of `a`.** The image in the structure sheaf of the section of the exceptional ideal
  sheaf attached to `t` is `chartTwistCoeff t` times the restricted generator.
* `AlgebraicGeometry.chartEquiv_map`: **the chartwise comparison commutes with restriction.**
* `AlgebraicGeometry.chartGeneratorRes_eq_appLE`: the restricted generator is the pullback of
  `a` along the blowup morphism, read over the smaller open. This is what makes the generator
  side of a chart-to-chart comparison a statement about `AlgebraicGeometry.Scheme.Hom.appLE`
  alone.

## Implementation notes

The whole file exists to produce one `Γ(X', V)`-*linear* equivalence, and the obstacle is that
the trivialization of `𝒪(1)` is linear over the functions on the chart, not over the functions
on the blowup. The two rings are identified by
`Stacks.RelativeProj.Situation.chartSectionsIso`, and the module structure on the sections of
the pushed-forward chart twist is restriction of scalars along that identification
(`ModuleCat.restrictScalars.smul_def'`), so the composite is linear — but only after the scalar
is written at the spelling `(ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op W)` that the
twist sections carry. At the spelling `Γ(Proj 𝒜, W)` the two agree definitionally but not
*reducibly*, and `HSMul` synthesis fails; a type ascription on the product does not help, since
it does not change what `inferType` returns, while a `show` on the scalar itself does. That is
`chartTwistSections_smul` below.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.RelativeProj
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj (moduleSections twistGrading twistingSheaf)

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)

/-- **The ideal sheaf of the exceptional divisor of a blowup, as a sheaf of modules.** -/
abbrev exceptionalIdealModule : (blowUp I).Modules :=
  Stacks.ClosedImmersion.idealSheaf (exceptionalIdeal I).subschemeι.toLRSHom.toShHom

/-! ### The chart at `a` inside the relative-`Proj` chart over `U` -/

/-- The standard affine chart at `a` lies inside the relative-`Proj` chart over `U`. -/
theorem chartOpen_le_opensRange_relativeProjChart :
    (Stacks.BlowUpChartCover.chartOpen I U a).1 ≤
      (Situation.relativeProjChart (reesSituation I) U).opensRange := by
  rw [Stacks.BlowUpChartCover.chartOpen_eq_image]
  exact Scheme.Hom.image_le_opensRange _ _

/-- An open of the standard affine chart at `a` pulls back into `D₊(a⁽¹⁾)`. -/
theorem preimage_relativeProjChart_le_basicOpen {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) :
    Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V ≤
      ProjectiveSpectrum.basicOpen ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U a).1 :=
  (Scheme.Hom.preimage_mono _ hV).trans
    (Stacks.BlowUpChartCover.preimage_relativeProjChart_chartOpen I U a).le

/-! ### The trivializing coefficient of `𝒪(1)` on the chart -/

/-- **A section of `𝒪_{X'}(1)` over an open of the chart at `a`, read on the relative-`Proj`
chart over `U`** as a section of the absolute twisting sheaf of `Proj 𝒜(U)`. -/
def chartTwistSections {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    moduleSections ((reesSituation I).sectionRingGrading U.1)
      (twistGrading ((reesSituation I).sectionRingGrading U.1) 1)
      (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V) :=
  (Situation.twistSectionsIso ((reesSituation I).twistTransition 1) U
    (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).hom t

/-- Reading a section of `𝒪_{X'}(1)` on the chart is additive. -/
theorem chartTwistSections_add {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t t' : ToType ((blowUpTwist I 1).val.obj (op V))) :
    chartTwistSections I U a hV (t + t')
      = chartTwistSections I U a hV t + chartTwistSections I U a hV t' :=
  map_add _ t t'

/-- **Reading a section of `𝒪_{X'}(1)` on the chart turns the action of a function on the
blowup into the action of its restriction to the chart.** The module structure on the sections of
the pushed-forward chart twist is restriction of scalars along the chart's map on sections, so
this is `ModuleCat.restrictScalars.smul_def'`; the scalar has to be written at the spelling the
twist sections carry, since `HSMul` synthesis does not unfold `Γ(Proj 𝒜, W)` into it. -/
theorem chartTwistSections_smul {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (r : ToType ((blowUp I).ringCatSheaf.obj.obj (op V)))
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    chartTwistSections I U a hV (r • t)
      = (show ToType ((ProjectiveSpectrum.Proj.structureSheaf
            ((reesSituation I).sectionRingGrading U.1)).obj.obj
            (op (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V)))
          from ((Situation.relativeProjChart (reesSituation I) U).app V).hom r) •
        chartTwistSections I U a hV t :=
  (Situation.twistSectionsIso ((reesSituation I).twistTransition 1) U
    (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).hom.hom.map_smul r t

/-- **The trivializing coefficient of `𝒪_{X'}(1)` on the chart at `a`**: a section of
`𝒪_{X'}(1)` over an open of the chart, divided by the trivializing section of the degree-one
generator `a⁽¹⁾` and read back as a section of the structure sheaf of the blowup. -/
def chartTwistCoeff {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) : Γ(blowUp I, V) :=
  (Situation.chartSectionsIso (reesSituation I) U
      (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).inv.hom
    (twistOneCoeff ((reesSituation I).sectionRingGrading U.1) (reesDegreeOne I U a).2
      (preimage_relativeProjChart_le_basicOpen I U a hV) (chartTwistSections I U a hV t))

/-- **The chart reads the trivializing coefficient as the quotient of the section of `𝒪(1)` by
the trivializing section of `a⁽¹⁾`.** -/
theorem app_relativeProjChart_chartTwistCoeff {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    ((Situation.relativeProjChart (reesSituation I) U).app V).hom
        (chartTwistCoeff I U a hV t)
      = twistOneCoeff ((reesSituation I).sectionRingGrading U.1) (reesDegreeOne I U a).2
          (preimage_relativeProjChart_le_basicOpen I U a hV) (chartTwistSections I U a hV t) :=
  Situation.chartSectionsIso_hom_inv_apply (reesSituation I) U
    (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a)) _

/-- The trivializing coefficient of `t` is any section whose image on the relative-`Proj` chart is
the quotient of the section of `𝒪(1)` read there. -/
private theorem chartTwistCoeff_eq_of_app_eq {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) (z : Γ(blowUp I, V))
    (h : ((Situation.relativeProjChart (reesSituation I) U).app V).hom z
      = twistOneCoeff ((reesSituation I).sectionRingGrading U.1) (reesDegreeOne I U a).2
          (preimage_relativeProjChart_le_basicOpen I U a hV) (chartTwistSections I U a hV t)) :
    chartTwistCoeff I U a hV t = z :=
  Situation.injective_app_relativeProjChart (reesSituation I) U
    (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))
    ((app_relativeProjChart_chartTwistCoeff I U a hV t).trans h.symm)

/-- The trivializing coefficient is additive. -/
theorem chartTwistCoeff_add {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t t' : ToType ((blowUpTwist I 1).val.obj (op V))) :
    chartTwistCoeff I U a hV (t + t')
      = chartTwistCoeff I U a hV t + chartTwistCoeff I U a hV t' := by
  refine chartTwistCoeff_eq_of_app_eq I U a hV _ _ ?_
  rw [map_add, app_relativeProjChart_chartTwistCoeff, app_relativeProjChart_chartTwistCoeff,
    chartTwistSections_add]
  exact (twistOneCoeff_add _ _ _ _ _).symm

/-- **The trivializing coefficient is linear over the functions on the blowup.** -/
theorem chartTwistCoeff_smul {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (r : ToType ((blowUp I).ringCatSheaf.obj.obj (op V)))
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    chartTwistCoeff I U a hV (r • t)
      = (show Γ(blowUp I, V) from r) * chartTwistCoeff I U a hV t := by
  refine chartTwistCoeff_eq_of_app_eq I U a hV _ _ ?_
  rw [chartTwistSections_smul]
  exact ((map_mul _ _ _).trans
    (congrArg _ (app_relativeProjChart_chartTwistCoeff I U a hV t))).trans
    (twistOneCoeff_smul _ _ _ _ _).symm

/-- The trivializing coefficient is a bijection onto the sections of the structure sheaf: it is
the composite of three bijections. -/
theorem bijective_chartTwistCoeff {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) :
    Function.Bijective (chartTwistCoeff I U a hV) := by
  have h1 : Function.Bijective (chartTwistSections I U a hV) :=
    (Situation.twistSectionsIso ((reesSituation I).twistTransition 1) U
      (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).toLinearEquiv.bijective
  have h2 : Function.Bijective
      (twistOneCoeff ((reesSituation I).sectionRingGrading U.1) (reesDegreeOne I U a).2
        (preimage_relativeProjChart_le_basicOpen I U a hV)) :=
    (trivializingEquiv ((reesSituation I).sectionRingGrading U.1) (reesDegreeOne I U a).2 1
      (preimage_relativeProjChart_le_basicOpen I U a hV)).symm.bijective
  have h3 : Function.Bijective ((Situation.chartSectionsIso (reesSituation I) U
      (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).inv.hom) :=
    ConcreteCategory.bijective_of_isIso (Situation.chartSectionsIso (reesSituation I) U
      (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).inv
  exact (h3.comp h2).comp h1

/-- **Reading a section of `𝒪_{X'}(1)` on the chart commutes with restriction.** -/
theorem chartTwistSections_map {V W : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) (hWV : W ≤ V)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    chartTwistSections I U a (hWV.trans hV)
        ((blowUpTwist I 1).val.restrictₛₗ (homOfLE hWV).op t)
      = (twistingSheaf ((reesSituation I).sectionRingGrading U.1) 1).val.restrictₛₗ
          (homOfLE (Scheme.Hom.preimage_mono
            (Situation.relativeProjChart (reesSituation I) U) hWV)).op
          (chartTwistSections I U a hV t) :=
  Situation.twistSectionsIso_restrict ((reesSituation I).twistTransition 1) U
    (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a)) hWV t

/-- **The trivializing coefficient commutes with restriction.** -/
theorem chartTwistCoeff_map {V W : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) (hWV : W ≤ V)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    ((blowUp I).presheaf.map (homOfLE hWV).op).hom (chartTwistCoeff I U a hV t)
      = chartTwistCoeff I U a (hWV.trans hV)
          ((blowUpTwist I 1).val.restrictₛₗ (homOfLE hWV).op t) := by
  refine (chartTwistCoeff_eq_of_app_eq I U a (hWV.trans hV) _ _ ?_).symm
  refine Eq.trans (Situation.map_chartSectionsIso_hom (reesSituation I) U hWV _) ?_
  refine Eq.trans (congrArg (((AlgebraicGeometry.Proj
      ((reesSituation I).sectionRingGrading U.1)).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono
        (Situation.relativeProjChart (reesSituation I) U) hWV)).op).hom)
    (app_relativeProjChart_chartTwistCoeff I U a hV t)) ?_
  rw [chartTwistSections_map]
  exact (twistOneCoeff_map ((reesSituation I).sectionRingGrading U.1)
    (reesDegreeOne I U a).2 (preimage_relativeProjChart_le_basicOpen I U a hV)
    (preimage_relativeProjChart_le_basicOpen I U a (hWV.trans hV))
    (Scheme.Hom.preimage_mono (Situation.relativeProjChart (reesSituation I) U) hWV)
    (chartTwistSections I U a hV t)).symm

/-! ### The chartwise comparison -/

/-- The trivialization of `𝒪_{X'}(1)` over an open of the chart at `a`, with its scalars at the
spelling the glueing data of `Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv` uses. -/
def chartTwistEquiv {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) :
    ToType ((blowUpTwist I 1).val.obj (op V))
      ≃ₗ[ToType ((blowUp I).ringCatSheaf.obj.obj (op V))]
        ToType ((blowUp I).ringCatSheaf.obj.obj (op V)) :=
  LinearEquiv.ofBijective
    (({ toFun := chartTwistCoeff I U a hV
        map_add' := chartTwistCoeff_add I U a hV
        map_smul' := chartTwistCoeff_smul I U a hV } :
      ToType ((blowUpTwist I 1).val.obj (op V))
        →ₗ[ToType ((blowUp I).ringCatSheaf.obj.obj (op V))]
          ToType ((blowUp I).ringCatSheaf.obj.obj (op V))))
    (bijective_chartTwistCoeff I U a hV)

/-- The trivialization `chartTwistEquiv` sends a section `t` to its coefficient
`chartTwistCoeff I U a hV t`. -/
@[simp] theorem chartTwistEquiv_apply {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    chartTwistEquiv I U a hV t = chartTwistCoeff I U a hV t := rfl

/-- The trivialization of the exceptional ideal sheaf over an open of the chart at `a`, with its
scalars at the same spelling. -/
def chartIdealEquiv {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) :
    ToType ((exceptionalIdealModule I).val.obj (op V))
      ≃ₗ[ToType ((blowUp I).ringCatSheaf.obj.obj (op V))]
        ToType ((blowUp I).ringCatSheaf.obj.obj (op V)) :=
  (Stacks.BlowUpChartCover.exceptionalChartTrivialization I U a).θ V (homOfLE hV)

/-- **The chartwise comparison of `𝒪_{X'}(1)` with the exceptional ideal sheaf** over an open of
the standard affine chart at `a`: divide by the trivializing section of `a⁽¹⁾`, then multiply by
the pullback of `a`. -/
def chartEquiv {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) :
    ToType ((blowUpTwist I 1).val.obj (op V))
      ≃ₗ[ToType ((blowUp I).ringCatSheaf.obj.obj (op V))]
        ToType ((exceptionalIdealModule I).val.obj (op V)) :=
  (chartTwistEquiv I U a hV).trans (chartIdealEquiv I U a hV).symm

/-! ### The characterisation of the chartwise comparison -/

/-- The generator of the exceptional ideal on the chart at `a`, restricted to an open of the
chart. -/
def chartGeneratorRes {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) : Γ(blowUp I, V) :=
  ((blowUp I).presheaf.map (homOfLE hV).op).hom
    (Stacks.BlowUpChartCover.chartGenerator I U a)

/-- **The restricted generator is the pullback of `a` along the blowup morphism**, read over the
smaller open. -/
theorem chartGeneratorRes_eq_appLE {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) :
    chartGeneratorRes I U a hV
      = ((blowUpToBase I).appLE U.1 V
          (hV.trans (Stacks.BlowUpChartCover.chartOpen_le I U a))).hom (a : Γ(X, U.1)) := by
  have h := Scheme.Hom.appLE_map (blowUpToBase I)
    (Stacks.BlowUpChartCover.chartOpen_le I U a) (homOfLE hV).op
  have h' := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp h) (a : Γ(X, U.1))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
  refine h'.trans (congrArg (fun e => ((blowUpToBase I).appLE U.1 V e).hom (a : Γ(X, U.1)))
    (Subsingleton.elim _ _))

/-- Restricting the restricted generator gives the restricted generator. -/
theorem map_chartGeneratorRes {V W : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) (hWV : W ≤ V) :
    ((blowUp I).presheaf.map (homOfLE hWV).op).hom (chartGeneratorRes I U a hV)
      = chartGeneratorRes I U a (hWV.trans hV) := by
  rw [chartGeneratorRes, chartGeneratorRes, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **The chartwise comparison is division by the pullback of `a`.** The image in the structure
sheaf of the section of the exceptional ideal sheaf attached to `t` is the trivializing
coefficient of `t` times the restricted generator. This is the characterisation two charts are
compared through. -/
theorem incl_app_chartEquiv {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    ((Stacks.CartierAffineLocal.incl (exceptionalIdeal I)).val.app (op V)).hom
        (chartEquiv I U a hV t)
      = chartTwistCoeff I U a hV t * chartGeneratorRes I U a hV :=
  Stacks.CartierAffineLocalConverse.incl_app_eq_θ_mul (exceptionalIdeal I)
    (Stacks.BlowUpChartCover.chartOpen I U a)
    (Stacks.BlowUpChartCover.chartGenerator I U a)
    (Stacks.BlowUpChartCover.chartGenerator_mem_nonZeroDivisors I U a)
    (Stacks.BlowUpChartCover.ideal_exceptionalIdeal_eq_span_chartGenerator I U a)
    (homOfLE hV) (chartEquiv I U a hV t) _
    ((chartIdealEquiv I U a hV).apply_symm_apply _)

/-- Two sections of the exceptional ideal sheaf over the same open agree as soon as their images
in the structure sheaf do. -/
theorem injective_incl_app_exceptionalIdeal (V : (blowUp I).Opens) :
    Function.Injective
      (((Stacks.CartierAffineLocal.incl (exceptionalIdeal I)).val.app (op V)).hom) :=
  Stacks.CartierAffineLocal.injective_incl_app (exceptionalIdeal I) V

/-- **The chartwise comparison commutes with restriction.** -/
theorem chartEquiv_map {V W : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) (hWV : W ≤ V)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    chartEquiv I U a (hWV.trans hV)
        ((blowUpTwist I 1).val.restrictₛₗ (homOfLE hWV).op t)
      = (exceptionalIdealModule I).val.restrictₛₗ (homOfLE hWV).op (chartEquiv I U a hV t) := by
  refine injective_incl_app_exceptionalIdeal I W ?_
  have hL := incl_app_chartEquiv I U a (hWV.trans hV)
    ((blowUpTwist I 1).val.restrictₛₗ (homOfLE hWV).op t)
  have hnat := PresheafOfModules.naturality_apply
    (Stacks.CartierAffineLocal.incl (exceptionalIdeal I)).val (homOfLE hWV).op
    (chartEquiv I U a hV t)
  have hR := incl_app_chartEquiv I U a hV t
  have hc := chartTwistCoeff_map I U a hV hWV t
  refine hL.trans (Eq.symm (hnat.trans ?_))
  refine (congrArg ((blowUp I).presheaf.map (homOfLE hWV).op).hom hR).trans ?_
  refine (map_mul ((blowUp I).presheaf.map (homOfLE hWV).op).hom _ _).trans ?_
  refine (congrArg (fun y => y * ((blowUp I).presheaf.map (homOfLE hWV).op).hom
    (chartGeneratorRes I U a hV)) hc).trans ?_
  exact congrArg (fun z => chartTwistCoeff I U a (hWV.trans hV)
    ((blowUpTwist I 1).val.restrictₛₗ (homOfLE hWV).op t) * z)
    (map_chartGeneratorRes I U a hV hWV)

end AlgebraicGeometry

end
