module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneBaseTransport
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneChartEquiv

/-!
# Two charts of a blowup give the same comparison of `𝒪(1)` with the exceptional ideal sheaf

`StacksFrontier/AlgebraicGeometry/Blowup/TwistOneChartEquiv.lean` builds the comparison
`AlgebraicGeometry.chartEquiv` of `𝒪_{X'}(1)` with the exceptional ideal sheaf over an open of
the standard affine chart of the blowup at a section `a ∈ ℐ(U)`. This file compares two such
charts. There are two cases, and they are genuinely different:

* **the same affine open `U` of the base, two sections `a, a'`.** Both charts lie in the single
  relative-`Proj` chart over `U`, so the comparison is an identity inside one `Proj` and it is
  `AlgebraicGeometry.twistOneCoeff_mul_chartBaseSectionRes_comm`.
* **an inclusion `U' ≤ U` of affine opens, with `a' = a|_{U'}`.** Here the two charts live over
  two different `Proj`s, compared by the Tag 01NO chart transition, and all four pieces of the
  comparison have to be transported along it.

## Main results

* `Stacks.RelativeProj.Situation.app_relativeProjChart_of_le`: **the chart over `U'` reads a
  section of the relative `Proj` as the chart over `U` does, followed by the chart transition.**
* `AlgebraicGeometry.app_relativeProjChart_chartGeneratorRes`: the chart over `U` reads the
  generator of the exceptional ideal as the pullback of `a` to the chart.
* `AlgebraicGeometry.chartEquiv_agree_of_eq_base`: **two charts over the same affine open of the
  base give the same comparison.**

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.RelativeProj
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj (moduleSections twistGrading twistingSheaf)

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-- **The chart over `W` reads a section of the relative `Proj` as the chart over a larger affine
open `W'` does, followed by the chart transition.** The charts are compatible with the transition
(`relativeProjChart_transition`), and that equation of morphisms is turned into an equation of
maps on sections by `appLE_congr`, whose inequality arguments are then identified by proof
irrelevance. -/
theorem app_relativeProjChart_of_le {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : s.relativeProj.Opens} (x : Γ(relativeProj s, V)) :
    ((relativeProjChart s W).app V).hom x
      = ((projInclusionMap s W.1 W'.1 h W.2 W'.2).appLE
            (relativeProjChart s W' ⁻¹ᵁ V) (relativeProjChart s W ⁻¹ᵁ V)
            (preimage_relativeProjChart_eq s h V).le).hom
          (((relativeProjChart s W').app V).hom x) := by
  have h1 := Scheme.Hom.appLE_comp_appLE (projInclusionMap s W.1 W'.1 h W.2 W'.2)
    (relativeProjChart s W') V (relativeProjChart s W' ⁻¹ᵁ V) (relativeProjChart s W ⁻¹ᵁ V)
    le_rfl (preimage_relativeProjChart_eq s h V).le
  have h2 := appLE_congr (relativeProjChart_transition s h) V (relativeProjChart s W ⁻¹ᵁ V)
    ((preimage_relativeProjChart_eq s h V).le) le_rfl
  have e1 := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (h1.trans h2)) x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appLE_eq_app] at e1
  exact e1.symm

end Stacks.RelativeProj.Situation

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Sections pull back along `appLE` by the restriction map of the morphism followed by the
restriction map of the source. -/
private theorem appLE_apply {Y Z : Scheme.{u}} (f : Y ⟶ Z) (P : Z.Opens) (Q : Y.Opens)
    (e : Q ≤ f ⁻¹ᵁ P) (z : Γ(Z, P)) :
    (f.appLE P Q e).hom z = ((Y.presheaf.map (homOfLE e).op)).hom ((f.app P).hom z) := rfl

/-- Two chartwise comparisons agree as soon as the coefficient-times-generator expressions they
are sent to in the structure sheaf do. -/
private theorem chartEquiv_eq_of_mul_eq {U U' : X.affineOpens} {a : I.ideal U} {a' : I.ideal U'}
    {V : (blowUp I).Opens} (hVa : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (hVa' : V ≤ (Stacks.BlowUpChartCover.chartOpen I U' a').1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V)))
    (h : chartTwistCoeff I U a hVa t * chartGeneratorRes I U a hVa
      = chartTwistCoeff I U' a' hVa' t * chartGeneratorRes I U' a' hVa') :
    chartEquiv I U a hVa t = chartEquiv I U' a' hVa' t :=
  injective_incl_app_exceptionalIdeal I V
    ((incl_app_chartEquiv I U a hVa t).trans (h.trans (incl_app_chartEquiv I U' a' hVa' t).symm))

section OneBase

variable (U : X.affineOpens) (a : I.ideal U)

/-- **The chart over `U` reads the generator of the exceptional ideal as the pullback of `a` to
the chart.** -/
theorem app_relativeProjChart_chartGeneratorRes {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) :
    ((Situation.relativeProjChart (reesSituation I) U).app V).hom (chartGeneratorRes I U a hV)
      = (reesSituation I).chartBaseSectionRes U.1 U.2 (a : Γ(X, U.1))
          (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V) := by
  refine Eq.trans (congrArg ((Situation.relativeProjChart (reesSituation I) U).app V).hom
    (chartGeneratorRes_eq_appLE I U a hV)) ?_
  exact (reesSituation I).app_relativeProjChart_appLE U (a : Γ(X, U.1))
    (hV.trans (Stacks.BlowUpChartCover.chartOpen_le I U a))

/-- **Two charts over the same affine open of the base give the same comparison of `𝒪_{X'}(1)`
with the exceptional ideal sheaf.** Both charts lie in the relative-`Proj` chart over `U`, so the
identity is checked inside the single `Proj 𝒜(U)`: it is
`AlgebraicGeometry.twistOneCoeff_mul_chartBaseSectionRes_comm`. -/
theorem chartEquiv_agree_of_eq_base (a' : I.ideal U) {V : (blowUp I).Opens}
    (hVa : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (hVa' : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a').1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    chartEquiv I U a hVa t = chartEquiv I U a' hVa' t := by
  refine chartEquiv_eq_of_mul_eq I hVa hVa' t ?_
  refine Situation.injective_app_relativeProjChart (reesSituation I) U
    (hVa.trans (chartOpen_le_opensRange_relativeProjChart I U a)) ?_
  refine Eq.trans (map_mul
    ((Situation.relativeProjChart (reesSituation I) U).app V).hom _ _) ?_
  refine Eq.symm (Eq.trans (map_mul
    ((Situation.relativeProjChart (reesSituation I) U).app V).hom _ _) ?_)
  refine Eq.symm (Eq.trans (congrArg₂ (· * ·)
    (app_relativeProjChart_chartTwistCoeff I U a hVa t)
    (app_relativeProjChart_chartGeneratorRes I U a hVa)) ?_)
  refine Eq.trans ?_ (congrArg₂ (· * ·)
    (app_relativeProjChart_chartTwistCoeff I U a' hVa' t)
    (app_relativeProjChart_chartGeneratorRes I U a' hVa')).symm
  exact twistOneCoeff_mul_chartBaseSectionRes_comm I U a a'
    (preimage_relativeProjChart_le_basicOpen I U a hVa)
    (preimage_relativeProjChart_le_basicOpen I U a' hVa')
    (chartTwistSections I U a hVa t)

end OneBase

/-! ### An inclusion of affine opens of the base -/

section TwoBases

variable {U U' : X.affineOpens} (h : U' ≤ U) (a : I.ideal U)

/-- The restriction of a section of the centre to a smaller affine open. -/
abbrev restrictIdeal : I.ideal U' :=
  ⟨(Stacks.Blowup.sheafRestrict h).hom (a : Γ(X, U.1)),
    Stacks.Blowup.sheafRestrict_mem_ideal I h a⟩

/-- **The chart at the restricted section is the part of the chart at `a` lying over `U'`.**
This is the standard open `D₊(a⁽¹⁾)` pulled back along the Tag 01NO chart transition
(`AlgebraicGeometry.projInclusionMap_preimage_basicOpen_reesDegreeOne`), pushed forward again
along the chart over `U'`. -/
theorem chartOpen_restrictIdeal_eq :
    (Stacks.BlowUpChartCover.chartOpen I U' (restrictIdeal I h a)).1
      = (Situation.relativeProjChart (reesSituation I) U').opensRange ⊓
          (Stacks.BlowUpChartCover.chartOpen I U a).1 := by
  have h1 : Situation.relativeProjChart (reesSituation I) U' ⁻¹ᵁ
        (Stacks.BlowUpChartCover.chartOpen I U a).1
      = Proj.basicOpen ((reesSituation I).sectionRingGrading U'.1)
          (reesDegreeOne I U' (restrictIdeal I h a)).1 := by
    rw [Situation.preimage_relativeProjChart_eq (reesSituation I) h,
      Stacks.BlowUpChartCover.preimage_relativeProjChart_chartOpen,
      projInclusionMap_preimage_basicOpen_reesDegreeOne]
  rw [Stacks.BlowUpChartCover.chartOpen_eq_image, ← h1,
    Scheme.Hom.image_preimage_eq_opensRange_inf]

/-- The chart at the restricted section lies inside the chart at `a`. -/
theorem chartOpen_restrictIdeal_le :
    (Stacks.BlowUpChartCover.chartOpen I U' (restrictIdeal I h a)).1
      ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1 :=
  (chartOpen_restrictIdeal_eq I h a).trans_le inf_le_right

/-- **A point of the chart at `a` lying over `U'` lies in the chart at the restricted
section.** -/
theorem mem_chartOpen_restrictIdeal {x : blowUp I}
    (hx : x ∈ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (hx' : x ∈ (Situation.relativeProjChart (reesSituation I) U').opensRange) :
    x ∈ (Stacks.BlowUpChartCover.chartOpen I U' (restrictIdeal I h a)).1 := by
  rw [chartOpen_restrictIdeal_eq I h a]
  exact ⟨hx', hx⟩

/-- **The generator of the exceptional ideal does not change under passing to a smaller chart.**
Both restricted generators are the pullback of `a` along the blowup morphism, read over the
smaller open: on the smaller chart the generator is the pullback of the *restriction* of `a`, and
restricting a section of the base before pulling it back is the same as pulling it back and
restricting (`AlgebraicGeometry.Scheme.Hom.map_appLE`). -/
theorem chartGeneratorRes_eq_of_le {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (hV' : V ≤ (Stacks.BlowUpChartCover.chartOpen I U' (restrictIdeal I h a)).1) :
    chartGeneratorRes I U a hV = chartGeneratorRes I U' (restrictIdeal I h a) hV' := by
  refine (chartGeneratorRes_eq_appLE I U a hV).trans ?_
  refine Eq.trans ?_ (chartGeneratorRes_eq_appLE I U' (restrictIdeal I h a) hV').symm
  have hm := Scheme.Hom.map_appLE (blowUpToBase I)
    (hV'.trans (Stacks.BlowUpChartCover.chartOpen_le I U' (restrictIdeal I h a)))
    (homOfLE h).op
  have e1 := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hm) (a : Γ(X, U.1))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
  exact e1.symm

/-- **The trivializing coefficient of `𝒪_{X'}(1)` does not change under passing to a smaller
chart.** Read on the chart over `U'`, the coefficient computed on the chart over `U` is
transported by the Tag 01NO chart transition: on the trivializing side by
`Stacks.ProjTwistComparison.app_trivializingEquiv_symm` at the degree-one generators, which
`AlgebraicGeometry.gradedSectionRestriction_reesDegreeOne` identifies, and on the sections side by
`Stacks.RelativeProj.Situation.twistPushforwardMap`, which
`Stacks.RelativeProj.Situation.twistPushforwardMap_twistSectionsIso` identifies with reading the
section on the smaller chart. -/
theorem chartTwistCoeff_eq_of_le {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (hV' : V ≤ (Stacks.BlowUpChartCover.chartOpen I U' (restrictIdeal I h a)).1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    chartTwistCoeff I U a hV t = chartTwistCoeff I U' (restrictIdeal I h a) hV' t := by
  have hWW : Situation.projInclusionMap (reesSituation I) U'.1 U.1 h U'.2 U.2 ⁻¹ᵁ
        (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V)
      ≤ ProjectiveSpectrum.basicOpen ((reesSituation I).sectionRingGrading U'.1)
          (reesDegreeOne I U' (restrictIdeal I h a)).1 :=
    (Scheme.Hom.preimage_mono _ (preimage_relativeProjChart_le_basicOpen I U a hV)).trans
      (projInclusionMap_preimage_basicOpen_reesDegreeOne I h a).le
  have hstep : (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
        ((reesSituation I).sectionRingGrading U'.1) 1).val.restrictₛₗ
        (homOfLE (Situation.preimage_relativeProjChart_eq (reesSituation I) h V).le).op
        (Stacks.ProjTwistComparison.sectionsMap
          (Situation.gradedSectionRestriction (reesSituation I) U'.1 U.1 h)
          (Situation.irrelevant_le_map_gradedSectionRestriction (reesSituation I) U'.1 U.1 h
            U'.2 U.2) 1 (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V)
          (chartTwistSections I U a hV t))
      = chartTwistSections I U' (restrictIdeal I h a) hV' t := by
    refine Eq.trans ?_ (Situation.twistPushforwardMap_twistSectionsIso (reesSituation I) 1 h
      (hV'.trans (chartOpen_le_opensRange_relativeProjChart I U' (restrictIdeal I h a))) t)
    refine Eq.trans ?_ (Situation.twistPushforwardMap_apply (reesSituation I) 1 h
      (chartTwistSections I U a hV t)).symm
    exact congrArg (fun i => ((Situation.twistChart (reesSituation I) 1 U').presheaf.map i).hom
      (Stacks.ProjTwistComparison.sectionsMap
        (Situation.gradedSectionRestriction (reesSituation I) U'.1 U.1 h)
        (Situation.irrelevant_le_map_gradedSectionRestriction (reesSituation I) U'.1 U.1 h
          U'.2 U.2) 1 (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V)
        (chartTwistSections I U a hV t))) (Subsingleton.elim _ _)
  refine Situation.injective_app_relativeProjChart (reesSituation I) U'
    (hV'.trans (chartOpen_le_opensRange_relativeProjChart I U' (restrictIdeal I h a))) ?_
  refine Eq.trans (Situation.app_relativeProjChart_of_le (reesSituation I) h _) ?_
  refine Eq.trans (congrArg
    (((Situation.projInclusionMap (reesSituation I) U'.1 U.1 h U'.2 U.2).appLE
        (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V)
        (Situation.relativeProjChart (reesSituation I) U' ⁻¹ᵁ V)
        (Situation.preimage_relativeProjChart_eq (reesSituation I) h V).le).hom)
    (app_relativeProjChart_chartTwistCoeff I U a hV t)) ?_
  refine Eq.trans (appLE_apply (Situation.projInclusionMap (reesSituation I) U'.1 U.1 h U'.2 U.2)
    _ _ (Situation.preimage_relativeProjChart_eq (reesSituation I) h V).le _) ?_
  refine Eq.trans (congrArg
    (((AlgebraicGeometry.Proj ((reesSituation I).sectionRingGrading U'.1)).presheaf.map
      (homOfLE (Situation.preimage_relativeProjChart_eq (reesSituation I) h V).le).op).hom)
    (Stacks.ProjTwistComparison.app_trivializingEquiv_symm
      (Situation.gradedSectionRestriction (reesSituation I) U'.1 U.1 h)
      (Situation.irrelevant_le_map_gradedSectionRestriction (reesSituation I) U'.1 U.1 h
        U'.2 U.2)
      (reesDegreeOne I U a).2 (reesDegreeOne I U' (restrictIdeal I h a)).2
      (gradedSectionRestriction_reesDegreeOne I h a)
      (preimage_relativeProjChart_le_basicOpen I U a hV) hWW
      (chartTwistSections I U a hV t))) ?_
  refine Eq.trans (twistOneCoeff_map ((reesSituation I).sectionRingGrading U'.1)
    (reesDegreeOne I U' (restrictIdeal I h a)).2 hWW
    (preimage_relativeProjChart_le_basicOpen I U' (restrictIdeal I h a) hV')
    (Situation.preimage_relativeProjChart_eq (reesSituation I) h V).le _).symm ?_
  refine Eq.trans (congrArg (twistOneCoeff ((reesSituation I).sectionRingGrading U'.1)
    (reesDegreeOne I U' (restrictIdeal I h a)).2
    (preimage_relativeProjChart_le_basicOpen I U' (restrictIdeal I h a) hV')) hstep) ?_
  exact (app_relativeProjChart_chartTwistCoeff I U' (restrictIdeal I h a) hV' t).symm

/-- **The chartwise comparison does not change under passing to the chart over a smaller affine
open of the base.** -/
theorem chartEquiv_agree_of_le {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (hV' : V ≤ (Stacks.BlowUpChartCover.chartOpen I U' (restrictIdeal I h a)).1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    chartEquiv I U a hV t = chartEquiv I U' (restrictIdeal I h a) hV' t := by
  refine chartEquiv_eq_of_mul_eq I hV hV' t ?_
  exact congrArg₂ (· * ·) (chartTwistCoeff_eq_of_le I h a hV hV' t)
    (chartGeneratorRes_eq_of_le I h a hV hV')

end TwoBases

end AlgebraicGeometry

end
